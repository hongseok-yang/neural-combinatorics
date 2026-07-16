"""hfin_pipeline.py -- autonomous end-to-end pipeline for closing Hfin.

Steps (all logged to stdout; run detached with output to pipeline.log):
  0. wait for the running 4-pair validation (flint_repair_test.log), max 2.6 h
  1. mass-generate all 196 pair certificates (parallel), retry stragglers
  2. emit per-m dispatchers + Aggregate (only when all 196 exist)
  3. clean scratch files
  4. lake build OddCycleBound (root: Hfin tree + capstone + widened Main)
  5. axiom-check odd_cycle_bound (expect propext/Classical.choice/Quot.sound)
  6. git commit the results
  7. write PIPELINE_STATUS.md
"""
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
OUTDIR = "OddCycleBound/HighDensity/Hfin"
STATUS = {"validation": "?", "generation": "?", "build": "?", "axioms": "?",
          "commit": "?"}


def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] PIPELINE: {msg}", flush=True)


def write_status(final=False):
    with open("PIPELINE_STATUS.md", "w", encoding="utf-8") as f:
        f.write("# Hfin pipeline status\n\n")
        f.write(f"Updated: {time.strftime('%Y-%m-%d %H:%M:%S')}"
                f"{' (FINAL)' if final else ' (running)'}\n\n")
        for k, v in STATUS.items():
            f.write(f"- **{k}**: {v}\n")


def run(cmd, timeout=None, logfile=None):
    log(f"run: {' '.join(cmd)}")
    with open(logfile, "w", encoding="utf-8") if logfile else open(os.devnull, "w") as lf:
        p = subprocess.run(cmd, stdout=lf if logfile else None,
                           stderr=subprocess.STDOUT if logfile else None,
                           timeout=timeout)
    return p.returncode


def step0_wait_validation():
    t0 = time.time()
    while time.time() - t0 < 2.6 * 3600:
        try:
            with open("flint_repair_test.log", encoding="utf-8") as f:
                txt = f.read()
            verdicts = re.findall(r"^\((\d+), (\d+)\) (ok|FAIL)", txt, re.M)
            if len(verdicts) >= 4:
                STATUS["validation"] = ", ".join(f"({a},{b}) {v}" for a, b, v in verdicts)
                log(f"validation: {STATUS['validation']}")
                return
        except OSError:
            pass
        time.sleep(60)
        write_status()
    STATUS["validation"] = "timed out waiting; proceeding anyway"
    log(STATUS["validation"])


def step1_generate():
    import hfin_certs as H
    jobs = min(12, os.cpu_count() or 4)
    for attempt, j in ((1, jobs), (2, max(4, jobs // 2))):
        pairs = H.all_pairs()
        missing = [(m, r) for (m, r) in pairs
                   if not os.path.exists(f"{OUTDIR}/P{m:03d}R{r:02d}.lean")]
        if not missing:
            break
        log(f"generation attempt {attempt}: {len(missing)} pairs to go, jobs={j}")
        try:
            H.gen_all(OUTDIR, jobs=j)
        except Exception as e:
            log(f"gen_all raised: {e!r}")
        write_status()
    pairs = H.all_pairs()
    missing = [(m, r) for (m, r) in pairs
               if not os.path.exists(f"{OUTDIR}/P{m:03d}R{r:02d}.lean")]
    if missing:
        STATUS["generation"] = f"INCOMPLETE: {len(missing)} missing: {missing[:12]}"
        log(STATUS["generation"])
        return False
    STATUS["generation"] = "all 196 pair files + dispatchers + Aggregate"
    log(STATUS["generation"])
    return True


def step3_cleanup():
    import glob
    junk = []
    for pat in ("OddCycleBound/HighDensity/HfinProto*.lean",
                "OddCycleBound/HighDensity/HfinProbe*.lean",
                "OddCycleBound/HighDensity/HfinBisect*.lean",
                "OddCycleBound/HighDensity/HfinNoLint*.lean",
                "OddCycleBound/HighDensity/HfinProf*.lean",
                "OddCycleBound/HighDensity/HfinListProto*.lean",
                "check_ax2.lean", "check_axioms_proto.lean",
                "_repro.py", "_dllrepro.py"):
        junk += glob.glob(pat)
    for f in junk:
        try:
            os.unlink(f)
        except OSError:
            pass
    log(f"cleaned {len(junk)} scratch files")


def step4_build():
    rc = run(["lake", "build", "OddCycleBound"], timeout=12 * 3600,
             logfile="pipeline_build.log")
    tail = ""
    try:
        with open("pipeline_build.log", encoding="utf-8", errors="replace") as f:
            tail = "".join(f.readlines()[-30:])
    except OSError:
        pass
    ok = rc == 0 and "error" not in tail.lower()
    STATUS["build"] = "OK" if ok else f"FAILED (rc {rc}); see pipeline_build.log"
    log(STATUS["build"])
    return ok


def step5_axioms():
    src = ("import OddCycleBound.Main\n"
           "open OddCycleBound.HighDensity\n"
           "#print axioms odd_cycle_bound\n")
    with open("check_final_axioms.lean", "w", encoding="utf-8") as f:
        f.write(src)
    rc = run(["lake", "env", "lean", "check_final_axioms.lean"],
             timeout=1800, logfile="pipeline_axioms.log")
    txt = ""
    try:
        with open("pipeline_axioms.log", encoding="utf-8", errors="replace") as f:
            txt = f.read()
    except OSError:
        pass
    ok = (rc == 0 and "odd_cycle_bound" in txt
          and "propext" in txt and "Classical.choice" in txt
          and "Quot.sound" in txt
          and "ofReduceBool" not in txt and "sorry" not in txt.lower())
    STATUS["axioms"] = txt.strip().splitlines()[-1] if txt.strip() else f"rc {rc}"
    if not ok:
        STATUS["axioms"] = "CHECK FAILED: " + STATUS["axioms"]
    log(STATUS["axioms"])
    return ok


def step6_commit(build_ok, ax_ok):
    if not (build_ok and ax_ok):
        STATUS["commit"] = "skipped (build/axioms not green)"
        log(STATUS["commit"])
        return
    add = ["OddCycleBound/HighDensity/Hfin",
           "OddCycleBound/HighDensity/HfinCertSum.lean",
           "OddCycleBound/HighDensity/HighDensityLE61.lean",
           "OddCycleBound/HighDensity/AtomicMomentRepresentation.lean",
           "OddCycleBound/HighDensity/AtomicSpectral.lean",
           "OddCycleBound/HighDensity/DefectIdentity.lean",
           "OddCycleBound/HighDensity/DefectPowerSeries.lean",
           "OddCycleBound/HighDensity/Expansion.lean",
           "OddCycleBound/HighDensity/ExpansionAssembly.lean",
           "OddCycleBound/HighDensity/FinalAssembly.lean",
           "OddCycleBound/HighDensity/GraphonKrylovBridge.lean",
           "OddCycleBound/HighDensity/KrylovCompression.lean",
           "OddCycleBound/Main.lean", "OddCycleBound.lean",
           "hfin_certs.py", "hfin_pipeline.py"]
    subprocess.run(["git", "add", "--"] + add, cwd=HERE)
    # do not commit the per-pair logs
    subprocess.run(["git", "reset", "-q", "--", f"{OUTDIR}/logs"], cwd=HERE)
    msg = ("goodman-high-density-m0: close Hfin (odd 9<=m<=61) -- exact Handelman "
           "certificates for all 196 residual-strip pairs; odd_cycle_bound now "
           "unconditional for every odd m >= 3 (axiom-clean)\n\n"
           "Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>")
    rc = subprocess.run(["git", "commit", "-m", msg], cwd=HERE).returncode
    STATUS["commit"] = "committed" if rc == 0 else f"git commit rc {rc}"
    log(STATUS["commit"])


def main():
    write_status()
    step0_wait_validation()
    write_status()
    gen_ok = step1_generate()
    write_status()
    step3_cleanup()
    build_ok = ax_ok = False
    if gen_ok:
        build_ok = step4_build()
        write_status()
        if build_ok:
            ax_ok = step5_axioms()
            write_status()
    else:
        STATUS["build"] = "skipped (generation incomplete)"
    step6_commit(build_ok, ax_ok)
    write_status(final=True)
    log("pipeline finished")


if __name__ == "__main__":
    main()
