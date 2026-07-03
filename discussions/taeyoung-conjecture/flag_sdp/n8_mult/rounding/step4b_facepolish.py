"""
Step 4b: Dykstra polish FROM the face-SDP iterate (kernels already ~1e-9,
so no projection shock).  Sets: kernel-affine, {slack[E22]=0 and slack[h]=0
for currently-negative h}, PSD cones (with Dykstra corrections).
"""
import os, pickle, argparse, time
import numpy as np

import common
import step4_polish as sp

DATA = common.DATA


def run(src, maxit=400, tag="facepolished"):
    with open(src, "rb") as f:
        pt = pickle.load(f)
    Qs = [np.array(M) for M in (pt["Qproj"] if "Qproj" in pt else pt["Q"])]
    Rs = [np.array(M) for M in (pt["Rproj"] if "Rproj" in pt else pt["R"])]
    with open(os.path.join(DATA, "multipartite22.pkl"), "rb") as f:
        multi_idx = pickle.load(f)
    E22 = sorted(multi_idx.values())

    corrQ = [np.zeros_like(Q) for Q in Qs]
    corrR = [np.zeros_like(R) for R in Rs]
    ep = sp.EqProjector(E22)
    epW = E22
    t0 = time.time()
    for it in range(maxit):
        Qs, Rs = sp.kernel_project(Qs, Rs)
        sl = sp.slacks(Qs, Rs)
        bad = [h for h in np.where(sl < -1e-13)[0] if h not in set(epW)]
        if bad:
            W = sorted(set(epW).union(bad))
            if len(W) != len(epW):
                epW = W
                ep = sp.EqProjector(epW)
        Qs, Rs = ep.project(Qs, Rs, sl)
        Yq = [Q + C for Q, C in zip(Qs, corrQ)]
        Yr = [R + C for R, C in zip(Rs, corrR)]
        Pq = sp.psd_clip(Yq)
        Pr = sp.psd_clip(Yr)
        corrQ = [Y - P for Y, P in zip(Yq, Pq)]
        corrR = [Y - P for Y, P in zip(Yr, Pr)]
        Qs, Rs = Pq, Pr
        if it % 10 == 0 or it == maxit - 1:
            Qk, Rk = sp.kernel_project(Qs, Rs)
            slk = sp.slacks(Qk, Rk)
            m22 = np.abs(slk[E22]).max()
            print(f"  it{it:4d}: |W|={len(epW)} max|slack[E22]|={m22:.3e} "
                  f"min={slk.min():.3e} ({time.time()-t0:.0f}s)", flush=True)
            if m22 < 1e-12 and slk.min() > -1e-12:
                print("  CONVERGED")
                break
    Qs, Rs = sp.kernel_project(Qs, Rs)
    Qs = sp.psd_clip(Qs)
    Rs = sp.psd_clip(Rs)
    sl = sp.slacks(Qs, Rs)
    print(f"final: min slack {sl.min():.3e}, max|slack[E22]| "
          f"{np.abs(sl[E22]).max():.3e}")
    with open(os.path.join(DATA, f"{tag}.pkl"), "wb") as f:
        pickle.dump(dict(Q=Qs, R=Rs, W=epW, slack=sl), f)
    print(f"saved {tag}.pkl")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=os.path.join(DATA, "result_face.pkl"))
    ap.add_argument("--maxit", type=int, default=400)
    ap.add_argument("--tag", default="facepolished")
    a = ap.parse_args()
    run(a.src, maxit=a.maxit, tag=a.tag)
