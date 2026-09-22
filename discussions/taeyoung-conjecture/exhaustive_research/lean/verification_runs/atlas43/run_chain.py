"""Sequentially compile the whole Atlas 43 -> 196 chain with no time budget.

One `lake env lean -M <heap> -j 1` per module under run_bounded_lean.py's
process-tree cap (default 16 GiB).  Modules already built successfully in an
earlier run (`sequential_1`, `coresrows56_32gib`) are skipped.  A module that
fails on memory is retried once at 32 GiB and recorded as over-cap; any other
failure stops the run.  Results accumulate in results.jsonl; progress.txt gets
one line per module; done.flag is written at the end.
"""
import json, re, subprocess, sys, time, hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LAKE = 'C:/Users/mekty/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lake.exe'
RUNNER = ROOT / 'experiments/run_bounded_lean.py'
OUT = HERE / 'sequential_full'
OUT.mkdir(exist_ok=True)
CAP_GIB, HEAP_MIB = 16, 16384
RETRY_GIB, RETRY_HEAP_MIB = 32, 30720

modules = (HERE / 'modules.txt').read_text().split()

done = set()
prev = HERE / 'sequential_1/summary.json'
if prev.exists():
    done |= {r['module'] for r in json.loads(prev.read_text())['results'] if r['exit_code'] == 0}
if (HERE / 'coresrows56_32gib/compile.json').exists() and \
        json.loads((HERE / 'coresrows56_32gib/compile.json').read_text())['exit_code'] == 0:
    done.add('Taeyoung.Methods.RootedSOS.Atlas43CoresRows56')

def compile_once(module, gib, heap_mib, tag):
    rel = Path(*module.split('.')).with_suffix('.lean')
    olean = Path('.lake/build/lib/lean') / rel.with_suffix('.olean')
    (ROOT / 'lean' / olean).parent.mkdir(parents=True, exist_ok=True)
    stem = OUT / module / tag
    cmd = [sys.executable, str(RUNNER), '--seconds', '10000000', '--gib', str(gib),
           '--cwd', str(ROOT / 'lean'), '--output', str(stem), '--',
           LAKE, 'env', 'lean', '-M', str(heap_mib), '-j', '1', '-o', str(olean), str(rel)]
    subprocess.run(cmd, cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT)
    rep = json.loads(stem.with_suffix('.json').read_text(encoding='utf-8'))
    rep['module'] = module
    rep['tag'] = tag
    rep['source_sha256'] = hashlib.sha256((ROOT / 'lean' / rel).read_bytes()).hexdigest()
    log = stem.with_suffix('.log').read_text(encoding='utf-8', errors='replace')
    rep['memory_related'] = (rep['termination'] == 'memory_limit' or
                             bool(re.search(r'memory|heap|reduction got stuck|maximum recursion', log, re.I)))
    return rep

def note(line):
    with (HERE / 'progress.txt').open('a', encoding='utf-8') as f:
        f.write(line + '\n')
    print(line, flush=True)

start = time.monotonic()
note(f'start {time.strftime("%Y-%m-%d %H:%M:%S")}: {len(modules)} modules, {len(done)} already built, cap {CAP_GIB} GiB')
for i, module in enumerate(modules, 1):
    if module in done:
        continue
    rep = compile_once(module, CAP_GIB, HEAP_MIB, 'compile')
    status = 'ok'
    if rep['exit_code'] or rep['termination'] != 'exited':
        if rep['memory_related']:
            retry = compile_once(module, RETRY_GIB, RETRY_HEAP_MIB, 'retry32')
            if retry['exit_code'] == 0 and retry['termination'] == 'exited':
                status = 'ok_over_cap'
                rep = retry
            else:
                status = 'failed'
        else:
            status = 'failed'
    rep['status'] = status
    with (OUT / 'results.jsonl').open('a', encoding='utf-8') as f:
        f.write(json.dumps(rep) + '\n')
    note(f'[{i}/{len(modules)}] {module}: {rep["elapsed_seconds"]:.1f}s, '
         f'{rep["peak_tree_private_bytes"]/2**30:.2f} GiB, {status}, total {(time.monotonic()-start)/3600:.2f}h')
    if status == 'failed':
        note(f'STOP: {module} failed; see {OUT / module}')
        break
else:
    note(f'ALL DONE in {(time.monotonic()-start)/3600:.2f}h')
(HERE / 'done.flag').write_text(time.strftime('%Y-%m-%d %H:%M:%S'))
