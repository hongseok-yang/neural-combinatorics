"""Sequential, timed rebuild of an explicit ordered list of Lean modules.

The one-hour budget is shared by the entire list. Already existing artifacts
are not used to skip any listed source. Dependencies outside the list must be
built beforehand and are not included in this timing.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--seconds', type=float, default=3600)
    parser.add_argument('--gib', type=float, default=16)
    parser.add_argument('modules', nargs='+')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    results = []
    success = True
    total = len(args.modules)
    for index, module in enumerate(args.modules, 1):
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', module):
            raise ValueError(f'invalid module name: {module}')
        relative = Path(*module.split('.')).with_suffix('.lean')
        source = root/'lean'/relative
        artifact = Path('.lake/build/lib/lean')/relative.with_suffix('.olean')
        (root/'lean'/artifact).parent.mkdir(parents=True, exist_ok=True)
        remaining = args.seconds-(time.monotonic()-start)
        if remaining <= 0:
            success = False
            break
        stem = output/module/'compile'
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        command = [sys.executable, str(root/'experiments/run_bounded_lean.py'),
                   '--seconds', str(remaining), '--gib', str(args.gib),
                   '--cwd', str(root/'lean'), '--output', str(stem), '--',
                   args.lake, 'env', 'lean', '-M', '12288', '-j', '1',
                   '-o', str(artifact), str(relative)]
        run = subprocess.run(command, cwd=root, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True)
        # run_bounded_lean uses with_suffix, so retain that exact path rule.
        report_path = stem.with_suffix('.json')
        report = json.loads(report_path.read_text(encoding='utf-8'))
        report['module'] = module
        report['source_sha256'] = source_hash
        report['source_unchanged'] = source_hash == hashlib.sha256(source.read_bytes()).hexdigest()
        report['log'] = str(stem.with_suffix('.log'))
        results.append(report)
        used = time.monotonic()-start
        print(f"({index}/{total}) {module}: {report['elapsed_seconds']:.1f}s, "
              f"{report['peak_tree_private_bytes']/2**30:.2f} GiB private, "
              f"exit {run.returncode}; {used:.0f}s used, "
              f"{args.seconds-used:.0f}s of budget left", flush=True)
        if run.returncode or not report['source_unchanged']:
            success = False
            break
    summary = dict(success=success and len(results)==len(args.modules),
                   requested_modules=args.modules, results=results,
                   elapsed_seconds=round(time.monotonic()-start,3),
                   limit_seconds=args.seconds, limit_gib=args.gib,
                   peak_private_bytes=max((r['peak_tree_private_bytes'] for r in results),default=0),
                   peak_rss_bytes=max((r['peak_tree_rss_bytes'] for r in results),default=0))
    (output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    return 0 if summary['success'] else 1


if __name__=='__main__':
    sys.exit(main())
