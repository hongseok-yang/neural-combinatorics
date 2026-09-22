"""Run one Lean command with a wall-time budget and process-tree memory audit.

Use the pinned Lake executable explicitly. Logs and a JSON measurement survive
failures. Only descendants of the process started here are monitored/terminated;
an independently running editor is never touched. Lean also receives its own
memory limit through the command arguments supplied by the caller.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

import psutil


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds', type=float, default=3600)
    parser.add_argument('--gib', type=float, default=16)
    parser.add_argument('--cwd', default='lean')
    parser.add_argument('--output', required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == '--':
        command = command[1:]
    if not command:
        parser.error('a command is required')
    output = Path(args.output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    start = time.monotonic()
    peak_rss = peak_private = 0
    reason = None
    known: dict[int, psutil.Process] = {}
    with output.with_suffix('.log').open('w', encoding='utf-8') as log:
        child = subprocess.Popen(command, cwd=args.cwd, env=env,
                                 stdout=log, stderr=subprocess.STDOUT)
        parent = psutil.Process(child.pid)
        known[parent.pid] = parent
        try:
            while child.poll() is None:
                try:
                    for proc in parent.children(recursive=True):
                        known[proc.pid] = proc
                except psutil.NoSuchProcess:
                    pass
                rss = private = 0
                for proc in list(known.values()):
                    try:
                        memory = proc.memory_info()
                        rss += memory.rss
                        private += getattr(memory, 'private', memory.rss)
                    except psutil.NoSuchProcess:
                        known.pop(proc.pid, None)
                peak_rss = max(peak_rss, rss)
                peak_private = max(peak_private, private)
                if max(rss, private) >= args.gib * 2**30:
                    reason = 'memory_limit'
                    break
                if time.monotonic() - start >= args.seconds:
                    reason = 'time_limit'
                    break
                time.sleep(0.2)
        except KeyboardInterrupt:
            reason = 'interrupted'
        finally:
            if reason is not None:
                for proc in reversed(list(known.values())):
                    try:
                        proc.kill()
                    except psutil.NoSuchProcess:
                        pass
            code = child.wait()
    report = dict(command=command, cwd=str(Path(args.cwd).resolve()),
                  elapsed_seconds=round(time.monotonic()-start, 3),
                  peak_tree_rss_bytes=peak_rss, peak_tree_private_bytes=peak_private,
                  sampling_seconds=0.2, exit_code=code,
                  termination=reason or 'exited',
                  time_limit_seconds=args.seconds, memory_limit_gib=args.gib)
    output.with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n',
                                          encoding='utf-8')
    print(json.dumps(report), flush=True)
    return code if code else (1 if reason else 0)


if __name__ == '__main__':
    sys.exit(main())
