"""Generate one complete, unverified compact S4 row from its interval pieces.

Consumes independently audited compact candidates, named either by
`--lower/--upper` or by repeated `--piece SUFFIX=PATH` in interval order. A row
whose S4 pieces start above the admissible endpoint names the hand-written
module covering the rest with `--low-module/--low-right`; that one module is
the only Lean source the row may already contain. Refuses to overwrite
existing row methods or verified catalogue examples. The generated example is
staged; only the fresh acceptance driver may install it.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from generate_compact_s4_psd import PREFIX, row_tag


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--atlas', type=int, required=True)
    parser.add_argument('--lower')
    parser.add_argument('--upper')
    parser.add_argument('--piece', action='append', default=[], metavar='SUFFIX=PATH',
                        help='Namespace suffix and audited candidate of one S4 piece, in interval order.')
    parser.add_argument('--low-module',
                        help='Hand-written row module covering the range left of the first S4 piece.')
    parser.add_argument('--low-right',
                        help='Right endpoint of that module, where the first S4 piece starts.')
    args = parser.parse_args()
    if args.piece:
        assert args.lower is None and args.upper is None, 'Give either --piece or --lower/--upper.'
        pieces = []
        for item in args.piece:
            suffix,sep,path = item.partition('=')
            assert sep and suffix and path, item
            pieces.append((suffix,path))
    else:
        assert args.lower and args.upper, 'Give both --lower and --upper, or use --piece.'
        pieces = [('Lower',args.lower),('Upper',args.upper)]
    assert (args.low_module is None) == (args.low_right is None), \
        'A low module and its right endpoint are given together.'
    workspace = Path(__file__).resolve().parents[1]
    scripts = workspace/'experiments'
    atlas = args.atlas
    example = workspace/f'lean/Taeyoung/Examples/Graph{atlas}.lean'
    assert 'formalization := .verified' not in example.read_text(encoding='utf-8')
    root = workspace/f'lean/Taeyoung/Methods/RootedSOS/CompactS4/Atlas{atlas}'
    low = root/f'{args.low_module}.lean' if args.low_module else None
    if low is not None:
        assert low.is_file(), f'Write {low} before preparing the row.'
    assert not any(p for p in root.rglob('*.lean') if p != low), \
        'Existing row methods must be preserved.'
    candidates = []
    for suffix,path in pieces:
        c = json.loads(Path(path).read_text(encoding='utf-8'))
        assert int(c['atlas']) == atlas
        c['lean_namespace_suffix'] = suffix
        row_tag(c)
        candidate = scripts/f'atlas{atlas}_compact_{suffix.lower()}_namespaced.json'
        assert not candidate.exists(), candidate
        candidates.append((suffix,c,candidate))

    def run(script,*arguments):
        subprocess.run([sys.executable,'-X','utf8',str(scripts/script),*map(str,arguments)],
                       cwd=workspace,check=True)

    run('generate_compact_s4_assembly.py',Path(pieces[-1][1]).resolve(),'--coloring-only')
    witnesses = []
    for suffix,c,candidate in candidates:
        candidate.write_text(json.dumps(c,separators=(',',':'))+'\n',encoding='utf-8')
        witness = scripts/f'atlas{atlas}_compact_{suffix.lower()}_group_witness.json'
        witnesses.append(witness)
        run('generate_compact_s4_psd.py',candidate)
        run('generate_compact_s4_expansion.py',candidate)
        run('export_compact_s4_group_totals.py',candidate)
        run('generate_compact_s4_group_totals.py',witness)
        run('generate_compact_s4_interval.py',witness)
        run('generate_compact_s4_density.py',candidate)
        run('generate_compact_s4_block_sums.py','--atlas',atlas,'--namespace-suffix',suffix)
        run('inline_compact_s4_density.py','--atlas',atlas,'--namespace-suffix',suffix)
        run('merge_compact_s4_blocks.py','--atlas',atlas,'--namespace-suffix',suffix)
    completion = ['--complete']
    if args.low_module:
        completion += ['--low-module',args.low_module,'--low-right',args.low_right]
    run('generate_compact_s4_piece_assembly.py',*witnesses,*completion)
    row_prefix = f'{PREFIX}.CompactS4.Atlas{atlas}.'
    files = list(root.rglob('*.lean'))
    for path in files:
        for dep in re.findall(r'^import ([A-Za-z0-9_.]+)',path.read_text(encoding='utf-8'),re.M):
            if dep.startswith(row_prefix):
                assert (workspace/'lean'/Path(*dep.split('.')).with_suffix('.lean')).exists(), dep
    assert len(files)+1 <= 100
    print(f'Prepared Atlas{atlas}: {len(files)+1} row files including the staged example.')


if __name__ == '__main__':
    main()
