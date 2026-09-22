"""Inline ten small density modules into the five corresponding block sums.

All declarations and proofs are retained. This reduces the source-file count for
rows with multiple intervals without changing the mathematical dependency work.
Only generated, unverified row sources may be transformed.
"""

import argparse
import hashlib
import json
from pathlib import Path
from generate_compact_s4_psd import PREFIX, row_tag


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--atlas', required=True, type=int)
    parser.add_argument('--namespace-suffix', default='')
    args = parser.parse_args()
    atlas = args.atlas
    example = Path(f'lean/Taeyoung/Examples/Graph{atlas}.lean').read_text(encoding='utf-8')
    assert 'formalization := .verified' not in example, 'Preserve accepted row sources.'
    ns = PREFIX+'.'+row_tag(dict(atlas=atlas, lean_namespace_suffix=args.namespace_suffix))
    root = (Path('lean')/Path(*ns.split('.'))).resolve()
    assert root.is_relative_to(Path.cwd().resolve())
    all_sources = {p:p.read_text(encoding='utf-8') for p in root.glob('*.lean')}
    changes, removed = [], []
    for b in range(5):
        target = root/f'BlockSum{b}.lean'
        donors = [root/f'Block{k:02d}Density.lean' for k in (b,b+5)]
        donor_imports = [f'import {ns}.{p.stem}' for p in donors]
        assert all(line in all_sources[target].splitlines() for line in donor_imports)
        for p,text in all_sources.items():
            if p != target:
                assert not any(line in text.splitlines() for line in donor_imports), p
        imports, bodies = [], []
        for p in donors+[target]:
            text = all_sources[p]
            lines = text.splitlines(keepends=True)
            for line in lines:
                if line.startswith('import ') and line.strip() not in donor_imports and line.strip() not in imports:
                    imports.append(line.strip())
            bodies.append(''.join(line for line in lines if not line.startswith('import ')).strip())
        result = '\n'.join(imports)+'\n\n'+'\n\n'.join(bodies)+'\n'
        changes.append((target,result))
        removed.extend(donors)
    for target,result in changes:
        target.write_text(result,encoding='utf-8')
    for donor in removed:
        assert donor.resolve().parent == root
        donor.unlink()
    record = dict(atlas=atlas, removed_modules=[p.stem for p in removed],
                  retained_targets=[p.stem for p,_ in changes],
                  original_sha256={p.name:hashlib.sha256(all_sources[p].encode()).hexdigest() for p in removed},
                  reason='Proof declarations retained verbatim inside their block-sum modules; no cached-proof shortcut.')
    suffix = '_'+args.namespace_suffix.lower() if args.namespace_suffix else ''
    output = Path(f'lean/verification_runs/atlas{atlas}/density_inlining{suffix}.json')
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(f'Inlined ten density modules; {len(list(root.glob("*.lean")))} row method files now present.',flush=True)


if __name__ == '__main__':
    main()
