"""Retain each block's data, PSD and expansion proofs in one Lean module.

Only unverified row sources may be merged. All imports into the selected
namespace are updated; donors are removed only after their complete bodies
have been written into the merged module. No proof is omitted or cached away.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

from generate_compact_s4_psd import PREFIX, row_tag


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--atlas', type=int, required=True)
    parser.add_argument('--namespace-suffix', default='')
    parser.add_argument('--blocks', nargs='+', type=int, default=list(range(10)))
    args = parser.parse_args()
    assert len(set(args.blocks)) == len(args.blocks)
    assert all(0 <= b < 10 for b in args.blocks)
    workspace = Path(__file__).resolve().parents[1]
    lean = workspace/'lean'
    example = lean/f'Taeyoung/Examples/Graph{args.atlas}.lean'
    assert 'formalization := .verified' not in example.read_text(encoding='utf-8')
    tag = row_tag(dict(atlas=args.atlas, lean_namespace_suffix=args.namespace_suffix))
    ns = PREFIX+'.'+tag
    root = (lean/Path(*ns.split('.'))).resolve()
    root.relative_to(workspace)
    label = args.namespace_suffix.lower() or 'single'
    output = workspace/f'lean/verification_runs/atlas{args.atlas}/block_merges'/f'{label}_{"_".join(map(str,args.blocks))}.json'
    assert not output.exists(), output
    sources = {p:p.read_text(encoding='utf-8') for p in root.glob('*.lean')}
    mapping, groups = {}, []
    for b in range(10):
        stem = f'Block{b:02d}'
        if root/f'{stem}.lean' in sources:
            for suffix in ('Data','PSD','ExpansionData','Expansion'):
                mapping[ns+'.'+stem+suffix] = ns+'.'+stem
    for b in args.blocks:
        stem = f'Block{b:02d}'
        donors = [root/f'{stem}{s}.lean' for s in ('Data','PSD','ExpansionData','Expansion')]
        target = root/f'{stem}.lean'
        assert not target.exists(), target
        assert all(p in sources for p in donors), donors
        for p in donors:
            mapping[ns+'.'+p.stem] = ns+'.'+stem
        groups.append((target, donors))

    def transform(text, self_module):
        imports, body = [], []
        for line in text.splitlines(keepends=True):
            match = re.fullmatch(r'import ([A-Za-z0-9_.]+)\s*', line)
            if match:
                dep = mapping.get(match[1], match[1])
                if dep != self_module and dep not in imports:
                    imports.append(dep)
            else:
                body.append(line)
        return '\n'.join('import '+dep for dep in imports)+'\n\n'+''.join(body).strip()+'\n'

    changed = {}
    removed = {p for _, donors in groups for p in donors}
    for target, donors in groups:
        text = '\n\n'.join(sources[p] for p in donors)
        changed[target] = transform(text, ns+'.'+target.stem)
    for p, text in sources.items():
        if p not in removed and any('import '+old+'\n' in text for old in mapping):
            updated = transform(text, ns+'.'+p.stem)
            if updated != text:
                changed[p] = updated
    for p, text in changed.items():
        p.resolve().relative_to(root)
        p.write_text(text, encoding='utf-8')
    for p in removed:
        assert p.resolve().parent == root
        p.unlink()
    record = dict(atlas=args.atlas, namespace_suffix=args.namespace_suffix, blocks=args.blocks,
                  original_sha256={p.name:hashlib.sha256(sources[p].encode()).hexdigest() for p in removed},
                  merged_sha256={p.name:hashlib.sha256(changed[p].encode()).hexdigest() for p,_ in groups},
                  reason='All original declarations and proofs retained; imports redirected to merged blocks.')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print(f'Merged {len(groups)} blocks in {ns}; removed {3*len(groups)} source files.')


if __name__ == '__main__':
    main()
