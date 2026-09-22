"""Topologically order the Graph043/Graph196 closure; list modules to compile sequentially."""
import re, sys
from pathlib import Path
LEAN = Path('lean')
def path(m): return LEAN / (m.replace('.', '/') + '.lean')
def imports(m):
    return [x for line in path(m).read_text(encoding='utf-8-sig').splitlines() if line.startswith('import ')
            for x in line[7:].split() if x.startswith('Taeyoung')]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imports(m): visit(d)
    order.append(m)
visit('Taeyoung.Examples.Graph043'); n43 = len(order)
visit('Taeyoung.Examples.Graph196')
def olean(m): return LEAN / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
todo, prebuilt_missing = [], []
for m in order:
    if 'Atlas43' in m or 'Graph043' in m or 'Graph196' in m or 'Atlas196' in m or m in order[n43:]:
        todo.append(m)
    elif not olean(m).exists():
        prebuilt_missing.append(m)
print('closure', len(order), 'to compile', len(todo), 'prebuilt prerequisites missing olean:', prebuilt_missing)
Path('lean/verification_runs/atlas43/modules.txt').write_text('\n'.join(todo) + '\n')
print('first 5:', todo[:5]); print('last 5:', todo[-5:])
