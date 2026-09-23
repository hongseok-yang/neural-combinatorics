import os, json, collections, sys, glob
from datetime import datetime, timezone, timedelta
sys.stdout.reconfigure(encoding='utf-8')
K = timezone(timedelta(hours=9))


def T(ts):
    return datetime.fromtimestamp(ts, K).strftime('%m-%d %H:%M')


R = r'c:\Users\mekty\neural-combinatorics\discussions\taeyoung-conjecture\exhaustive_research\lean'
rows = json.load(open(os.path.join(os.path.dirname(__file__), 'lean_ts.json')))
g = collections.defaultdict(list)
for r in rows:
    g[r['group']].append(r)
print('group | source final (max write) | olean built (min..max)')
for k, rs in sorted(g.items(), key=lambda kv: min(r['born'] for r in kv[1])):
    ob = [r['olean_mod'] for r in rs if r['olean_mod']]
    print(f"{k:26s} {T(max(r['modified'] for r in rs))} | {T(min(ob)) if ob else '-'} .. {T(max(ob)) if ob else '-'}")

base = os.path.join(R, '.lake', 'build', 'lib', 'lean')
orph = []
for o in glob.glob(os.path.join(base, 'Taeyoung', '**', '*.olean'), recursive=True):
    rel = os.path.relpath(o, base)[:-6]
    if not os.path.exists(os.path.join(R, rel + '.lean')):
        m = os.stat(o).st_mtime
        if datetime(2026, 8, 13, tzinfo=K) <= datetime.fromtimestamp(m, K) < datetime(2026, 8, 21, tzinfo=K):
            orph.append((T(m), rel.replace(os.sep, '/'), os.path.getsize(o)))
print('\norphan oleans from Aug 13-20 (compiled module whose source no longer exists):', len(orph))
for x in sorted(orph):
    print('  ', x)
