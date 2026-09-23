"""Creation / modification / build timestamps of the Lean files that entered git in the
Aug 18 bulk commit (2cb386309) and the Aug 19 commit (239519dfb)."""
import os, subprocess, sys, collections, json
from datetime import datetime, timezone, timedelta
sys.stdout.reconfigure(encoding='utf-8')
KST = timezone(timedelta(hours=9))
REPO = r'c:\Users\mekty\neural-combinatorics\discussions\taeyoung-conjecture\exhaustive_research'
PFX = 'discussions/taeyoung-conjecture/exhaustive_research/'


def run(*a):
    return subprocess.run(a, cwd=REPO, capture_output=True, text=True, encoding='utf-8').stdout


def t(ts):
    return datetime.fromtimestamp(ts, KST).strftime('%m-%d %H:%M') if ts else None


rows = []
for c in ('2cb386309', '239519dfb'):
    for f in run('git', 'show', '--diff-filter=A', '--name-only', '--format=', c, '--', 'lean/Taeyoung').split():
        if not f.endswith('.lean'):
            continue
        rel = f[len(PFX):]
        p = os.path.join(REPO, rel)
        if not os.path.exists(p):
            continue
        st = os.stat(p)
        mod = rel[len('lean/'):-len('.lean')]
        olean = os.path.join(REPO, 'lean', '.lake', 'build', 'lib', 'lean', mod + '.olean')
        ob = os.stat(olean) if os.path.exists(olean) else None
        lines = open(p, encoding='utf-8', errors='replace').read().count('\n')
        parts = mod.split('/')
        grp = parts[1] if len(parts) > 2 and parts[1] != 'Methods' else ('/'.join(parts[1:3]) if parts[1] == 'Methods' else parts[1])
        rows.append(dict(file=rel, commit=c, group=grp.replace('.lean', ''), lines=lines,
                         born=st.st_birthtime, modified=st.st_mtime,
                         olean_born=ob.st_birthtime if ob else None, olean_mod=ob.st_mtime if ob else None))
json.dump(rows, open(os.path.join(os.path.dirname(__file__), 'lean_ts.json'), 'w'), indent=1)
print(len(rows), 'files')
# distribution of creation times by day
byday = collections.Counter(t(r['born'])[:5] for r in rows)
print('created per day:', sorted(byday.items()))
bymod = collections.Counter(t(r['modified'])[:5] for r in rows)
print('last modified per day:', sorted(bymod.items()))
# per group: first creation, last modification, lines
g = collections.defaultdict(list)
for r in rows:
    g[r['group']].append(r)
print()
for k, rs in sorted(g.items(), key=lambda kv: min(r['born'] for r in kv[1])):
    print(f"{k:28s} files={len(rs):3d} lines={sum(r['lines'] for r in rs):6d} created {t(min(r['born'] for r in rs))} .. {t(max(r['born'] for r in rs))}  last-mod {t(max(r['modified'] for r in rs))}")
