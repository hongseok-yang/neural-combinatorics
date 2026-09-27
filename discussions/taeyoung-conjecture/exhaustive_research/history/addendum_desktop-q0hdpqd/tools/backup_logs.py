"""Copy the raw agent logs behind the DESKTOP-Q0HDPQD addendum into a backup tree that
mirrors ~/.codex and ~/.claude. Adapted from history/tools/backup_logs.py.

Included: every Codex rollout whose cwd is inside neural-combinatorics or
FlagAlgebra-Graph (project rollouts plus the related-work context cited in the
addendum), the Codex state/goals databases (consistent snapshots via the backup
API), the session index, the surviving Claude memory notes of the projects cited,
and the untracked repository files produced in the window (experiments scripts,
notes, the C5 plan and c5_exp). Excluded on purpose: ~/.codex/logs_2.sqlite
(application diagnostics, no conversation content) and the live transcript of the
addendum-writing Claude session (still being appended to while this runs).
"""
import glob, hashlib, json, os, shutil, sqlite3, sys

sys.stdout.reconfigure(encoding='utf-8')
HOME = os.path.expanduser('~')
DEST = os.path.join(HOME, 'ai_session_backups', 'taeyoung_exhaustive_research_desktop-q0hdpqd')
REPO = r'C:\Users\mekje\KAIST\CS\neural-combinatorics\discussions\taeyoung-conjecture\exhaustive_research'
copied = []


def copy(src, rel_to=HOME, prefix=''):
    dst = os.path.join(DEST, prefix, os.path.relpath(src, rel_to))
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy2(src, dst)
    copied.append(dst)


for f in sorted(glob.glob(os.path.join(HOME, '.codex', 'sessions', '*', '*', '*', '*.jsonl'))):
    with open(f, encoding='utf-8') as fh:
        first = fh.readline()
    if 'neural-combinatorics' in first or 'FlagAlgebra-Graph' in first:
        copy(f)
copy(os.path.join(HOME, '.codex', 'session_index.jsonl'))
for name in ['state_5.sqlite', 'goals_1.sqlite']:
    src = sqlite3.connect(f"file:{os.path.join(HOME, '.codex', name)}?mode=ro", uri=True)
    dst_path = os.path.join(DEST, '.codex', name)
    os.makedirs(os.path.dirname(dst_path), exist_ok=True)
    if os.path.exists(dst_path):
        os.remove(dst_path)
    dst = sqlite3.connect(dst_path)
    src.backup(dst)
    dst.close(); src.close()
    copied.append(dst_path)

for proj in ['c--Users-mekje-KAIST-CS-neural-combinatorics',
             'c--Users-mekje-KAIST-CS-neural-combinatorics-discussions-goodman-style-bound',
             'c--Users-mekje-KAIST-CS-neural-combinatorics-discussions-schur-decomposition',
             'c--Users-mekje-KAIST-CS-FlagAlgebra-Graph']:
    for f in glob.glob(os.path.join(HOME, '.claude', 'projects', proj, 'memory', '*.md')):
        copy(f)
copy(os.path.join(HOME, '.claude', 'settings.json'))

# Untracked project files produced in the window (git does not keep them).
extra = ['C5_FIRST_INTERVAL_RESEARCH_PLAN.md', 'notes/dense_degree_power_bias.tex']
extra += [os.path.relpath(p, REPO) for p in glob.glob(os.path.join(REPO, 'c5_exp', '**', '*'), recursive=True)
          if os.path.isfile(p) and '__pycache__' not in p]
import subprocess
st = subprocess.run(['git', '-C', REPO, 'status', '--porcelain'], capture_output=True, text=True).stdout
for line in st.splitlines():
    p = line[3:].strip()
    if p.endswith('.py') and '/experiments/' in p:
        extra.append(os.path.relpath(os.path.join(REPO, '..', '..', '..', p), REPO).replace('\\', '/'))
extra = sorted(set(e.replace('\\', '/') for e in extra))
for rp in extra:
    src = os.path.normpath(os.path.join(REPO, rp))
    if os.path.isfile(src):
        copy(src, rel_to=os.path.dirname(REPO), prefix='repo_untracked')

# ChatGPT account export zip (supplied by the author 2026-09-27), kept whole.
for z in glob.glob(os.path.join(REPO, '49f6*.zip')):
    copy(z, rel_to=REPO, prefix='chatgpt_export')

manifest = []
for p in sorted(copied):
    h = hashlib.sha256()
    with open(p, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    manifest.append(dict(path=os.path.relpath(p, DEST).replace('\\', '/'), bytes=os.path.getsize(p), sha256=h.hexdigest()))
with open(os.path.join(DEST, 'MANIFEST.json'), 'w', encoding='utf-8') as fh:
    json.dump(manifest, fh, indent=1)
with open(os.path.join(DEST, 'README.md'), 'w', encoding='utf-8') as fh:
    fh.write('''# Raw-log backup for history/addendum_desktop-q0hdpqd (created 2026-09-23)

Mirror of the `~/.codex` and `~/.claude` files behind the addendum, from DESKTOP-Q0HDPQD.
`.codex/sessions/` holds every rollout whose working directory is inside neural-combinatorics
or FlagAlgebra-Graph; `.codex/state_5.sqlite` and `goals_1.sqlite` are consistent snapshots
taken with the SQLite backup API. `.claude/projects/*/memory/` holds the surviving memory
notes (the transcripts of 19-26 Aug were already deleted by Claude Code's 30-day retention
before this backup; the addendum-writing session's own transcript is excluded because it was
still growing while the backup ran). `repo_untracked/` keeps the project files git does not
track: the window's `experiments/*.py`, `notes/dense_degree_power_bias.tex`,
`C5_FIRST_INTERVAL_RESEARCH_PLAN.md` and `c5_exp/`. `chatgpt_export/` keeps the author's
ChatGPT account export zip whole (conversations-*.json shards inside cover the ChatGPT Pro
lane of Appendix E). `~/.codex/logs_2.sqlite` (application diagnostics, no conversation
content) is not copied.

Verify integrity against `MANIFEST.json` (path, bytes, SHA-256). Re-running the addendum
extraction against this tree (`HISTORY_LOG_ROOT` pointing here) reproduces
`ADDENDUM_PROMPTS.md` and `addendum_index.json`.
''')
print(DEST, len(manifest), 'files', round(sum(m['bytes'] for m in manifest) / 2**20, 1), 'MiB')
