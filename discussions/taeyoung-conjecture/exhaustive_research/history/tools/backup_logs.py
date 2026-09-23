"""Copy the raw agent logs behind history/ into a backup tree that mirrors ~/.codex and ~/.claude."""
import glob, hashlib, json, os, shutil, sqlite3, sys

sys.stdout.reconfigure(encoding='utf-8')
HOME = os.path.expanduser('~')
DEST = os.path.join(HOME, 'ai_session_backups', 'taeyoung_exhaustive_research')
copied = []


def copy(src, rel_to=HOME, prefix=''):
    dst = os.path.join(DEST, prefix, os.path.relpath(src, rel_to))
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy2(src, dst)
    copied.append(dst)


# Codex rollouts: every session whose cwd is inside neural-combinatorics
# (this project plus the goodman-style-bound / oddcycle prehistory).
for f in sorted(glob.glob(os.path.join(HOME, '.codex', 'sessions', '*', '*', '*', '*.jsonl'))):
    with open(f, encoding='utf-8') as fh:
        first = fh.readline()
    if 'neural-combinatorics' in first:
        copy(f)
for name in ['session_index.jsonl']:
    copy(os.path.join(HOME, '.codex', name))
for f in glob.glob(os.path.join(HOME, '.codex', 'attachments', '**', '*'), recursive=True):
    if os.path.isfile(f):
        copy(f)
# Codex SQLite state: consistent snapshots via the backup API (includes WAL contents).
for name in ['state_5.sqlite', 'goals_1.sqlite', 'thread_history_1.sqlite']:
    src = sqlite3.connect(f"file:{os.path.join(HOME, '.codex', name)}?mode=ro", uri=True)
    dst_path = os.path.join(DEST, '.codex', name)
    os.makedirs(os.path.dirname(dst_path), exist_ok=True)
    if os.path.exists(dst_path):
        os.remove(dst_path)
    dst = sqlite3.connect(dst_path)
    src.backup(dst)
    dst.close(); src.close()
    copied.append(dst_path)

# Claude Code: every transcript, subagent transcript and tool-result file of this project,
# plus the memory notes of the parent project (they identify the deleted Aug 13-20 session).
proj = os.path.join(HOME, '.claude', 'projects', 'c--Users-mekty-neural-combinatorics-discussions-taeyoung-conjecture-exhaustive-research')
for f in glob.glob(os.path.join(proj, '**', '*'), recursive=True):
    if os.path.isfile(f):
        copy(f)
for f in glob.glob(os.path.join(HOME, '.claude', 'projects', 'c--Users-mekty-neural-combinatorics', 'memory', '*.md')):
    copy(f)

# Process documents and scripts in the project that git does not track (untracked or ignored),
# copied under repo_untracked/ with their project-relative paths.
REPO = os.path.join(HOME, 'neural-combinatorics', 'discussions', 'taeyoung-conjecture', 'exhaustive_research')
extra = ['lean/docs/TODO.md', 'lean/docs/README.md', 'lean/README.md',
         'HANDOFF_ATLAS_188_171_174_153.md', 'git_verification_untracked_inventory.json']
extra += [os.path.relpath(p, REPO) for p in glob.glob(os.path.join(REPO, 'codes', '**', '*.py'), recursive=True)
          if '__pycache__' not in p]
for rp in extra:
    src = os.path.join(REPO, rp)
    if os.path.isfile(src):
        copy(src, rel_to=os.path.join(REPO, '..'), prefix='repo_untracked')

# Manifest with sizes and SHA-256.
manifest = []
for p in sorted(copied):
    h = hashlib.sha256()
    with open(p, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    manifest.append(dict(path=os.path.relpath(p, DEST).replace('\\', '/'), bytes=os.path.getsize(p), sha256=h.hexdigest()))
with open(os.path.join(DEST, 'MANIFEST.json'), 'w', encoding='utf-8') as fh:
    json.dump(manifest, fh, indent=1)
print(DEST, len(manifest), 'files', round(sum(m['bytes'] for m in manifest) / 2**20, 1), 'MiB')
