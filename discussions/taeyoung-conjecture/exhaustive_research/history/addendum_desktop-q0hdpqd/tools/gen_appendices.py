"""Generate ADDENDUM_PROMPTS.md (verbatim prompt list, D.n) and addendum_index.json
from sessions.json. Adapted from history/tools/gen_appendices.py.

Fork handling: the six 2026-08-24 sessions are forks of `01a02ea5`; a fork's rollout
replays the parent's prompts and final messages with the fork instant as timestamp.
Replayed prompts are suppressed from the D list (they are byte-identical to the
parent's, which is listed); the index keeps every turn and marks replays.
"""
import json, os, re, sys, collections
from datetime import datetime

sys.stdout.reconfigure(encoding='utf-8')
D = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(D)
os.makedirs(OUT, exist_ok=True)
data = json.load(open(os.path.join(D, 'sessions.json'), encoding='utf-8'))
F = '%Y-%m-%d %H:%M:%S'
THIS_SESSION = '01f2d234-3490-45e5-8c83-5b51ff20798a'
PARENT_FORK = '01a02ea5'
FORKS = {'01a02f68-1b82', '01a02f68-37b6', '01a02f68-5069', '01a02f8f', '01a02f93', '01a02f97'}


def is_fork(s):
    return s['id'][:13] in FORKS or s['id'][:8] in {f[:8] for f in FORKS}


def hours(a, b):
    if not a or not b:
        return None
    return (datetime.strptime(b, F) - datetime.strptime(a, F)).total_seconds() / 3600


def is_review(s):
    return any('auto-review' in m for m in s['models'])


def model_label(s):
    return '; '.join(m.split(' (x')[0] for m in s['models'])


codex = sorted(data['codex'], key=lambda s: s['start'])

# ------------------------------------------------ chronological prompt list
seen_texts = {}
events = []
for s in codex:
    if is_review(s):
        continue
    turn_of = {}
    for t in s['turns']:
        if t.get('prompt') and t.get('model') and not t.get('replayed'):
            turn_of.setdefault(t['prompt'].strip(), t['model'])
    for p in s['prompts']:
        key = p['text'].strip()
        if key in seen_texts:
            continue  # replayed copy inside a fork
        seen_texts[key] = s['id']
        tm = turn_of.get(key)
        label = f'{tm[0]} / effort={tm[1]}' if tm else model_label(s)
        events.append(dict(time=p['time'], tool='Codex (VS Code)' if s.get('originator') == 'codex_vscode'
                           else 'Codex (codex exec, non-interactive)',
                           session=s['id'], role=s['role'], model=label, text=p['text']))
events.sort(key=lambda e: e['time'])


def fence(text):
    n = 3
    while '`' * n in text:
        n += 1
    return '`' * n + 'text\n' + text.rstrip() + '\n' + '`' * n


NOTES = {
    ('2026-08-23 21:43', '01a02ea5'): 'This prompt was re-run six more times at effort `ultra` in the forked sessions '
        '`01a02f68-1b82`, `01a02f68-37b6`, `01a02f68-5069`, `01a02f8f`, `01a02f93`, `01a02f97` (2026-08-24 01:15–02:23). '
        'The forks replay the whole conversation up to and including the prompt of 01:15:27 byte-for-byte, so their '
        'prompts are not repeated here.',
    ('2026-08-25 01:34', '01a0349f'): 'The `/goal` objective is inline (no attachment file); the same text appears as the '
        'thread goal in the goal events of the session.',
    ('2026-08-26 04:06', '01a03a51'): 'The plan file this prompt refers to, `C5_FIRST_INTERVAL_RESEARCH_PLAN.md`, was '
        'written by Codex itself 15 minutes earlier, at the end of session `01a0349f` (turn 9, 03:46–03:51), at the '
        'user\'s request.',
}

out = []
w = out.append
w('# Addendum Appendix D — User prompts on DESKTOP-Q0HDPQD, verbatim and in order\n')
w('Every prompt the human typed into Codex on this device in sessions whose working directory is '
  '`discussions/taeyoung-conjecture/exhaustive_research` (primary), `papers/oddcycle_bound` (related work), or another '
  '`taeyoung-conjecture` folder (flagged). Times are Korea Standard Time (UTC+9). Prompts are reproduced byte-for-byte, '
  'including the IDE-context header that the Codex VS Code extension prepends (`# Context from my IDE setup:`), typos, '
  'and the Markdown escapes of the input box (`\\_`, `&#x20;`). Approval-reviewer prompts (machine-generated) are '
  'excluded, as are the prompts a fork replays from its parent. No surviving Claude Code transcript on this device '
  'contains prompts from the window (30-day retention); the session that compiled this addendum is excluded.\n')
di = 0
for e in events:
    di += 1
    tag = {'primary': '', 'related': ' · related work (oddcycle paper)', 'flagged': ' · flagged (outside window)'}[e['role']]
    w(f"\n## D.{di} — {e['time']} · {e['tool']} · `{e['session'][:8]}` · {e['model']}{tag}\n")
    w(fence(e['text']))
    note = NOTES.get((e['time'][:16], e['session'][:8]))
    if note:
        w(f'\n*Note:* {note}')
open(os.path.join(OUT, 'ADDENDUM_PROMPTS.md'), 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print('prompts', di)

# ------------------------------------------------ JSON index
idx = dict(timezone='Asia/Seoul (UTC+9)', generated='2026-09-23', device='DESKTOP-Q0HDPQD (Windows 11 Home 10.0.26200)',
           sessions=[])
for s in codex:
    u = s['total_usage'] or {}
    role = 'approval-reviewer' if is_review(s) else ('worker-fork' if is_fork(s) else 'worker')
    idx['sessions'].append(dict(
        tool='Codex', role=role, relevance=s['role'], id=s['id'], interface=s.get('originator'),
        cli_version=s['cli'], cwd=s.get('cwd'), models=s['models'], db_effort=s['db_effort'],
        start=s['start'], end=s['end'], usage=u, compactions=s['compactions'],
        goal=s['goal'], goal_events=s['goal_events'], tool_calls=s['tool_calls'], files=s['files'],
        turn_contexts=s['turn_contexts'],
        turns=[dict(start=t['start'], end=t.get('end'), status=t.get('status'), model=t.get('model'),
                    replayed=bool(t.get('replayed')), prompt=t.get('prompt'), files=t['files'],
                    commentary=[] if t.get('replayed') else t.get('commentary', []),
                    report=t.get('final')) for t in s['turns']],
        prompts=[] if is_review(s) else s['prompts']))
for s in data['claude']:
    if s['id'] == THIS_SESSION:
        idx['sessions'].append(dict(tool='Claude Code', role='addendum-compiler (excluded from the history)',
                                    id=s['id'], version=s['version'], models=s['models'],
                                    start=s.get('start'), end=s.get('end'), usage=s['usage']))
        continue
    if s['subagent']:
        role = 'subagent'
    elif (s.get('start') or '') > '2026-08-27':
        role = 'post-campaign session, outside the addendum window'
    else:
        role = 'worker'
    idx['sessions'].append(dict(tool='Claude Code', role=role, id=s['id'],
                                version=s['version'], models=s['models'], start=s.get('start'), end=s.get('end'),
                                usage=s['usage'], tool_calls=s['tools'], files=s['files']))
json.dump(idx, open(os.path.join(OUT, 'addendum_index.json'), 'w', encoding='utf-8'), ensure_ascii=False, indent=1)

# ------------------------------------------------ sessions table (markdown fragment for the history)
rows = []
for s in codex:
    u = s['total_usage'] or {}
    role = 'reviewer' if is_review(s) else ('fork' if is_fork(s) else 'worker')
    eff = re.findall(r'effort=(\w+) \(x(\d+)', '; '.join(s['models']))
    effs = ', '.join(f'{e}×{n}' for e, n in eff)
    tc = s['tool_calls']
    live = [t for t in s['turns'] if not t.get('replayed')]
    rows.append(f"| `{s['id'][:8]}` | {role} | {s['start'][5:16]} → {s['end'][5:16]} | {effs} | "
                f"{len(live)} | {sum(1 for p in s['prompts'] if seen_texts.get(p['text'].strip()) == s['id'])} | "
                f"{(u.get('total_tokens') or s['db_tokens'] or 0)/1e6:,.1f} M | {u.get('output_tokens', 0):,} | "
                f"{u.get('reasoning_output_tokens', 0):,} | {tc.get('shell_command', 0) + tc.get('exec_command', 0):,} | "
                f"{tc.get('apply_patch', 0):,} |")
open(os.path.join(D, 'sessions_table.md'), 'w', encoding='utf-8').write('\n'.join(rows) + '\n')
print('index sessions', len(idx['sessions']))
