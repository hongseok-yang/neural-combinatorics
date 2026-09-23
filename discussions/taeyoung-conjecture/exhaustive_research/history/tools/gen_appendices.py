"""Generate the verbatim-prompt appendix, the per-turn session log and a JSON index
from sessions.json (Codex) and a per-turn re-parse of the Claude Code transcripts."""
import json, os, re, sys, glob, collections
from datetime import datetime

sys.stdout.reconfigure(encoding='utf-8')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from extract import kst, rel, claude_text, NOISE, HOME

D = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1]
os.makedirs(OUT, exist_ok=True)
data = json.load(open(os.path.join(D, 'sessions.json'), encoding='utf-8'))
F = '%Y-%m-%d %H:%M:%S'
THIS_SESSION = '49b19681-c08f-4229-9552-590d971530c0'


def hours(a, b):
    if not a or not b:
        return None
    return (datetime.strptime(b, F) - datetime.strptime(a, F)).total_seconds() / 3600


def is_review(s):
    return any('auto-review' in m for m in s['models'])


def model_label(s):
    return '; '.join(m.split(' (x')[0] for m in s['models'])


# ------------------------------------------------ Claude per-turn re-parse
def claude_turns(path):
    turns, cur = [], None
    for line in open(path, encoding='utf-8'):
        try:
            d = json.loads(line)
        except Exception:
            continue
        ts = d.get('timestamp')
        t = d.get('type')
        if t == 'user' and not d.get('isMeta') and not d.get('isCompactSummary'):
            txt, tr = claude_text(d['message'].get('content'))
            if tr or not txt.strip() or txt.startswith(NOISE):
                continue
            cur = dict(start=kst(ts), end=kst(ts), prompt=txt, files=collections.Counter(), commits=[],
                       models=collections.Counter(), tools=collections.Counter(), final=None, subagents=[])
            turns.append(cur)
        elif t == 'assistant' and cur is not None:
            cur['end'] = kst(ts)
            m = d['message']
            if m.get('model') and m['model'] != '<synthetic>':
                cur['models'][f"{m['model']} / effort={d.get('effort')}"] += 1
            for c in m.get('content', []):
                if c.get('type') == 'tool_use':
                    cur['tools'][c['name']] += 1
                    inp = c.get('input', {})
                    if c['name'] in ('Edit', 'Write', 'NotebookEdit'):
                        cur['files'][rel(inp.get('file_path', '?'))] += 1
                    if c['name'] in ('Bash', 'PowerShell'):
                        for msg in re.findall(r'git commit[^\n]*?-m\s+["\']([^"\'\n]+)', inp.get('command', '')):
                            cur['commits'].append(msg)
                    if c['name'] == 'Agent':
                        cur['subagents'].append(inp.get('description'))
                elif c.get('type') == 'text' and c['text'].strip():
                    cur['final'] = c['text']
        elif ts and cur is not None:
            cur['end'] = max(cur['end'], kst(ts))
    return turns


CLAUDE_DIR = f'{HOME}/.claude/projects/c--Users-mekty-neural-combinatorics-discussions-taeyoung-conjecture-exhaustive-research'
claude_main = [s for s in data['claude'] if not s['subagent'] and s['id'] != THIS_SESSION]
claude_main.sort(key=lambda s: s['start'])
for s in claude_main:
    s['turn_list'] = claude_turns(f"{CLAUDE_DIR}/{s['id']}.jsonl")

codex = sorted(data['codex'], key=lambda s: s['start'])

# ------------------------------------------------ chronological prompt list
events = []
for s in codex:
    if is_review(s):
        continue
    for p in s['prompts']:
        events.append(dict(time=p['time'], tool='Codex (VS Code)' if s.get('originator') == 'codex_vscode' else 'Codex (codex exec, non-interactive)',
                           session=s['id'], model=model_label(s), text=p['text']))
for s in claude_main:
    for t in s['turn_list']:
        events.append(dict(time=t['start'], tool='Claude Code (VS Code)', session=s['id'],
                           model=', '.join(sorted(t['models'])) or ', '.join(k for k in s['models'] if k != '<synthetic>'),
                           text=t['prompt']))
events.sort(key=lambda e: e['time'])

ATT = {
    'ff37a146-56ea-43c1-854c-56cc83e886fd': f'{HOME}/.codex/attachments/ff37a146-56ea-43c1-854c-56cc83e886fd/goal-objective.md',
    '233b0e2b-aefd-470b-be31-e8544e07ff33': f'{HOME}/.codex/attachments/233b0e2b-aefd-470b-be31-e8544e07ff33/goal-objective.md',
}


def fence(text):
    n = 3
    while '`' * n in text:
        n += 1
    return '`' * n + 'text\n' + text.rstrip() + '\n' + '`' * n


out = []
w = out.append
w('# Appendix A — User prompts, verbatim and in order\n')
w('Every prompt the human typed into Codex or Claude Code while working in `exhaustive_research/`, '
  'reconstructed from the local session logs (see the main history, §2). Times are Korea Standard Time (UTC+9). '
  'Prompts are reproduced byte-for-byte, including typos, the Markdown escapes that the Codex VS Code input box inserted '
  '(`\\_`, `&#x20;`), and text the user pasted from earlier agent output. '
  'Approval-reviewer prompts (generated automatically by Codex) and this history-writing session are excluded. '
  'Where a prompt was written by an agent and pasted by the user, the note under the prompt says so.\n')
AUTHORED = {
    ('2026-08-13 12:37', '019ff931'): 'Drafted by Codex (session `019ff8c8`, turn 7, 12:36) at the user\'s request, then pasted verbatim.',
    ('2026-08-13 14:38', '019ff9a0'): 'Drafted by Codex (session `019ff931`, turn 5, 14:35–14:37) at the user\'s request. This first paste was interrupted after 24 s and re-issued as a Codex `/goal` (next entries).',
    ('2026-08-13 14:38', '019ff9a1'): 'The `/goal` command loads the attachment below, which is the Codex-drafted prompt of 14:38:14.',
    ('2026-08-18 11:50', '01a012c4'): 'Drafted by Codex (session `019ff9a1`, turn 39, 11:44–11:47); the user added the last sentence of item 9 of "Catalogue changes after an exact counterexample" ("Only revise lean/…GraphXXX.lean from excluded_middle to one side, and let the proof to be sorry."). Interrupted after 5 s and re-issued as a `/goal`.',
    ('2026-08-18 11:50', '01a012c6'): 'The `/goal` command loads the attachment below (the prompt of 11:50:01).',
    ('2026-08-13 19:21', '019ffaa3'): 'Non-interactive `codex exec` run (approval policy "never"). No human typed this in the Codex UI; its style and its stated purpose (Lean 4 formalization of forest Sidorenko) indicate that the concurrent Claude Code Lean worker dispatched it. This attribution is an inference; that Claude transcript no longer exists.',
    ('2026-09-22 12:20', 'd19b441c'): 'The user pasted the tail of the preceding Codex conversation (session `01a0c2be`) below the first paragraph.',
    ('2026-09-23 00:04', '272ea172'): 'The handoff file it refers to was written by Claude Fable 5.1 in session `d19b441c` (00:03).',
}
for i, e in enumerate(events, 1):
    w(f"\n## A.{i} — {e['time']} · {e['tool']} · `{e['session'][:8]}` · {e['model']}\n")
    w(fence(e['text']))
    note = AUTHORED.get((e['time'][:16], e['session'][:8]))
    if note:
        w(f'\n*Provenance:* {note}')
    m = re.search(r'attachments\\([0-9a-f-]{36})\\goal-objective\.md', e['text'])
    if m and e['text'].startswith('/goal') and m.group(1) in ATT:
        att = open(ATT[m.group(1)], encoding='utf-8').read()
        w(f"\n<details><summary>Attachment <code>{m.group(1)}/goal-objective.md</code> ({len(att):,} characters) — the goal objective this command loads</summary>\n")
        w(fence(att))
        w('\n</details>')
# goal objectives set or edited through the Codex goal interface (thread_goal_updated events).
# Objectives the agent set itself with its create_goal/update_goal tools do not emit these events.
GOAL_NOTE = {
    '2026-08-13 12:52': 'Set by the user through the goal interface (user\'s wording), turning the running session into an autonomous loop.',
    '2026-08-13 14:38': 'Same text as prompt A.18.',
    '2026-08-13 17:00': 'Set by the user through the goal interface (user\'s wording).',
    '2026-08-13 17:40': 'The user\'s edit of the previous objective: one sentence added about FAILED_PROOF_ATTEMPTS.md.',
    '2026-08-18 11:50': 'Same text as prompt A.36.',
    '2026-08-18 15:34': 'Objective restated with the open count updated (28 → 24). No agent goal-tool call precedes the change, so it was made through the goal interface; the wording follows the objective the agent drafted at 11:50.',
    '2026-08-18 22:02': 'Open count updated (24 → 22), as above.',
    '2026-08-19 13:29': 'Open count updated (22 → 21), as above.',
    '2026-09-21 17:02': 'Set by the user through the goal interface (user\'s wording).',
    '2026-09-21 17:04': 'The user\'s edit of the previous objective: the per-row resource limits (about 100 files, 16 GiB sequential, 1 hour) and the catalogue-update rule were added.',
}
w('\n\n# Goal objectives (G series)\n')
w('Codex `/goal` objectives drive autonomous multi-turn runs. The objectives below were set or changed through the Codex goal interface; they appear in the logs as `thread_goal_updated` events rather than as user messages, so they are listed separately. Objectives the agent set for itself with its own goal tools are omitted.\n')
gi = 0
for s in codex:
    last = None
    for ge in s['goal_events']:
        if ge['objective'] == last:
            continue
        last = ge['objective']
        gi += 1
        w(f"\n## G.{gi} — {ge['time']} · Codex goal · `{s['id'][:8]}` · {model_label(s)}\n")
        w(fence(ge['objective']))
        note = GOAL_NOTE.get(ge['time'][:16])
        if note:
            w(f'\n*Provenance:* {note}')
open(os.path.join(OUT, 'APPENDIX_A_USER_PROMPTS.md'), 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print('prompts', len(events), 'goals', gi)

# ------------------------------------------------ per-turn session log
out = []
w = out.append
w('# Appendix B — Session-by-session, turn-by-turn log\n')
w('Generated from the local Codex rollout files (`~/.codex/sessions/`), the Codex state databases '
  '(`~/.codex/state_5.sqlite`, `goals_1.sqlite`) and the Claude Code transcripts (`~/.claude/projects/…`). '
  'Times are KST. "Files" lists the files the agent created or edited in that turn through its patch/edit tool, with the '
  'number of patch operations; files written indirectly (by scripts the agent ran, e.g. generated Lean modules or the '
  'regenerated catalogue) are not captured here and appear only in git. "Report" is the opening of the agent\'s final '
  'message for the turn, truncated at 1,800 characters.\n')
for s in codex:
    rv = is_review(s)
    u = s['total_usage'] or {}
    w(f"\n## Codex session `{s['id']}`{' — approval reviewer' if rv else ''}\n")
    w(f"- Interface: {s.get('originator')} (Codex CLI {s['cli']}); approval policy `{s['approval']}`")
    w(f"- Model / reasoning effort: {model_label(s)}")
    w(f"- Wall clock: {s['start']} → {s['end']}")
    w(f"- Tokens: {u.get('total_tokens', 0):,} total ({u.get('cached_input_tokens', 0):,} cached input, "
      f"{u.get('output_tokens', 0):,} output, of which {u.get('reasoning_output_tokens', 0):,} reasoning); "
      f"context compactions: {s['compactions']}")
    tc = s['tool_calls']
    w(f"- Tool calls: {tc.get('shell_command', 0) + tc.get('exec_command', 0):,} shell, {tc.get('apply_patch', 0):,} patch, "
      f"{tc.get('web__run', 0)} web, {tc.get('update_plan', 0)} plan updates")
    if s['goal']:
        g = s['goal']
        w(f"- Codex goal (final state `{g['status']}`, {g['tokens_used']:,} tokens, {g['time_used_seconds'] / 3600:.1f} h): "
          f"{g['objective'][:600]}{'…' if len(g['objective']) > 600 else ''}")
    for ge in s['goal_events']:
        w(f"  - goal event {ge['time']}: {ge['status']} (tokens {ge['tokens']:,}, {ge['secs'] or 0} s)")
    if rv:
        w(f"- {len(s['turns'])} approval decisions:")
        for t in s['turns']:
            w(f"  - {t['start']}: `{(t.get('final') or '').strip()[:400]}`")
        continue
    for i, t in enumerate(s['turns']):
        h = hours(t['start'], t.get('end'))
        mdl = f"{t['model'][0]} / {t['model'][1]}" if t.get('model') else 'n/a'
        w(f"\n### Turn {i} — {t['start']} → {t.get('end') or '(no end record)'}"
          f"{f' ({h:.2f} h)' if h is not None else ''} · {mdl} · {t.get('status') or 'no completion record'}\n")
        pr = (t.get('prompt') or '').strip()
        w('Prompt: ' + (f'"{pr[:240]}{"…" if len(pr) > 240 else ""}"'.replace('\n', ' ') if pr else '*(none — autonomous `/goal` continuation)*'))
        if t['files']:
            w('\nFiles: ' + ', '.join(f'`{a}`×{b}' for a, b in t['files']))
        if t.get('final'):
            fin = t['final'].strip()
            w('\nReport:\n\n' + '\n'.join('> ' + l for l in (fin[:1800] + (' …' if len(fin) > 1800 else '')).splitlines()))
for s in claude_main:
    u = s['usage']
    w(f"\n## Claude Code session `{s['id']}`\n")
    w(f"- Interface: Claude Code {s['version']} (VS Code extension)")
    w(f"- Model: {', '.join(k for k in s['models'] if k != '<synthetic>')}; effort: "
      + ', '.join(f'{k} (×{v} messages)' for k, v in s['effort'].items()))
    w(f"- Wall clock: {s['start']} → {s['end']}")
    w(f"- Tokens: {u.get('output_tokens', 0):,} output; {u.get('cache_read_input_tokens', 0) + u.get('cache_creation_input_tokens', 0) + u.get('input_tokens', 0):,} input (incl. cache)")
    w(f"- Tool calls: " + ', '.join(f'{k} {v}' for k, v in sorted(s['tools'].items(), key=lambda x: -x[1])))
    for i, t in enumerate(s['turn_list']):
        h = hours(t['start'], t['end'])
        w(f"\n### Turn {i} — {t['start']} → {t['end']} ({h:.2f} h) · {', '.join(sorted(t['models']))}\n")
        pr = t['prompt'].strip()
        pr = re.sub(r'<ide_opened_file>.*?</ide_opened_file>\s*', '', pr, flags=re.S)
        w(f'Prompt: "{pr[:240]}{"…" if len(pr) > 240 else ""}"'.replace('\n', ' '))
        if t['subagents']:
            w('\nSubagents spawned (Claude Opus 5): ' + '; '.join(t['subagents']))
        if t['files']:
            w('\nFiles: ' + ', '.join(f'`{a}`×{b}' for a, b in t['files'].most_common()))
        if t['final']:
            fin = t['final'].strip()
            w('\nReport:\n\n' + '\n'.join('> ' + l for l in (fin[:1800] + (' …' if len(fin) > 1800 else '')).splitlines()))
open(os.path.join(OUT, 'APPENDIX_B_SESSION_LOG.md'), 'w', encoding='utf-8').write('\n'.join(out) + '\n')

# ------------------------------------------------ JSON index
idx = dict(timezone='Asia/Seoul (UTC+9)', generated='2026-09-23', sessions=[])
for s in codex:
    u = s['total_usage'] or {}
    idx['sessions'].append(dict(
        tool='Codex', role='approval-reviewer' if is_review(s) else 'worker', id=s['id'], interface=s.get('originator'),
        cli_version=s['cli'], models=s['models'], start=s['start'], end=s['end'], usage=u, compactions=s['compactions'],
        goal=s['goal'], goal_events=s['goal_events'], tool_calls=s['tool_calls'], files=s['files'],
        turns=[dict(start=t['start'], end=t.get('end'), status=t.get('status'), model=t.get('model'),
                    prompt=t.get('prompt'), files=t['files'], report=t.get('final')) for t in s['turns']],
        prompts=[] if is_review(s) else s['prompts']))
for s in claude_main:
    idx['sessions'].append(dict(
        tool='Claude Code', role='worker', id=s['id'], version=s['version'], models=s['models'], start=s['start'],
        end=s['end'], usage=s['usage'], tool_calls=s['tools'], files=s['files'],
        turns=[dict(start=t['start'], end=t['end'], models=dict(t['models']), prompt=t['prompt'],
                    files=dict(t['files']), subagents=t['subagents'], report=t['final']) for t in s['turn_list']]))
for s in data['claude']:
    if s['subagent']:
        idx['sessions'].append(dict(tool='Claude Code', role='subagent', id=s['id'], models=s['models'], effort=s['effort'],
                                    start=s['start'], end=s['end'], usage=s['usage'], tool_calls=s['tools'],
                                    task=s['prompts'][0]['text'] if s['prompts'] else None))
json.dump(idx, open(os.path.join(OUT, 'session_index.json'), 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
print('done')
