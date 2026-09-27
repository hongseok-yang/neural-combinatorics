"""Extract a structured history of the Codex and Claude Code sessions on DESKTOP-Q0HDPQD
(the author's second device) that concern discussions/taeyoung-conjecture/exhaustive_research
or papers/oddcycle_bound, for the 2026-08-19..27 addendum.

Adapted from history/tools/extract.py (same output structure). Differences:
- relevance is decided by the session's cwd: `taeyoung-conjecture/exhaustive_research`
  -> role "primary"; `papers/oddcycle_bound` -> role "related"; any other
  `taeyoung-conjecture` path -> role "flagged" (out-of-window prehistory);
- forked sessions replay the parent's history at the fork instant; turns whose
  start..end span is under 2 s are marked `replayed`;
- the ordered `turn_context` stream (time, model, effort) is kept, because the
  reasoning-effort changes are a subject of the addendum;
- Claude Code transcripts of this device's exhaustive-research project are read the
  same way as in the original script (only the addendum-writing session survives).
"""
import json, glob, os, re, sys, sqlite3, collections
from datetime import datetime, timezone, timedelta

sys.stdout.reconfigure(encoding='utf-8')
KST = timezone(timedelta(hours=9))
HOME = os.environ.get('HISTORY_LOG_ROOT') or os.path.expanduser('~')
OUT = os.path.dirname(os.path.abspath(__file__))
ROOT_MARK = 'exhaustive_research'
THIS_SESSION = '01f2d234-3490-45e5-8c83-5b51ff20798a'  # the session writing this addendum


def kst(ts):
    if ts is None:
        return None
    if isinstance(ts, (int, float)):
        if ts > 1e12:
            ts /= 1000
        return datetime.fromtimestamp(ts, KST).strftime('%Y-%m-%d %H:%M:%S')
    return datetime.fromisoformat(ts.replace('Z', '+00:00')).astimezone(KST).strftime('%Y-%m-%d %H:%M:%S')


def rel(p):
    p = p.replace('\\', '/')
    if '/AppData/Local/Temp/claude/' in p:
        return '(agent scratchpad)/' + p.rsplit('/', 1)[-1]
    if '/.claude/projects/' in p and '/memory/' in p:
        return '(Claude memory)/' + p.rsplit('/', 1)[-1]
    i = p.find(ROOT_MARK + '/')
    if i >= 0:
        return p[i + len(ROOT_MARK) + 1:]
    i = p.find('neural-combinatorics/')
    return p[i + len('neural-combinatorics/'):] if i >= 0 else p


def role_of(cwd):
    n = (cwd or '').lower().replace('\\', '/')
    if 'taeyoung-conjecture/exhaustive_research' in n:
        return 'primary'
    if 'oddcycle_bound' in n:
        return 'related'
    if 'taeyoung-conjecture' in n:
        return 'flagged'
    return None


# ---------------------------------------------------------------- Codex
def codex_sessions():
    st = sqlite3.connect(f'file:{HOME}/.codex/state_5.sqlite?mode=ro', uri=True)
    cols = [r[1] for r in st.execute('pragma table_info(threads)')]
    threads = {r[0]: dict(zip(cols, r)) for r in st.execute('select * from threads')}
    goals = {}
    try:
        gl = sqlite3.connect(f'file:{HOME}/.codex/goals_1.sqlite?mode=ro', uri=True)
        gcols = [r[1] for r in gl.execute('pragma table_info(thread_goals)')]
        goals = {r[0]: dict(zip(gcols, r)) for r in gl.execute('select * from thread_goals')}
    except Exception:
        pass
    out = []
    for f in sorted(glob.glob(f'{HOME}/.codex/sessions/2026/*/*/*.jsonl')):
        sid = f[-42:-6]
        th = threads.get(sid, {})
        with open(f, encoding='utf-8') as fh:
            first = json.loads(fh.readline())
        cwd0 = (first.get('payload') or {}).get('cwd') or th.get('cwd') or ''
        role = role_of(cwd0)
        if role is None:
            continue
        s = dict(tool='Codex', id=sid, file=f, size=os.path.getsize(f), role=role, title=th.get('title'),
                 source=th.get('source'), cli=th.get('cli_version'), git_sha=th.get('git_sha'),
                 approval=th.get('approval_mode'), db_model=th.get('model'), db_effort=th.get('reasoning_effort'),
                 db_tokens=th.get('tokens_used'), goal=goals.get(sid), turns=[], prompts=[], goal_events=[],
                 models=collections.Counter(), files=collections.Counter(), file_ops=collections.Counter(),
                 compactions=0, tool_calls=collections.Counter(), commands=[], web=[], turn_contexts=[])
        cur = None
        seen_changes = set()
        last_total = None
        turn_models = {}
        for line in open(f, encoding='utf-8'):
            d = json.loads(line)
            t = d['type']; p = d.get('payload') or {}
            ts = d.get('timestamp')
            if t == 'session_meta':
                if 'start' in s:
                    continue
                s['start'] = kst(p.get('timestamp') or ts)
                s['cwd'] = p.get('cwd'); s['originator'] = p.get('originator')
            elif t == 'turn_context':
                eff = p.get('effort') or p.get('reasoning_effort')
                turn_models[p.get('turn_id')] = (p.get('model'), eff)
                s['models'][(p.get('model'), eff)] += 1
                s['turn_contexts'].append(dict(time=kst(ts), model=p.get('model'), effort=eff))
            elif t == 'compacted':
                s['compactions'] += 1
            elif t == 'event_msg':
                pt = p.get('type')
                if pt == 'task_started':
                    cur = dict(turn_id=p.get('turn_id'), start=kst(ts), files=collections.Counter(), prompt=None,
                               commentary=[])
                    s['turns'].append(cur)
                elif pt == 'agent_message':
                    # visible progress messages; the model's reasoning itself is encrypted and not stored in the clear
                    if cur is not None and p.get('message'):
                        cur['commentary'].append(dict(time=kst(ts), text=p['message']))
                elif pt == 'task_complete' or pt == 'turn_aborted':
                    tgt = cur
                    for tt in reversed(s['turns']):
                        if tt['turn_id'] == p.get('turn_id'):
                            tgt = tt; break
                    if tgt is not None:
                        tgt['end'] = kst(ts)
                        tgt['status'] = 'aborted:' + str(p.get('reason')) if pt == 'turn_aborted' else 'complete'
                        tgt['final'] = p.get('last_agent_message')
                        tgt['model'] = turn_models.get(tgt['turn_id'])
                elif pt == 'item_completed':
                    it = p.get('item', {})
                    if it.get('type') == 'UserMessage':
                        txt = '\n'.join(c.get('text', '') for c in it.get('content', []) if c.get('type') == 'text')
                        imgs = sum(1 for c in it.get('content', []) if c.get('type') != 'text')
                        pr = dict(time=kst(ts), text=txt, attachments=imgs, turn_id=p.get('turn_id'))
                        s['prompts'].append(pr)
                        if cur is not None and cur.get('prompt') is None and cur['turn_id'] == p.get('turn_id'):
                            cur['prompt'] = txt
                    elif it.get('type') == 'FileChange' and it.get('id') not in seen_changes:
                        seen_changes.add(it.get('id'))
                        for path, ch in (it.get('changes') or {}).items():
                            r = rel(path)
                            s['files'][r] += 1
                            s['file_ops'][(r, ch.get('type'))] += 1
                            if cur is not None:
                                cur['files'][r] += 1
                    elif it.get('type') == 'WebSearch':
                        s['web'].append(json.dumps(it, ensure_ascii=False)[:300])
                elif pt == 'thread_goal_updated':
                    g = p.get('goal', {})
                    s['goal_events'].append(dict(time=kst(ts), status=g.get('status'), objective=g.get('objective'),
                                                 tokens=g.get('tokensUsed'), secs=g.get('timeUsedSeconds')))
                elif pt == 'token_count':
                    info = p.get('info') or {}
                    if info.get('total_token_usage'):
                        last_total = info['total_token_usage']
                elif pt == 'user_message':
                    txt = p.get('message', '')
                    if not any(pr['text'].strip() == txt.strip() and pr['time'][:16] == kst(ts)[:16] for pr in s['prompts']):
                        s['prompts'].append(dict(time=kst(ts), text=txt, attachments=len(p.get('images') or []) + len(p.get('local_images') or []), turn_id=None))
                        if cur is not None and cur.get('prompt') is None:
                            cur['prompt'] = txt
                elif pt == 'patch_apply_end' and p.get('call_id') not in seen_changes:
                    seen_changes.add(p.get('call_id'))
                    for path, ch in (p.get('changes') or {}).items():
                        r = rel(path)
                        s['files'][r] += 1
                        s['file_ops'][(r, ch.get('type'))] += 1
                        if cur is not None:
                            cur['files'][r] += 1
            elif t == 'response_item':
                pt = p.get('type')
                if pt == 'custom_tool_call':
                    inp = p.get('input', '')
                    for m in re.findall(r'tools\.(\w+)', inp):
                        s['tool_calls'][m] += 1
                    for m in re.findall(r'command\s*:\s*"((?:[^"\\]|\\.)*)"', inp):
                        if re.search(r'lake|lean|verify_lean|python|pdflatex|latexmk|git ', m):
                            s['commands'].append((kst(ts), m[:300]))
                elif pt == 'function_call':
                    s['tool_calls']['fn:' + p.get('name', '')] += 1
            s['end'] = kst(ts)
        s['total_usage'] = last_total
        s['models'] = [f'{m} / effort={e} (x{n} turn contexts)' for (m, e), n in s['models'].items()]
        s['files'] = s['files'].most_common()
        s['file_ops'] = sorted(f'{k[1]}:{k[0]}' for k in s['file_ops'])
        fmt = '%Y-%m-%d %H:%M:%S'
        for tt in s['turns']:
            tt['files'] = tt['files'].most_common()
            if tt.get('end'):
                span = (datetime.strptime(tt['end'], fmt) - datetime.strptime(tt['start'], fmt)).total_seconds()
                tt['replayed'] = span < 2 and bool(tt.get('final'))
        s['tool_calls'] = dict(s['tool_calls'])
        out.append(s)
    return out


# ---------------------------------------------------------------- Claude
NOISE = ('<task-notification>', 'Another Claude session sent a message', '<local-command', '<command-name>',
         '<system-reminder>', 'Caveat:', '[Request interrupted')


def claude_text(content):
    if isinstance(content, str):
        return content, False
    parts, tool_result = [], False
    for c in content:
        if c.get('type') == 'text':
            parts.append(c['text'])
        elif c.get('type') == 'tool_result':
            tool_result = True
        elif c.get('type') == 'image':
            parts.append('[image attached]')
    return '\n'.join(parts), tool_result


def claude_sessions():
    base = f'{HOME}/.claude/projects/c--Users-mekje-KAIST-CS-neural-combinatorics-discussions-taeyoung-conjecture-exhaustive-research'
    out = []
    for f in sorted(glob.glob(base + '/*.jsonl')) + sorted(glob.glob(base + '/*/subagents/*.jsonl')):
        s = dict(tool='Claude Code', id=os.path.basename(f)[:-6], file=f, size=os.path.getsize(f),
                 subagent='subagents' in f, prompts=[], notifications=0, models=collections.Counter(),
                 files=collections.Counter(), tools=collections.Counter(), commands=[], finals=[], usage=collections.Counter(),
                 titles=[], version=None, effort=collections.Counter())
        last_text = None
        for line in open(f, encoding='utf-8'):
            try:
                d = json.loads(line)
            except Exception:
                continue
            ts = d.get('timestamp')
            if ts:
                s.setdefault('start', kst(ts)); s['end'] = kst(ts)
            t = d.get('type')
            if d.get('version'):
                s['version'] = d['version']
            if t == 'ai-title':
                s['titles'].append(d.get('aiTitle') or d.get('title'))
            if t == 'user':
                if d.get('isMeta') or d.get('isCompactSummary'):
                    continue
                txt, tr = claude_text(d['message'].get('content'))
                if tr or not txt.strip():
                    continue
                if txt.startswith(NOISE):
                    s['notifications'] += 1
                    continue
                if last_text:
                    s['finals'].append(dict(time=last_text[0], text=last_text[1]))
                    last_text = None
                s['prompts'].append(dict(time=kst(ts), text=txt, kind='user'))
            elif t == 'assistant':
                m = d['message']
                s['models'][m.get('model')] += 1
                if m.get('model') != '<synthetic>':
                    s['effort'][d.get('effort')] += 1
                u = m.get('usage') or {}
                for k in ('input_tokens', 'output_tokens', 'cache_read_input_tokens', 'cache_creation_input_tokens'):
                    s['usage'][k] += u.get(k) or 0
                for c in m.get('content', []):
                    if c.get('type') == 'tool_use':
                        s['tools'][c['name']] += 1
                        inp = c.get('input', {})
                        if c['name'] in ('Edit', 'Write', 'NotebookEdit', 'MultiEdit'):
                            s['files'][rel(inp.get('file_path', '?'))] += 1
                    elif c.get('type') == 'text' and c['text'].strip():
                        last_text = (kst(ts), c['text'])
        if last_text:
            s['finals'].append(dict(time=last_text[0], text=last_text[1]))
        s['models'] = dict(s['models']); s['files'] = s['files'].most_common(); s['tools'] = dict(s['tools'])
        s['usage'] = dict(s['usage']); s['effort'] = dict(s['effort'])
        out.append(s)
    return out


if __name__ == '__main__':
    cx = codex_sessions()
    cl = claude_sessions()
    with open(os.path.join(OUT, 'sessions.json'), 'w', encoding='utf-8') as fh:
        json.dump(dict(codex=cx, claude=cl), fh, ensure_ascii=False, indent=1, default=str)
    for s in cx:
        print(s['start'], s['end'], s['id'][:8], s['role'], s['title'][:40] if s['title'] else None,
              s['models'], len(s['prompts']), 'turns', len(s['turns']),
              'replayed', sum(1 for t in s['turns'] if t.get('replayed')),
              'tok', (s['total_usage'] or {}).get('total_tokens'), 'db', s['db_tokens'])
    for s in cl:
        print(s.get('start'), s.get('end'), s['id'][:8], 'subagent' if s['subagent'] else 'main', s['models'],
              'prompts', sum(1 for p in s['prompts'] if p['kind'] == 'user'), s['usage'])
