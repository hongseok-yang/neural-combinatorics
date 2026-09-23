"""Extract a structured history of Codex and Claude Code sessions for exhaustive_research."""
import json, glob, os, re, sys, sqlite3, collections
from datetime import datetime, timezone, timedelta

sys.stdout.reconfigure(encoding='utf-8')
KST = timezone(timedelta(hours=9))
HOME = os.environ.get('HISTORY_LOG_ROOT') or os.path.expanduser('~')  # set HISTORY_LOG_ROOT to read a backup tree
OUT = os.path.dirname(os.path.abspath(__file__))
ROOT_MARK = 'exhaustive_research'


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
    return p[i + len(ROOT_MARK) + 1:] if i >= 0 else p


# ---------------------------------------------------------------- Codex
def codex_sessions():
    st = sqlite3.connect(f'file:{HOME}/.codex/state_5.sqlite?mode=ro', uri=True)
    cols = [r[1] for r in st.execute('pragma table_info(threads)')]
    threads = {r[0]: dict(zip(cols, r)) for r in st.execute('select * from threads')}
    gl = sqlite3.connect(f'file:{HOME}/.codex/goals_1.sqlite?mode=ro', uri=True)
    gcols = [r[1] for r in gl.execute('pragma table_info(thread_goals)')]
    goals = {r[0]: dict(zip(gcols, r)) for r in gl.execute('select * from thread_goals')}
    out = []
    for f in sorted(glob.glob(f'{HOME}/.codex/sessions/2026/*/*/*.jsonl')):
        sid = f[-42:-6]
        th = threads.get(sid, {})
        with open(f, encoding='utf-8') as fh:
            first = fh.readline()
        if ROOT_MARK not in first and ROOT_MARK not in (th.get('cwd') or ''):
            continue
        s = dict(tool='Codex', id=sid, file=f, size=os.path.getsize(f), title=th.get('title'),
                 source=th.get('source'), cli=th.get('cli_version'), git_sha=th.get('git_sha'),
                 approval=th.get('approval_mode'), db_model=th.get('model'), db_effort=th.get('reasoning_effort'),
                 db_tokens=th.get('tokens_used'), goal=goals.get(sid), turns=[], prompts=[], goal_events=[],
                 models=collections.Counter(), files=collections.Counter(), file_ops=collections.Counter(),
                 compactions=0, tool_calls=collections.Counter(), commands=[], web=[])
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
                turn_models[p.get('turn_id')] = (p.get('model'), p.get('effort') or p.get('reasoning_effort'))
                s['models'][(p.get('model'), p.get('effort') or p.get('reasoning_effort'))] += 1
            elif t == 'compacted':
                s['compactions'] += 1
            elif t == 'event_msg':
                pt = p.get('type')
                if pt == 'task_started':
                    cur = dict(turn_id=p.get('turn_id'), start=kst(ts), files=collections.Counter(), prompt=None)
                    s['turns'].append(cur)
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
        for tt in s['turns']:
            tt['files'] = tt['files'].most_common()
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
    base = f'{HOME}/.claude/projects/c--Users-mekty-neural-combinatorics-discussions-taeyoung-conjecture-exhaustive-research'
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
                    if '<command-name>' in txt:
                        s['prompts'].append(dict(time=kst(ts), text=re.sub(r'\s+', ' ', txt)[:400], kind='slash'))
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
                        if c['name'] in ('Bash', 'PowerShell'):
                            cmd = inp.get('command', '')
                            if re.search(r'lake|lean|verify_lean|git commit|pdflatex|latexmk', cmd):
                                s['commands'].append((kst(ts), cmd[:300]))
                        if c['name'] == 'Agent':
                            s['prompts'].append(dict(time=kst(ts), kind='subagent-spawn',
                                                     text=f"[{inp.get('description')}] " + inp.get('prompt', '')[:1500]))
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
        print(s['start'], s['end'], s['id'], s['title'], s['models'], len(s['prompts']), 'turns', len(s['turns']),
              'files', len(s['files']), 'tok', (s['total_usage'] or {}).get('total_tokens'), 'db', s['db_tokens'])
    for s in cl:
        print(s.get('start'), s.get('end'), s['id'], s['subagent'], s['models'], 'prompts',
              sum(1 for p in s['prompts'] if p['kind'] == 'user'), 'files', len(s['files']), s['usage'])
