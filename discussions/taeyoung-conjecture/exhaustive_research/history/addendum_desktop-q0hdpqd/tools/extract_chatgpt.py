"""Extract the relevant ChatGPT Pro conversations from the account export
(the zip the author placed in the project root on 2026-09-27; conversations-*.json shards)
and write ADDENDUM_CHATGPT.md (E-series verbatim prompts + per-conversation record)
and chatgpt_sessions.json.

Point CHATGPT_EXPORT_ROOT at the extracted export tree (default: the scratchpad copy).
Conversation selection is explicit (ids below), decided by reading the export:
- CAMPAIGN: conversations that worked on the 117-graph classification in the gap window;
- SATELLITE: same-window conversations serving the campaign indirectly or adjacent threads;
- PREHISTORY: earlier conversations behind the campaign's input documents (one line each).
"""
import json, glob, os, sys
from datetime import datetime, timezone, timedelta

sys.stdout.reconfigure(encoding='utf-8')
KST = timezone(timedelta(hours=9))
D = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(D)
os.makedirs(OUT, exist_ok=True)
ROOT = os.environ.get('CHATGPT_EXPORT_ROOT') or (
    r'C:\Users\mekje\AppData\Local\Temp\claude'
    r'\c--Users-mekje-KAIST-CS-neural-combinatorics-discussions-taeyoung-conjecture-exhaustive-research'
    r'\01f2d234-3490-45e5-8c83-5b51ff20798a\scratchpad\chatgpt_export')

CAMPAIGN = {
    '6a83c384': 'Blekherman–Raymond entropy proof of t(P5)^3 >= t(P3)^5 written out in LaTeX (Atlas 102 reference)',
    '6a856564': 'PRODUCED notes/chordal_entropy_extension.tex (monotone-exponent + PAVA entropy theorem)',
    '6a85a514': '21-instance research brief (in the form of an agent-drafted prompt); no resolution',
    '6a8628e3': 'three-instance brief (Atlas 130 bridge-triangles, K4 pages, house); run ended without a final answer',
    '6a871354': 'the house-graph (Atlas 43) proving thread, 20-23 Aug; partial intervals only',
    '6a8961a4': 'branch of the house thread; PRODUCED notes/house_partial.tex (p >= (1+1/sqrt3)/2 write-up)',
    '6a8aaa3d': 'edge-robustness audit of the chordal-entropy theorem (GLLV comparison); insert not kept',
    '6a8ab440': 'count of catalogue rows covered by the chordal-entropy theorem (30, or 29 connected)',
    '6a8afa8c': 'the Codex-drafted CHORDAL_OPEN_CASES brief with 4 PDF attachments (Atlas 181/157/130); no closure',
}
SATELLITE = {
    '6a8420b0': 'odd-cycle paper: proof region-splitting question (related work)',
    '6a8697f6': 'large-deviation rate-function flag-algebra formulation (separate thread)',
    '6a8aa259': 'common-graphs literature status (with a self-correction on "odd girth")',
    '6a8ab684': 'extremal Ramsey graphs lookup (adjacent)',
    '6a8c6dfb': 'neural-extremal research prospectus, 22->26 pages (new-directions thread, night of the /goal run)',
    '6a8d6696': 'flag-algebra encoding of partially integrated Sidorenko objects (C5/Moebius thread)',
    '6a8e68cc': 'path-Sidorenko (Blakley-Roy) citation check (C5 thread)',
}
PREHISTORY = [
    ('6a1d1004', 'Graph Conjecture Proof Request'), ('6a1e0305', 'Graph Inequality Conjecture'),
    ('6a212973', 'Turan graph non-optimality'), ('6a263152', 'Inequality on Homomorphism Density'),
    ('6a26317d', 'Inequality on Homomorphism Density'), ('6a28a58d', 'Relaxing Proof Constraints'),
    ('6a2a36d7', 'Graph Homomorphism Conjecture'), ('6a2fb3c6', 'Graph Inequality Conjecture'),
    ('6a43eec7', 'Research Direction for Homomorphism'), ('6a46a2fc', 'Graph Conjecture Operations'),
    ('6a51de48', 'Graph Homomorphism Inequality'), ('6a58d671', 'Human Verifiable Proof'),
    ('6a60e66f', 'Universal proof for odd cycles'), ('6a62426a', 'Chordal Graph Proof'),
    ('6a674743', 'Lower Bound Chordal Graph Edges'), ('6a68c4d5', 'Chordal Graph Naming'),
    ('6a6b9ee2', 'Unproven Conjecture in Graph Theory'), ('6a795e31', 'Branch - Upper Bound Gap Analysis'),
    ('6a7c38c7', 'Graph Bounds and Relaxation'), ('6a7d5b2a', 'Branch - Graph Bounds and Relaxation'),
    ('6a7c89c3', "Fisher's theorem and generalization"),
]
PRE_IDS = {i for i, _ in PREHISTORY}


def kst(ts):
    return datetime.fromtimestamp(ts, KST).strftime('%Y-%m-%d %H:%M:%S') if ts else '?'


def texts(m):
    c = m.get('content') or {}
    out = []
    for p in c.get('parts') or []:
        out.append(p if isinstance(p, str) else json.dumps(p, ensure_ascii=False))
    if c.get('text'):
        out.append(c['text'])
    return '\n'.join(out), c.get('content_type')


def chain_of(conv):
    mp = conv.get('mapping') or {}
    chain = []
    node = conv.get('current_node')
    while node:
        n = mp.get(node)
        if not n:
            break
        if n.get('message'):
            chain.append(n['message'])
        node = n.get('parent')
    chain.reverse()
    return chain


convs = {}
for f in sorted(glob.glob(os.path.join(ROOT, 'conversations-*.json'))):
    for conv in json.load(open(f, encoding='utf-8')):
        cid = (conv.get('conversation_id') or '')[:8]
        if cid in CAMPAIGN or cid in SATELLITE or cid in PRE_IDS:
            convs[cid] = conv

records = []
for cid in sorted(set(CAMPAIGN) | set(SATELLITE), key=lambda c: convs[c].get('create_time') or 0):
    conv = convs[cid]
    chain = chain_of(conv)
    models, prompts, finals, downloads, messages = {}, [], [], [], []
    for m in chain:
        role = (m.get('author') or {}).get('role')
        slug = (m.get('metadata') or {}).get('model_slug')
        if slug:
            models[slug] = models.get(slug, 0) + 1
        txt, ctype = texts(m)
        atts = [a.get('name', '?') for a in (m.get('metadata') or {}).get('attachments') or []]
        if role == 'user' and (txt.strip() or atts):
            prompts.append(dict(time=kst(m.get('create_time')), text=txt, attachments=atts))
            messages.append(dict(time=kst(m.get('create_time')), role='user', text=txt, attachments=atts))
        elif role == 'assistant' and ctype == 'text' and txt.strip():
            finals.append(dict(time=kst(m.get('create_time')), model=slug, chars=len(txt)))
            messages.append(dict(time=kst(m.get('create_time')), role='assistant', model=slug, text=txt))
            for line in txt.splitlines():
                if 'sandbox:/' in line:
                    downloads.append(line.strip()[:200])
    records.append(dict(
        id=conv.get('conversation_id'), title=conv.get('title'),
        role='campaign' if cid in CAMPAIGN else 'satellite',
        note=(CAMPAIGN.get(cid) or SATELLITE.get(cid)),
        start=kst(conv.get('create_time')), last=kst(conv.get('update_time')),
        models=models, n_messages=len(chain), prompts=prompts,
        assistant_text_messages=finals, sandbox_downloads=downloads,
        messages=messages if cid in CAMPAIGN else None))

json.dump(dict(source='ChatGPT account export of 2026-09-23 (zip in the project root)',
               timezone='Asia/Seoul (UTC+9)', conversations=records,
               prehistory=[dict(id=i, title=t, start=kst(convs[i].get('create_time')),
                                last=kst(convs[i].get('update_time'))) for i, t in PREHISTORY if i in convs]),
          open(os.path.join(D, 'chatgpt_sessions.json'), 'w', encoding='utf-8'), ensure_ascii=False, indent=1)


def fence(text):
    n = 3
    while '`' * n in text:
        n += 1
    return '`' * n + 'text\n' + text.rstrip() + '\n' + '`' * n


NOTES = {
    ('6a85a514', 0): 'A brief in the form of an agent-drafted prompt ("# Prompt for ChatGPT Pro: resolve one open '
        'case…", 21 instances, 18,497 characters). Its content — the exhausted tensor searches, the L-infinity '
        'stability radii, the 10^-6..10^-12 high-density radii — is the campaign state as of 19 Aug. The session that '
        'drafted it is in neither machine\'s surviving logs: this device has no session at that time, and the '
        'workstation Codex logs never mention ChatGPT (the deleted Claude Code sessions remain possible). Pasted by '
        'the user.',
    ('6a8628e3', 0): 'A second brief of the same form (three instances: Atlas 130, a K4-with-pages graph, the '
        'house), with the same untraced provenance as the brief above.',
    ('6a8961a4', 0): 'Branch point: the conversation is forked from the house thread after the 21 Aug 23:51 partial '
        'result; the earlier prompts are replayed from the parent and not repeated here.',
    ('6a8afa8c', 0): 'This is `CHORDAL_OPEN_CASES_RESEARCH_BRIEF.md`, drafted by Codex in session `01a02ea5` turn 1 '
        '(23 Aug 22:13–22:31, prompt D.77) together with its `chatgpt_pro_attachments/`; the user pasted it 19 minutes '
        'after the Codex turn finished, attaching the four PDFs the brief prescribes.',
}

out = []
w = out.append
w('# Addendum Appendix E — ChatGPT Pro conversations (from the account export)\n')
w('The author\'s ChatGPT account export (zip of 2026-09-23, placed in the project root on 2026-09-27) contains 1,068 '
  'conversations back to May 2024. The conversations below are the ones relevant to `exhaustive_research/` in the '
  '2026-08-18…26 window ("campaign" and "satellite"), followed by the earlier conversations behind the campaign\'s '
  'input documents ("prehistory"). Times are KST. Model names are the export\'s `model_slug` values, verbatim '
  '(`gpt-5-6-pro`, `gpt-5-6-thinking`, `gpt-5.6-sol-wm`). User prompts are reproduced byte-for-byte. Assistant '
  'progress/thought entries are counted but not reproduced; files the assistant delivered as sandbox downloads are '
  'listed by link line. The full raw record is in the export zip (kept in the raw-data backup).\n')
ei = 0
seen = set()
for r in records:
    w(f"\n## Conversation `{r['id'][:8]}` — \u201c{r['title']}\u201d ({r['role']})\n")
    w(f"- {r['start']} → {r['last']}; models: " + ', '.join(f'{k}×{v}' for k, v in r['models'].items())
      + f"; {r['n_messages']} messages on the final path")
    w(f"- {r['note']}")
    for dl in r['sandbox_downloads']:
        w(f"- Delivered file: `{dl}`")
    j = 0
    skipped = 0
    for p in r['prompts']:
        key = p['text'].strip()
        if key and key in seen:  # a branched conversation replays its parent's prompts
            skipped += 1
            continue
        seen.add(key)
        ei += 1
        att = (' · attachments: ' + ', '.join(p['attachments'])) if p['attachments'] else ''
        w(f"\n### E.{ei} — {p['time']} · `{r['id'][:8]}`{att}\n")
        w(fence(p['text']) if p['text'].strip() else '*(attachment-only message)*')
        note = NOTES.get((r['id'][:8], j))
        if note:
            w(f'\n*Note:* {note}')
        j += 1
    if skipped:
        w(f"\n*({skipped} earlier prompt(s) replayed from the parent conversation are listed there.)*")
w('\n\n# Prehistory (before 2026-08-18, one line each)\n')
w('These conversations precede the gap window; they are listed to locate the origin of the campaign\'s input '
  'documents and standing methods. They are not part of the addendum\'s session tables.\n')
for i, t in PREHISTORY:
    if i in convs:
        c = convs[i]
        w(f"- `{i}` — \u201c{c.get('title')}\u201d, {kst(c.get('create_time'))[:16]} → {kst(c.get('update_time'))[:16]}")
open(os.path.join(OUT, 'ADDENDUM_CHATGPT.md'), 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print('conversations', len(records), 'prompts', ei, 'prehistory', sum(1 for i, _ in PREHISTORY if i in convs))
