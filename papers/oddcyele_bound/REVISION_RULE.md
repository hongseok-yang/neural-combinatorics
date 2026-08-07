# Revision rules for `paper_new_region2_v2.tex`

Working rules stated by the author (TaeYoung Kim) during the August 2026 revision pass. These
are process rules, binding on whoever — human or AI — revises this manuscript. Companion files:
`REVISION_STYLE.md` (prose preferences), `TERMINOLOGY.md` (naming), `RENAMING.md` (label map).

The author reads the paper top to bottom, one passage at a time, and states what to change. The
rules below exist so that this reading is not invalidated by edits the author did not ask for.

## 1. No scripts on the manuscript

Do not use Python, `sed`, or any generated edit to change the text. It makes the author's audit
impossible. Reading and counting with scripts is fine; writing is not.

## 2. Change nothing that was not requested

If something in text the author has **already revised**, or is **revising right now**, looks
wrong or improvable, do not touch it. Describe it and wait for a decision. This is strict — it
is not satisfied by editing and reporting afterwards.

## 3. Material ahead of the reading point is exempt

Rule 2 covers revised and under-revision text only. Passages the author has not yet reached do
not need to be flagged; they will be covered when the reading gets there.

## 4. Never discard a revision because it contains an error

If the author's requested wording is factually wrong, do not fall back to the old text. Apply
the author's phrasing with the error corrected, and say which part was corrected and why.

## 5. Revision markers point backwards only

Mark revised passages only where they **precede** the author's current reading point; that is
what has to be re-checked. The passage under revision, and everything after it, will be read
anyway and needs no marker.

## 6. Pure moves get delimiters, not colour

Text that was relocated without rewording is delimited by begin/end markers, so the author does
not re-read already-approved prose. Colour is for text that was written or reworded.

## 7. Recompile after every edit

Run `pdflatex` twice and report errors, undefined references, duplicate labels, and overfull
boxes honestly. Equation and theorem numbers quoted in discussion come from the `.aux` file
(`\newlabel{key}{{number}{page}…}`), never from memory.

## 8. Banned words

Never **"record"**, **"display"**, or **"read"** (as in "read as", "reading it as", "read off").
The full list of rejected words is `REVISION_STYLE.md` §1 and still stands.
