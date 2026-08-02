#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
strip_comments.py -- produce an anonymized copy of the Lean sources with every comment removed.

Motivation: comments can leak author identity, so for a double-blind peer-review release we strip
them from all `.lean` files.

What it removes (all Lean comment forms):
  * line comments        `-- ...` (to end of line)
  * block comments       `/- ... -/`  (properly NESTED)
  * doc comments         `/-- ... -/`
  * module doc comments  `/-! ... -/`

What it preserves:
  * String literals `"..."` (with `\\` escapes and multi-line string gaps) -- a `--` or `/-` inside
    a string is NOT a comment.
  * Character literals `'x'` and `'\\n'` -- so `'"'`, `'-'`, `'/'` never derail the scanner.
    (Primed identifiers such as `x'` are left untouched.)

By default it writes a stripped COPY of the whole package into a sibling directory, so the originals
are never modified. The build cache `.lake` and VCS/editor junk are skipped; non-`.lean` files are
copied verbatim. Blank lines left behind by removed comments are collapsed and line endings are
normalized to LF.

Usage (Windows):
  "C:\\Program Files\\Python39\\python.exe" strip_comments.py            # -> ..\\complete_lean_anon
  "C:\\Program Files\\Python39\\python.exe" strip_comments.py --out D:\\release\\OddCycleBound
  "C:\\Program Files\\Python39\\python.exe" strip_comments.py --selftest # run internal checks only

After running, review the NON-Lean files in the output (README.md, lakefile.toml, lean-toolchain,
*.ps1) by hand -- this tool only strips Lean comments.
"""

import argparse
import io
import os
import shutil
import sys
from pathlib import Path

# Directories never copied into the release.
SKIP_DIRS = {".lake", ".git", ".github", ".vscode", "__pycache__", ".idea"}


def strip_lean_comments(src: str) -> str:
    """Return `src` with all Lean comments removed, respecting string/char literals.

    A block comment is replaced by a single space so adjacent tokens stay separated
    (e.g. `a/-c-/b` -> `a b`); a line comment is dropped but its newline is kept.
    """
    out = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]

        # --- string literal ---------------------------------------------------
        if c == '"':
            out.append(c)
            i += 1
            while i < n:
                d = src[i]
                out.append(d)
                if d == "\\" and i + 1 < n:      # escape (incl. `\<newline>` string gap)
                    out.append(src[i + 1])
                    i += 2
                    continue
                i += 1
                if d == '"':                     # closing quote
                    break
            continue

        # --- character literal  'x'  or  '\n' ---------------------------------
        # Only treat `'` as a char literal when it clearly delimits one; otherwise it is
        # a prime in an identifier (e.g. `x'`) and is emitted as an ordinary character.
        if c == "'":
            if i + 1 < n and src[i + 1] == "\\":
                # escaped char literal: scan to the closing quote
                j = i + 2
                while j < n and src[j] != "'":
                    j += 2 if (src[j] == "\\" and j + 1 < n) else 1
                if j < n:
                    j += 1                       # include closing quote
                out.append(src[i:j])
                i = j
                continue
            if i + 2 < n and src[i + 2] == "'":  # simple char literal 'x'
                out.append(src[i:i + 3])
                i += 3
                continue
            # otherwise: a lone `'` (identifier prime) -- emit as normal
            out.append(c)
            i += 1
            continue

        # --- line comment  -- ... ---------------------------------------------
        if c == "-" and i + 1 < n and src[i + 1] == "-":
            j = i
            while j < n and src[j] != "\n":
                j += 1
            i = j                                 # keep the newline
            continue

        # --- block comment  /- ... -/  (nested) -------------------------------
        if c == "/" and i + 1 < n and src[i + 1] == "-":
            depth = 1
            i += 2
            while i < n and depth > 0:
                if src[i] == "/" and i + 1 < n and src[i + 1] == "-":
                    depth += 1
                    i += 2
                elif src[i] == "-" and i + 1 < n and src[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            out.append(" ")                       # keep token separation
            continue

        out.append(c)
        i += 1

    return "".join(out)


def tidy(text: str) -> str:
    """Normalize line endings to LF, drop trailing whitespace, collapse blank-line runs."""
    lines = [ln.rstrip() for ln in text.replace("\r\n", "\n").replace("\r", "\n").split("\n")]
    result = []
    prev_blank = False
    for ln in lines:
        if ln == "":
            if prev_blank:
                continue
            prev_blank = True
        else:
            prev_blank = False
        result.append(ln)
    while result and result[0] == "":
        result.pop(0)
    while result and result[-1] == "":
        result.pop()
    return "\n".join(result) + "\n"


def process_lean(text: str) -> str:
    return tidy(strip_lean_comments(text))


def run(root: Path, out: Path, inplace: bool) -> None:
    root = root.resolve()
    lean_count = 0
    copy_count = 0

    if inplace:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
            for fn in filenames:
                if fn.endswith(".lean"):
                    p = Path(dirpath) / fn
                    with io.open(p, "r", encoding="utf-8") as f:
                        text = f.read()
                    with io.open(p, "w", encoding="utf-8", newline="\n") as f:
                        f.write(process_lean(text))
                    lean_count += 1
        print("Stripped %d .lean files IN PLACE under %s" % (lean_count, root))
        return

    out = out.resolve()
    if out == root:
        sys.exit("error: --out must differ from the source root")
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [
            d for d in dirnames
            if d not in SKIP_DIRS and (Path(dirpath) / d).resolve() != out
        ]
        rel_dir = Path(dirpath).resolve().relative_to(root)
        (out / rel_dir).mkdir(parents=True, exist_ok=True)
        for fn in filenames:
            src_file = Path(dirpath) / fn
            dst_file = out / rel_dir / fn
            if fn.endswith(".lean"):
                with io.open(src_file, "r", encoding="utf-8") as f:
                    text = f.read()
                with io.open(dst_file, "w", encoding="utf-8", newline="\n") as f:
                    f.write(process_lean(text))
                lean_count += 1
            else:
                shutil.copy2(src_file, dst_file)
                copy_count += 1

    print("Wrote anonymized copy to: %s" % out)
    print("  .lean files stripped : %d" % lean_count)
    print("  other files copied   : %d" % copy_count)
    print("  (.lake build cache was skipped -- reviewers run `lake build` to fetch mathlib)")
    print("Reminder: review non-Lean files (README.md, lakefile.toml, *.ps1) for author info by hand.")


def selftest() -> None:
    S = strip_lean_comments
    # line comment removed, code kept, newline kept
    assert S("x := 5 -- author: Jane\ny := 6") == "x := 5 \ny := 6", S("x := 5 -- a\ny := 6")
    # block comment (nested) removed
    assert "secret" not in S("a /- outer /- secret -/ still -/ b")
    assert S("a /- c -/ b") == "a   b"
    # doc and module-doc comments removed
    assert "Jane" not in S("/-- by Jane -/\ndef f := 0")
    assert "Jane" not in S("/-! module by Jane -/\nimport X")
    # string literals preserved (comment markers inside are NOT comments)
    assert S('s := "-- not a comment"') == 's := "-- not a comment"'
    assert S('s := "/- keep -/"') == 's := "/- keep -/"'
    assert S('s := "a \\" -- still string"') == 's := "a \\" -- still string"'
    # char literal containing a quote must not start a string
    assert S("c := '\"' -- x") == "c := '\"' "
    assert S("c := '-' -- x") == "c := '-' "
    # primed identifiers untouched
    assert S("theorem h' : p := h'") == "theorem h' : p := h'"
    # full pipeline: a leading module doc + blank runs collapse to clean code
    assert process_lean("/-! doc -/\n\n\nimport X\n") == "import X\n"
    assert tidy("a\n\n\n\nb\n") == "a\n\nb\n"
    print("selftest: all checks passed.")


def main() -> None:
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description="Strip all comments from Lean sources for anonymized release.")
    ap.add_argument("--root", type=Path, default=here,
                    help="package root to process (default: this script's directory)")
    ap.add_argument("--out", type=Path, default=None,
                    help="output directory for the stripped copy (default: <root>_anon sibling)")
    ap.add_argument("--inplace", action="store_true",
                    help="DANGER: overwrite the .lean files in place instead of writing a copy")
    ap.add_argument("--selftest", action="store_true", help="run internal self-tests and exit")
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    root = args.root.resolve()
    out = args.out.resolve() if args.out is not None else root.parent / (root.name + "_anon")
    run(root, out, args.inplace)


if __name__ == "__main__":
    main()
