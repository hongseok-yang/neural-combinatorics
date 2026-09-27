#!/usr/bin/env python3
"""Extract the files embedded in even_apex_blueprint.tex via filecontents* blocks.

Usage:  python tools/extract_embedded.py even_apex_blueprint.tex certificates

Writes mean_two_sos.json, mean_three_sos.json, negative_majority_sos.json,
positive_majority_sos.json, verify_six_vertex.py, verify_algebra.py, independent_audit.py and
run_verification.sh into the target directory.  Only the standard library is used; no TeX is run.
Tested with Python 3.9 on 2026-09-27 (the four JSON files and three scripts extract byte-exactly;
`independent_audit.py --certificates . --export lean-data` then passes in about 30 s).
"""
import pathlib
import sys

BS = chr(92)  # backslash, spelled out so the source survives shells that eat escapes
BEGIN = BS + 'begin{filecontents*}'
END = BS + 'end{filecontents*}'


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    src = pathlib.Path(sys.argv[1]).read_text(encoding='utf-8')
    out = pathlib.Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    pos = 0
    count = 0
    while True:
        i = src.find(BEGIN, pos)
        if i < 0:
            break
        j = i + len(BEGIN)
        if src[j] == '[':                      # optional [overwrite]
            j = src.find(']', j) + 1
        assert src[j] == '{', 'malformed filecontents header'
        k = src.find('}', j)
        name = src[j + 1:k]
        body_start = src.find(chr(10), k) + 1
        e = src.find(END, body_start)
        assert e > 0, 'unterminated filecontents block'
        # newline='' keeps LF line endings on Windows, so the files match the embedded bytes.
        with open(out / name, 'w', encoding='utf-8', newline='') as fh:
            fh.write(src[body_start:e])
        print(f'{name}: {e - body_start} bytes')
        count += 1
        pos = e + len(END)
    print(f'{count} embedded files written to {out}')


if __name__ == '__main__':
    main()
