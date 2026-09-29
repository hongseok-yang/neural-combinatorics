"""Static checks for the generated mathematics manuscript."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "generated"

PROHIBITED = [
    r"\brecord(?:s|ed|ing)?\b",
    r"\bdisplay(?:s|ed|ing)?\b",
    r"\bestimated\b",
    r"\bread off\b",
    r"\bbudget\b",
    r"\blimits of integration\b",
    r"\bgenuinely\b",
    r"\bmanifestly\b",
    r"\bartificial\b",
    r"\bdecisive\b",
    r"\bthe bracket\b",
    r"\bdata\b",
    r"\bstructural facts\b",
    r"\bprincipal chain\b",
    r"\bdefects?\b",
    r"\bacts on\b",
]


def main() -> None:
    manuscript = (ROOT / "main.tex").read_text(encoding="utf-8")
    generated = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted(GENERATED.glob("*.tex"))
    )
    text = manuscript + "\n" + generated

    for pattern in PROHIBITED:
        match = re.search(pattern, text, flags=re.IGNORECASE)
        assert match is None, (pattern, match.group(0) if match else None)

    assert all(char in "\n\r\t" or ord(char) >= 32 for char in text)

    rows = json.loads((GENERATED / "classification.json").read_text(encoding="utf-8"))
    assert len(rows) == 117
    assert sum(row["status"] == "positive" for row in rows) == 94
    assert sum(row["status"] == "negative" for row in rows) == 23
    assert len({row["atlas"] for row in rows}) == 117

    witnesses = json.loads(
        (GENERATED / "negative_witnesses.json").read_text(encoding="utf-8")
    )
    assert len(witnesses) == 23
    assert {row["atlas"] for row in witnesses} == {
        row["atlas"] for row in rows if row["status"] == "negative"
    }

    log_path = ROOT / "main.log"
    if log_path.exists():
        log = log_path.read_text(encoding="utf-8", errors="replace")
        assert "undefined references" not in log
        assert "undefined citations" not in log
        assert "LaTeX Warning: Reference" not in log
        assert "LaTeX Warning: Citation" not in log

    print("manuscript checks passed: 117 rows, 94 positive, 23 negative")


if __name__ == "__main__":
    main()
