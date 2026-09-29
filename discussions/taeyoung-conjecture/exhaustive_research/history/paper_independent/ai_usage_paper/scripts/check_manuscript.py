"""Static checks for the AI-usage companion manuscript."""

from __future__ import annotations

import re
from pathlib import Path


HERE = Path(__file__).resolve()
PAPER = HERE.parent.parent


BANNED = [
    "record",
    "display",
    "estimated",
    "read off",
    "recording",
    "budget",
    "limits of integration",
    "genuinely",
    "manifestly",
    "artificial",
    "decisive",
    "the bracket",
    "data",
    "structural facts",
    "principal chain",
    "defect",
]


def exact_word(text: str, word: str) -> bool:
    if " " in word:
        return word.lower() in text.lower()
    return re.search(rf"\b{re.escape(word)}\b", text, re.IGNORECASE) is not None


def main() -> None:
    manuscript = (PAPER / "main.tex").read_text(encoding="utf-8")
    metrics = (PAPER / "generated" / "metrics_macros.tex").read_text(encoding="utf-8")
    excerpts = (PAPER / "generated" / "excerpts.tex").read_text(encoding="utf-8")

    for word in BANNED:
        assert not exact_word(manuscript, word), f"banned manuscript term: {word}"
    assert re.search(r"\bagents?\b", manuscript, re.IGNORECASE) is None

    expected_macros = {
        "CatalogueRows": "117",
        "PositiveRows": "94",
        "NegativeRows": "23",
        "FailedRoutes": "65",
        "AtlasFortyThreeModules": "1,097",
    }
    for name, value in expected_macros.items():
        assert rf"\newcommand{{\{name}}}{{{value}}}" in metrics, (name, value)

    labels = re.findall(r"\\label\{ex:(B\d\d)\}", excerpts)
    assert labels == [
        "B11", "B12", "B21", "B22", "B23", "B31",
        "B32", "B33", "B34", "B35", "B36", "B41", "B42",
    ], labels
    assert "session 01a03722" in excerpts
    assert "session d19b441c" in excerpts
    assert "session 272ea172" in excerpts
    assert "session 01a0349f" in excerpts
    assert "CompanionMath2026" in manuscript

    print("AI-usage manuscript checks passed: five findings, 13 curated excerpts.")


if __name__ == "__main__":
    main()
