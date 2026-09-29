"""Generate the curated verbatim-excerpt appendix from the session indexes."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve()
PROJECT = HERE.parents[4]
OUT = HERE.parent.parent / "generated"


def load(relative: str):
    return json.loads((PROJECT / relative).read_text(encoding="utf-8"))


def session(index: dict, prefix: str) -> dict:
    matches = [item for item in index["sessions"] if item["id"].startswith(prefix)]
    assert len(matches) == 1, (prefix, len(matches))
    return matches[0]


def extract(field: str, start: str, end: str | None = None) -> str:
    assert start in field, start
    tail = field[field.index(start) :]
    if end is None:
        return tail.strip()
    assert end in tail, end
    return tail[: tail.index(end)].strip()


def tex(value: str) -> str:
    value = value.replace("&#x20;", "")
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "²": r"\textsuperscript{2}",
        "³": r"\textsuperscript{3}",
        "⁴": r"\textsuperscript{4}",
        "⁵": r"\textsuperscript{5}",
        "₁": r"\textsubscript{1}",
        "₂": r"\textsubscript{2}",
        "₄": r"\textsubscript{4}",
        "₅": r"\textsubscript{5}",
        "₇": r"\textsubscript{7}",
        "≈": r"\(\approx\)",
        "≤": r"\(\leq\)",
        "≥": r"\(\geq\)",
        "→": r"\(\to\)",
        "⇒": r"\(\Rightarrow\)",
        "×": r"\(\times\)",
        "≡": r"\(\equiv\)",
        "Φ": r"\(\Phi\)",
        "Θ": r"\(\Theta\)",
        "θ": r"\(\theta\)",
        "χ": r"\(\chi\)",
        "−": "-",
        "–": "--",
        "—": "---",
        "…": r"\ldots{}",
        "✅": r"\(\checkmark\)",
    }
    return "".join(replacements.get(char, char) for char in value)


def block(label: str, meta: str, speaker: str, value: str) -> list[str]:
    lines = [
        rf"\subsubsection*{{Excerpt {label}}}",
        rf"\phantomsection\label{{ex:{label.replace('.', '')}}}",
        rf"\noindent\textit{{{meta}; speaker: {speaker}.}}",
        r"\begin{quote}\small\ttfamily\raggedright",
    ]
    for source_line in value.splitlines():
        if not source_line.strip():
            lines.append(r"\medskip")
            continue
        lines.append(tex(source_line.rstrip()))
        lines.append(r"\par")
    lines.extend([r"\end{quote}", ""])
    return lines


def main() -> None:
    workstation = load("history/session_index.json")
    second = load("history/addendum_desktop-q0hdpqd/addendum_index.json")

    repair = session(workstation, "01a03722")
    fable = session(workstation, "d19b441c")
    opus = session(workstation, "272ea172")
    breakthrough = session(second, "01a0349f")

    repair_prompt = repair["turns"][1]["prompt"].strip()
    repair_report = extract(
        repair["turns"][1]["report"],
        "Key finding:",
        "Changes:",
    ) + "\n\n" + extract(
        repair["turns"][1]["report"],
        "Atlas 43 remains marked",
    )

    crash_prompt = fable["turns"][6]["prompt"].strip()
    crash_report = extract(
        fable["turns"][6]["report"],
        "1. **The crash was mine.",
        "2. Untouched, not mine:",
    )
    sequential_report = extract(
        fable["turns"][8]["report"],
        "**Atlas 43 and 196 are",
        "**Bonus fix:**",
    )

    scale_prompt = opus["turns"][2]["prompt"].strip()
    scale_report = extract(
        opus["turns"][2]["report"],
        "## Atlas 127: not feasible",
        "## The numbers you asked for",
    ) + "\n\n" + extract(
        opus["turns"][2]["report"],
        "**Files: roughly",
        "## Two things worth weighing",
    )
    redirect_prompt = opus["turns"][3]["prompt"].strip()
    redirect_report = extract(
        opus["turns"][3]["report"],
        "**The decisive direction works",
        "## Ranked fallbacks",
    )
    rational_report = extract(
        opus["turns"][4]["report"],
        "## Rationalization works.",
        "**Two caveats.**",
    )
    verified_report = extract(
        opus["turns"][5]["report"],
        "Atlas 127 is verified",
        "**Three script fixes**",
    )

    breakthrough_prompt = extract(
        breakthrough["turns"][0]["prompt"],
        "/goal Would you please",
        "- Proving for some conditional graphon",
    )
    breakthrough_report = extract(
        breakthrough["turns"][0]["report"],
        "Outcome:",
        "Documentation and catalogue:",
    )

    sections: list[str] = [
        r"\section{Curated chronological excerpts}",
        r"\label{app:excerpts}",
        (
            "The selection rule includes exchanges that changed mathematical correctness, "
            "proof status, verification scope, resource policy, or research direction. "
            "Wording and typographical errors are retained.  Export-only HTML spacing "
            "markers are omitted, and mathematical Unicode glyphs receive equivalent "
            "LaTeX typesetting.  Ellipses are not inserted inside an excerpt."
        ),
        "",
        r"\subsection{The Atlas 43 semantic repair}",
    ]
    sections += block(
        "B.1.1",
        "25 August 2026, 13:21 KST; Codex gpt-5.6-sol, xhigh; session 01a03722, turn 1; prompt A.38",
        "human author",
        repair_prompt,
    )
    sections += block(
        "B.1.2",
        "25 August 2026, 14:04 KST; same session and turn",
        "Codex",
        repair_report,
    )
    sections.append(r"\subsection{Memory failure and sequential checking}")
    sections += block(
        "B.2.1",
        "22 September 2026, 13:27 KST; Claude Code claude-fable-5-1, high; session d19b441c, turn 6; prompt A.74",
        "human author",
        crash_prompt,
    )
    sections += block(
        "B.2.2",
        "22 September 2026, 14:30 KST; same session and turn",
        "Claude Fable",
        crash_report,
    )
    sections += block(
        "B.2.3",
        "22 September 2026, 22:07 KST; same session, turn 8",
        "Claude Fable",
        sequential_report,
    )
    sections.append(r"\subsection{Replacing the Atlas 127 proof object}")
    sections += block(
        "B.3.1",
        "23 September 2026, 08:02 KST; Claude Code claude-opus-5, xhigh; session 272ea172, turn 2; prompt A.83",
        "human author",
        scale_prompt,
    )
    sections += block(
        "B.3.2",
        "23 September 2026, 11:44 KST; same session and turn",
        "Claude Opus",
        scale_report,
    )
    sections += block(
        "B.3.3",
        "23 September 2026, 11:44 KST; same session, turn 3; prompt A.84",
        "human author",
        redirect_prompt,
    )
    sections += block(
        "B.3.4",
        "23 September 2026, 12:00 KST; same session and turn",
        "Claude Opus",
        redirect_report,
    )
    sections += block(
        "B.3.5",
        "23 September 2026, 12:49 KST; same session, turn 4; response to prompt A.85",
        "Claude Opus",
        rational_report,
    )
    sections += block(
        "B.3.6",
        "23 September 2026, 13:44 KST; same session, turn 5; response to prompt A.86",
        "Claude Opus",
        verified_report,
    )
    sections.append(r"\subsection{The long Codex certificate turn}")
    sections += block(
        "B.4.1",
        "25 August 2026, 01:34 KST; Codex gpt-5.6-sol, xhigh; session 01a0349f, turn 0; prompt D.87",
        "human author",
        breakthrough_prompt,
    )
    sections += block(
        "B.4.2",
        "25 August 2026, 12:03 KST; same session and turn",
        "Codex",
        breakthrough_report,
    )

    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "excerpts.tex").write_text(
        "\n".join(sections).rstrip() + "\n", encoding="utf-8"
    )
    print("generated 13 curated excerpts")


if __name__ == "__main__":
    main()
