"""Generate the 117-row classification data and LaTeX table from project sources."""

from __future__ import annotations

import html
import json
import re
from pathlib import Path

import networkx as nx
import sympy as sp


HERE = Path(__file__).resolve()
PROJECT = HERE.parents[4]
CATALOGUE = PROJECT / "GRAPH_CLASSIFICATION_UP_TO_6_VERTICES.md"
EXAMPLES = PROJECT / "lean" / "Taeyoung" / "Examples"
OUT = HERE.parent.parent / "generated"

FALLBACK_SOURCES = {
    "odd-cycle bound": ["notes/paper_new_region2_v3.tex"],
    "paw inequality": ["notes/rooted_triangle_tree_extensions.tex"],
    "pure chordal": ["notes/pure_chordal.tex"],
    "rooted triangle--tree inequality": ["notes/rooted_triangle_tree_extensions.tex"],
    "clique common-leaf inequality": ["notes/clique_common_leaf_extensions.tex"],
    "tensor product of Turan graphons": [
        "lean/Taeyoung/Methods/Negative/Tensor.lean",
        "history/paper_independent/math_paper/scripts/verify_negative_witnesses.py",
    ],
    "special cone inequality": ["notes/paw_triangle_edge_cones.tex"],
    "component multiplicativity": ["history/paper_independent/math_paper/main.tex"],
    "whiskering": ["notes/whiskering.tex"],
    "self-amalgamation": ["notes/self_amalgam.tex"],
    "cone over a forest": ["notes/forest_cone_graphon_bound.tex"],
    "six explicit cone lifts": ["notes/six_verified_base_cones.tex"],
    "concrete clique--odd-cycle theorem": ["notes/clique_oddcycle_join.tex"],
}

ROW_RE = re.compile(
    r"^\|\s*(?P<atlas>\d+)\s*\|.*?\|\s*(?P<v>\d+)\s*\|\s*"
    r"(?P<e>\d+)\s*\|\s*(?P<chi>\d+)\s*\|\s*<code>(?P<g6>.*?)</code>\s*\|\s*"
    r"(?P<status>.*?)\s*\|\s*(?P<lean>.*?)\s*\|\s*(?P<reason>.*?)\s*\|$"
)


def chromatic_number(graph: nx.Graph) -> int:
    vertices = list(graph.nodes())
    for colors in range(1, len(vertices) + 1):
        assignment = [-1] * len(vertices)

        def search(index: int) -> bool:
            if index == len(vertices):
                return True
            vertex = vertices[index]
            for color in range(colors):
                if all(
                    assignment[vertices.index(neighbor)] != color
                    for neighbor in graph.neighbors(vertex)
                    if vertices.index(neighbor) < index
                ):
                    assignment[index] = color
                    if search(index + 1):
                        return True
                    assignment[index] = -1
            return False

        if search(0):
            return colors
    raise AssertionError("finite graph has no coloring")


def plain_markdown(value: str) -> str:
    value = html.unescape(value)
    value = re.sub(r"\[([^]]+)\]\([^)]+\)", r"\1", value)
    value = re.sub(r"<[^>]+>", "", value)
    value = value.replace("**", "").replace("`", "")
    value = value.replace("🟢", "").replace("🔴", "").replace("✅", "")
    return " ".join(value.split())


def note_paths(reason: str) -> list[str]:
    return sorted(set(re.findall(r"\((notes/[^)]+)\)", reason)))


def method_label(reason: str, status: str) -> str:
    text = plain_markdown(reason)
    rules = [
        ("Exact induced rooted interval", "induced rooted interval SOS"),
        ("Exact rooted interval-SOS", "three-root interval SOS"),
        ("Exact four-root interval-SOS", "four-root interval SOS"),
        ("Exact compact", "compact four-root interval SOS"),
        ("normalized-link cone", "normalized-link cone lift"),
        ("house inequality", "normalized-link cone lift"),
        ("Pure-chordal", "pure chordal"),
        ("Odd-cycle Goodman", "odd-cycle bound"),
        ("Independent proof for the paw", "paw inequality"),
        ("Tensor", "tensor product of Turan graphons"),
        ("Turan-local", "local perturbation of a Turan graphon"),
        ("Turán-local", "local perturbation of a Turan graphon"),
        ("fractional-fibre", "fractional-fibre step graphon"),
        ("Whiskering", "whiskering"),
        ("self-amalgam", "self-amalgamation"),
        ("Multiplicativity", "component multiplicativity"),
        ("Cone-over-forest", "cone over a forest"),
        ("Six verified-base cone", "six explicit cone lifts"),
        ("Paw/triangle", "special cone inequality"),
        ("Rooted triangle", "rooted triangle--tree inequality"),
        ("Mixed rooted", "mixed rooted-triangle inequality"),
        ("Two-root", "two-root book inequality"),
        ("Page-rooted", "page-rooted book inequality"),
        ("Triangle-book", "triangle-book attachment inequality"),
        ("Triangle three-edge", "triangle tail inequality"),
        ("Triangle two-leaf", "triangle broom inequality"),
        ("Triangle adjacent", "adjacent leaf--tail inequality"),
        ("Odd-cycle one-leaf", "odd-cycle leaf inequality"),
        ("Diamond", "diamond leaf inequality"),
        ("Bowtie", "bowtie leaf inequality"),
        ("Clique common", "clique common-leaf inequality"),
        ("Clique distributed", "clique distributed-leaf inequality"),
        ("supporting plane", "supporting-plane inequality"),
        ("Hilbert projection", "Hilbert projection"),
        ("concentration", "exact square identity"),
        ("smoothed Goodman", "direct compact interval SOS"),
        ("Concrete clique", "concrete clique--odd-cycle theorem"),
    ]
    for needle, label in rules:
        if needle.lower() in text.lower():
            return label
    if status == "negative":
        return "exact step-graphon counterexample"
    return text.split(":", 1)[0].split("(", 1)[0].strip()


def tex_escape(value: str) -> str:
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
    }
    return "".join(replacements.get(char, char) for char in value)


def parse_rows() -> list[dict[str, object]]:
    atlas = nx.graph_atlas_g()
    p = sp.Symbol("p")
    rows: list[dict[str, object]] = []
    for line in CATALOGUE.read_text(encoding="utf-8").splitlines():
        match = ROW_RE.match(line)
        if not match:
            continue
        source = match.groupdict()
        atlas_id = int(source["atlas"])
        graph = atlas[atlas_id]
        graph6 = nx.to_graph6_bytes(graph, header=False).decode("ascii").strip()
        expected_graph6 = html.unescape(source["g6"])
        assert graph6 == expected_graph6, (atlas_id, graph6, expected_graph6)
        vertices = int(source["v"])
        edges = int(source["e"])
        chi = int(source["chi"])
        assert (len(graph), graph.number_of_edges(), chromatic_number(graph)) == (
            vertices,
            edges,
            chi,
        )
        polynomial = nx.chromatic_polynomial(graph)
        x = next(iter(polynomial.free_symbols))
        target = sp.factor(
            sp.cancel((1 - p) ** vertices * polynomial.as_expr().subs(x, 1 / (1 - p)))
        )
        status_text = plain_markdown(source["status"]).lower()
        status = "positive" if "positive" in status_text else "negative"
        lean_text = plain_markdown(source["lean"]).lower()
        assert "verified" in lean_text
        example = EXAMPLES / f"Graph{atlas_id:03d}.lean"
        assert example.exists()
        example_text = example.read_text(encoding="utf-8")
        theorem_kind = "SatisfiesLowerBound" if status == "positive" else "ViolatesLowerBound"
        assert f"theorem status : {theorem_kind} graph" in example_text
        reason = source["reason"]
        rows.append(
            {
                "atlas": atlas_id,
                "graph6": graph6,
                "vertices": vertices,
                "edges_count": edges,
                "edge_list": [list(edge) for edge in sorted(tuple(sorted(edge)) for edge in graph.edges())],
                "chromatic_number": chi,
                "admissible_left": str(sp.Rational(chi - 2, chi - 1)),
                "chromatic_polynomial": str(sp.factor(polynomial.as_expr())),
                "target": str(target),
                "target_latex": sp.latex(target),
                "status": status,
                "method": method_label(reason, status),
                "reason": plain_markdown(reason),
                "notes": note_paths(reason),
                "lean_file": str(example.relative_to(PROJECT)).replace("\\", "/"),
                "lean_theorem": f"Taeyoung.Examples.Graph{atlas_id:03d}.status",
            }
        )
    assert len(rows) == 117, len(rows)
    assert sum(row["status"] == "positive" for row in rows) == 94
    assert sum(row["status"] == "negative" for row in rows) == 23
    return rows


def write_latex(rows: list[dict[str, object]]) -> None:
    lines = [
        r"\begin{landscape}",
        r"\fontsize{5.5}{6.5}\selectfont",
        r"\setlength{\tabcolsep}{1.5pt}",
        r"\begin{longtable}{r l r r r l p{4.0cm} p{3.5cm} p{2.7cm}}",
        r"\caption{Complete classification.  The interval column gives the required range of edge densities.}\label{tab:classification}\\",
        r"\toprule",
        r"Atlas & graph6 & $v$ & $e$ & $\chi$ & interval & $\Phi_H(p)$ & method & Lean theorem\\",
        r"\midrule",
        r"\endfirsthead",
        r"\multicolumn{9}{c}{\tablename\ \thetable\ (continued)}\\",
        r"\toprule",
        r"Atlas & graph6 & $v$ & $e$ & $\chi$ & interval & $\Phi_H(p)$ & method & Lean theorem\\",
        r"\midrule",
        r"\endhead",
        r"\midrule",
        r"\multicolumn{9}{r}{continued on next page}\\",
        r"\endfoot",
        r"\bottomrule",
        r"\endlastfoot",
    ]
    for row in rows:
        interval = rf"$[{sp.latex(sp.Rational(row['chromatic_number'] - 2, row['chromatic_number'] - 1))},1]$"
        status = "+" if row["status"] == "positive" else "--"
        method = f"{status} {tex_escape(str(row['method']))}"
        theorem = rf"\texttt{{Graph{row['atlas']:03d}.status}}"
        lines.append(
            f"{row['atlas']} & \\texttt{{{tex_escape(str(row['graph6']))}}} & "
            f"{row['vertices']} & {row['edges_count']} & {row['chromatic_number']} & {interval} & "
            f"${row['target_latex']}$ & {method} & {theorem}\\\\"
        )
    lines.extend([r"\end{longtable}", r"\end{landscape}", ""])
    (OUT / "classification_table.tex").write_text("\n".join(lines), encoding="utf-8")

    edge_lines = [
        r"\begin{landscape}",
        r"\scriptsize",
        r"\begin{longtable}{r l p{8.7cm} p{7.0cm}}",
        r"\caption{Machine-readable identifiers, edge lists, and source files.}\label{tab:row-sources}\\",
        r"\toprule Atlas & graph6 & edge list & source\\ \midrule",
        r"\endfirsthead",
        r"\toprule Atlas & graph6 & edge list & source\\ \midrule",
        r"\endhead",
        r"\bottomrule\endfoot",
    ]
    for row in rows:
        edge_list = ", ".join(f"{u}{v}" for u, v in row["edge_list"])
        sources = list(row["notes"]) or list(FALLBACK_SOURCES.get(str(row["method"]), []))
        assert sources, (row["atlas"], row["method"])
        sources.append(str(row["lean_file"]))
        source = "; ".join(rf"\path{{{item}}}" for item in sources)
        edge_lines.append(
            f"{row['atlas']} & \\texttt{{{tex_escape(str(row['graph6']))}}} & "
            f"{tex_escape(edge_list)} & {source}\\\\"
        )
    edge_lines.extend([r"\end{longtable}", r"\end{landscape}", ""])
    (OUT / "row_sources_table.tex").write_text("\n".join(edge_lines), encoding="utf-8")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    rows = parse_rows()
    (OUT / "classification.json").write_text(
        json.dumps(rows, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    write_latex(rows)
    negative = [row["atlas"] for row in rows if row["status"] == "negative"]
    positive = [row["atlas"] for row in rows if row["status"] == "positive"]
    print(f"rows={len(rows)} positive={len(positive)} negative={len(negative)}")
    print("negative=" + ",".join(map(str, negative)))


if __name__ == "__main__":
    main()
