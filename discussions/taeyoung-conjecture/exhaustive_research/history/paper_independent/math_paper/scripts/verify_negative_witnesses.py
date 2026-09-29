"""Recompute all 23 negative witnesses with exact rational arithmetic."""

from __future__ import annotations

import itertools
import json
import re
from fractions import Fraction
from pathlib import Path

import networkx as nx
import sympy as sp


HERE = Path(__file__).resolve()
PROJECT = HERE.parents[4]
CLASSIFICATION = HERE.parent.parent / "generated" / "classification.json"
OUT = HERE.parent.parent / "generated"


def polynomial_value(graph: nx.Graph, value: Fraction) -> Fraction:
    polynomial = nx.chromatic_polynomial(graph)
    symbol = next(iter(polynomial.free_symbols))
    evaluated = polynomial.as_expr().subs(symbol, sp.Rational(value.numerator, value.denominator))
    rational = sp.Rational(evaluated)
    return Fraction(int(rational.p), int(rational.q))


def target_value(graph: nx.Graph, p: Fraction) -> Fraction:
    return (1 - p) ** len(graph) * polynomial_value(graph, 1 / (1 - p))


def hom_density_uniform(graph: nx.Graph, numerators: list[list[int]], scale: int) -> Fraction:
    states = len(numerators)
    total = 0
    for assignment in itertools.product(range(states), repeat=len(graph)):
        product = 1
        for u, v in graph.edges():
            product *= numerators[assignment[u]][assignment[v]]
        total += product
    return Fraction(total, states ** len(graph) * scale ** graph.number_of_edges())


def edge_density_uniform(numerators: list[list[int]], scale: int) -> Fraction:
    states = len(numerators)
    return Fraction(sum(map(sum, numerators)), states * states * scale)


def hom_density_weighted(
    graph: nx.Graph,
    weights: list[int],
    weight_denominator: int,
    numerators: list[list[int]],
    scale: int,
) -> Fraction:
    states = len(weights)
    total = 0
    for assignment in itertools.product(range(states), repeat=len(graph)):
        product = 1
        for vertex in range(len(graph)):
            product *= weights[assignment[vertex]]
        for u, v in graph.edges():
            product *= numerators[assignment[u]][assignment[v]]
        total += product
    denominator = weight_denominator ** len(graph) * scale ** graph.number_of_edges()
    return Fraction(total, denominator)


def edge_density_weighted(
    weights: list[int], weight_denominator: int, numerators: list[list[int]], scale: int
) -> Fraction:
    total = sum(weights[i] * weights[j] * numerators[i][j]
                for i in range(len(weights)) for j in range(len(weights)))
    return Fraction(total, weight_denominator * weight_denominator * scale)


def latex_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return rf"\frac{{{value.numerator}}}{{{value.denominator}}}"


def tex_escape(value: str) -> str:
    return value.replace("_", r"\_").replace("&", r"\&").replace("%", r"\%")


def main() -> None:
    rows = json.loads(CLASSIFICATION.read_text(encoding="utf-8"))
    atlas = nx.graph_atlas_g()
    two_scale = [[0, 1, 4, 4], [1, 0, 4, 4], [4, 4, 0, 1], [4, 4, 1, 0]]
    one_diagonal = [[1, 4, 4], [4, 0, 4], [4, 4, 0]]
    weights_152 = [1870752, 2998, 1875000, 125, 1125]
    matrix_152 = [
        [0, 0, 16, 16, 0],
        [0, 0, 16, 0, 16],
        [16, 16, 0, 1, 16],
        [16, 0, 1, 0, 0],
        [0, 16, 16, 0, 0],
    ]
    results: list[dict[str, str | int]] = []
    for row in rows:
        if row["status"] != "negative":
            continue
        atlas_id = int(row["atlas"])
        graph = atlas[atlas_id]
        reason = str(row["reason"])
        tensor = re.search(r"T_\{(\d+)\}\s*\\otimes\s*T_\{(\d+)\}", reason)
        if tensor:
            a, b = map(int, tensor.groups())
            p = Fraction(a - 1, a) * Fraction(b - 1, b)
            density = Fraction(
                int(nx.chromatic_polynomial(graph).subs({next(iter(nx.chromatic_polynomial(graph).free_symbols)): a})),
                a ** len(graph),
            ) * Fraction(
                int(nx.chromatic_polynomial(graph).subs({next(iter(nx.chromatic_polynomial(graph).free_symbols)): b})),
                b ** len(graph),
            )
            witness = rf"$T_{{{a}}}\otimes T_{{{b}}}$"
            source = "lean/Taeyoung/Methods/Negative/Tensor.lean"
        elif atlas_id in (166, 172):
            p = edge_density_uniform(two_scale, 4)
            density = hom_density_uniform(graph, two_scale, 4)
            witness = "four-step two-scale perturbation"
            source = "lean/Taeyoung/Methods/Negative/LocalTuran.lean"
        elif atlas_id == 206:
            p = edge_density_uniform(one_diagonal, 4)
            density = hom_density_uniform(graph, one_diagonal, 4)
            witness = "three-step one-diagonal perturbation"
            source = "lean/Taeyoung/Methods/Negative/LocalTuran.lean"
        elif atlas_id == 152:
            p = edge_density_weighted(weights_152, 3750000, matrix_152, 16)
            density = hom_density_weighted(graph, weights_152, 3750000, matrix_152, 16)
            witness = "five-step fractional-fibre perturbation"
            source = "lean/Taeyoung/Methods/Negative/Atlas152.lean"
        else:
            raise AssertionError(atlas_id)
        target = target_value(graph, p)
        gap = density - target
        threshold = Fraction(int(row["chromatic_number"]) - 2, int(row["chromatic_number"]) - 1)
        assert p >= threshold, (atlas_id, p, threshold)
        assert gap < 0, (atlas_id, gap)
        results.append(
            {
                "atlas": atlas_id,
                "witness": witness,
                "p": str(p),
                "density": str(density),
                "target": str(target),
                "gap": str(gap),
                "source": source,
            }
        )
    assert len(results) == 23
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "negative_witnesses.json").write_text(
        json.dumps(results, indent=2) + "\n", encoding="utf-8"
    )

    lines = [
        r"\begin{landscape}",
        r"\scriptsize",
        r"\begin{longtable}{r p{4.0cm} l p{4.1cm} p{4.1cm} p{4.8cm}}",
        r"\caption{Exact counterexamples for the 23 negative rows.}\label{tab:negative-witnesses}\\",
        r"\toprule Atlas & witness & $p$ & $t(H,W)$ & $\Phi_H(p)$ & $t(H,W)-\Phi_H(p)$\\ \midrule",
        r"\endfirsthead",
        r"\toprule Atlas & witness & $p$ & $t(H,W)$ & $\Phi_H(p)$ & $t(H,W)-\Phi_H(p)$\\ \midrule",
        r"\endhead",
        r"\bottomrule\endfoot",
    ]
    for result in results:
        p = Fraction(result["p"])
        density = Fraction(result["density"])
        target = Fraction(result["target"])
        gap = Fraction(result["gap"])
        target_cell = f"${latex_fraction(target)}$"
        gap_cell = f"${latex_fraction(gap)}$"
        if result["atlas"] == 152:
            target_cell = rf"\resizebox{{3.95cm}}{{!}}{{${latex_fraction(target)}$}}"
            gap_cell = rf"\resizebox{{4.65cm}}{{!}}{{${latex_fraction(gap)}$}}"
        lines.append(
            f"{result['atlas']} & {result['witness']} & ${latex_fraction(p)}$ & "
            f"${latex_fraction(density)}$ & {target_cell} & {gap_cell}\\\\"
        )
    lines.extend([r"\end{longtable}", r"\end{landscape}", ""])
    (OUT / "negative_witnesses_table.tex").write_text("\n".join(lines), encoding="utf-8")
    print(f"verified {len(results)} exact negative witnesses")


if __name__ == "__main__":
    main()
