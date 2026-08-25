"""Low-memory exact audit for conditional implications among unresolved rows.

This script verifies the structural and polynomial claims in
``notes/open_conditional_implications.tex``.  It deliberately separates
the full cone-closure arrow, proper-subinterval containment arrows, and graphs
that merely look like extensions.
"""

from __future__ import annotations

from itertools import permutations

import networkx as nx
import sympy as sp
from networkx.algorithms.polynomials import chromatic_polynomial


UNRESOLVED = {
    43,
    118,
    122,
    124,
    130,
    147,
    151,
    153,
    157,
    168,
    169,
    171,
    174,
    181,
    185,
    188,
    194,
    196,
    199,
    203,
}


def atlas_id(graph: nx.Graph, atlas: list[nx.Graph]) -> int | None:
    """Return the NetworkX Atlas ID of ``graph``, if it is in the Atlas."""

    for index, candidate in enumerate(atlas):
        if (
            len(candidate) == len(graph)
            and candidate.number_of_edges() == graph.number_of_edges()
            and nx.is_isomorphic(candidate, graph)
        ):
            return index
    return None


def phi(graph: nx.Graph, p: sp.Symbol, x: sp.Symbol) -> sp.Expr:
    chi = chromatic_polynomial(graph)
    return sp.factor((1 - p) ** len(graph) * chi.subs(x, 1 / (1 - p)))


def mapped_edges(graph: nx.Graph, vertex_map: tuple[int, ...]) -> set[tuple[int, int]]:
    """Return the edge set after applying a labelled vertex embedding."""

    return {
        tuple(sorted((vertex_map[u], vertex_map[v]))) for u, v in graph.edges()
    }


def positive_length_nonnegative_locus(
    polynomial: sp.Expr,
    variable: sp.Symbol,
    lower: sp.Rational,
) -> sp.Set:
    """Exactly return the positive-length nonnegative locus in [lower, 1].

    Every target gap arising in this finite audit factors over the rationals
    into linear factors and positive/negative-definite irreducible quadratics.
    Consequently its sign can change only at rational roots of its linear
    factors.  Rational midpoint tests on the resulting cells are exact.  The
    closure of every positive cell is precisely a positive-length component
    of the nonnegative locus; isolated zeroes are deliberately omitted.
    """

    poly = sp.Poly(sp.expand(polynomial), variable, domain=sp.QQ)
    assert not poly.is_zero
    cuts = {lower, sp.Rational(1)}
    _, factors = sp.factor_list(poly.as_expr(), variable)
    for factor, _multiplicity in factors:
        factor_poly = sp.Poly(factor, variable, domain=sp.QQ)
        if factor_poly.degree() == 1:
            leading, constant = factor_poly.all_coeffs()
            root = -constant / leading
            if lower < root < 1:
                cuts.add(root)
        elif factor_poly.degree() == 2:
            # A real irrational root would require algebraic sign cells.  The
            # assertion certifies that none occurs in this 20-row audit.
            assert sp.discriminant(factor_poly.as_expr(), variable) < 0
        else:
            raise AssertionError(f"unexpected irreducible factor: {factor}")

    locus: sp.Set = sp.EmptySet
    ordered_cuts = sorted(cuts)
    for left, right in zip(ordered_cuts, ordered_cuts[1:]):
        midpoint = (left + right) / 2
        value = poly.eval(midpoint)
        assert value != 0
        if value > 0:
            locus = sp.Union(locus, sp.Interval(left, right))
    return locus


def main() -> None:
    atlas = nx.graph_atlas_g()
    assert len(UNRESOLVED) == 20
    assert [index for index in sorted(UNRESOLVED) if len(atlas[index]) == 5] == [43]
    assert all(nx.is_connected(atlas[index]) for index in UNRESOLVED)

    # A universal-vertex closure can remain inside the six-vertex catalogue
    # only when its base has at most five vertices.
    cone_arrows: list[tuple[int, int]] = []
    for target_id in sorted(UNRESOLVED):
        target = atlas[target_id]
        for vertex, degree in target.degree():
            if degree != len(target) - 1:
                continue
            base = target.copy()
            base.remove_node(vertex)
            base_id = atlas_id(base, atlas)
            if base_id in UNRESOLVED:
                cone_arrows.append((base_id, target_id))

    assert cone_arrows == [(43, 196)]

    house = atlas[43]
    cone = house.copy()
    apex = max(cone.nodes, default=-1) + 1
    cone.add_node(apex)
    cone.add_edges_from((apex, vertex) for vertex in house)
    assert nx.is_isomorphic(cone, atlas[196])

    # The three leaf extensions are structural candidates, but no accepted
    # one-leaf closure theorem certifies them.
    leaf_candidates: list[int] = []
    for target_id in sorted(UNRESOLVED):
        target = atlas[target_id]
        for vertex, degree in list(target.degree()):
            if degree != 1:
                continue
            base = target.copy()
            base.remove_node(vertex)
            if nx.is_isomorphic(base, house):
                leaf_candidates.append(target_id)
                break
    assert leaf_candidates == [118, 122, 124]

    x, p, z, u = sp.symbols("x p z u")
    chi_43 = sp.factor(chromatic_polynomial(house))
    chi_196 = sp.factor(chromatic_polynomial(atlas[196]))
    phi_43 = phi(house, p, x)
    phi_196 = phi(atlas[196], p, x)

    assert chi_43 == x * (x - 1) * (x - 2) * (x**2 - 3 * x + 3)
    assert chi_196 == (
        x * (x - 1) * (x - 2) * (x - 3) * (x**2 - 5 * x + 7)
    )
    assert phi_43 == p * (2 * p - 1) * (3 * p**2 - 3 * p + 1)
    assert phi_196 == (
        p * (2 * p - 1) * (3 * p - 2) * (7 * p**2 - 9 * p + 3)
    )

    house_target_z = z * (2 * z - 1) * (3 * z**2 - 3 * z + 1)
    lifted = sp.factor(p**5 * house_target_z.subs(z, 2 - 1 / p))
    assert sp.factor(lifted - phi_196) == 0
    assert sp.factor(
        sp.diff(house_target_z, z, 2) - 2 * (3 * z - 1) * (12 * z - 5)
    ) == 0

    # Range arrow 188 -> 171.  Under this labelled embedding, Atlas 188 is
    # Atlas 171 plus exactly the edge 15.  Density monotonicity under deleting
    # an edge and the displayed target factorization prove the transfer on
    # 1/2 <= p <= 2/3.
    map_171_into_188 = (0, 5, 4, 3, 1, 2)
    edges_188 = {tuple(sorted(edge)) for edge in atlas[188].edges()}
    image_171 = mapped_edges(atlas[171], map_171_into_188)
    assert image_171 <= edges_188
    assert edges_188 - image_171 == {(1, 5)}
    phi_171 = phi(atlas[171], p, x)
    phi_188 = phi(atlas[188], p, x)
    diff_188_171 = p * (p - 1) * (2 * p - 1) ** 2 * (3 * p - 2)
    assert sp.factor(phi_188 - phi_171 - diff_188_171) == 0
    assert sp.factor(diff_188_171.subs(p, sp.Rational(1, 2) + u / 6)) == (
        u**2 * (u - 3) * (u - 1) * (u + 3) / 648
    )

    # Range arrow 188 -> 153.  Atlas 188 is the displayed copy of Atlas 153
    # plus exactly the two edges 15 and 24; its target dominates through 3/5.
    map_153_into_188 = (0, 1, 3, 4, 5, 2)
    image_153 = mapped_edges(atlas[153], map_153_into_188)
    assert image_153 <= edges_188
    assert edges_188 - image_153 == {(1, 5), (2, 4)}
    phi_153 = phi(atlas[153], p, x)
    diff_188_153 = p * (p - 1) * (2 * p - 1) ** 2 * (5 * p - 3)
    assert sp.factor(phi_188 - phi_153 - diff_188_153) == 0
    assert sp.factor(diff_188_153.subs(p, sp.Rational(1, 2) + u / 10)) == (
        u**2 * (u - 5) * (u - 1) * (u + 5) / 5000
    )

    # Range arrow 199 -> 181.  Atlas 199 is the displayed copy of Atlas 181
    # plus exactly the edge 03; the target difference is nonnegative on
    # 2/3 <= p <= 3/4.
    map_181_into_199 = (1, 3, 2, 4, 5, 0)
    edges_199 = {tuple(sorted(edge)) for edge in atlas[199].edges()}
    image_181 = mapped_edges(atlas[181], map_181_into_199)
    assert image_181 <= edges_199
    assert edges_199 - image_181 == {(0, 3)}
    phi_181 = phi(atlas[181], p, x)
    phi_199 = phi(atlas[199], p, x)
    diff_199_181 = p * (p - 1) * (2 * p - 1) * (3 * p - 2) * (4 * p - 3)
    assert sp.factor(phi_199 - phi_181 - diff_199_181) == 0
    assert sp.factor(diff_199_181.subs(p, sp.Rational(2, 3) + u / 12)) == (
        u * (u - 4) * (u - 1) * (u + 2) * (u + 8) / 10368
    )

    # Exhaust every ordered spanning-subgraph containment pair among the 20
    # unresolved rows.  A source theorem can be invoked only where both its
    # own required interval and the target's required interval are active.
    # We separately retain the target-only scan below to certify that this
    # intersection does not silently discard another applicable arrow.
    chromatic = {
        index: sp.factor(chromatic_polynomial(atlas[index]))
        for index in UNRESOLVED
    }
    targets = {
        index: sp.factor(
            (1 - p) ** len(atlas[index])
            * chromatic[index].subs(x, 1 / (1 - p))
        )
        for index in UNRESOLVED
    }
    chromatic_numbers = {
        index: next(
            colors
            for colors in range(1, len(atlas[index]) + 1)
            if chromatic[index].subs(x, colors) > 0
        )
        for index in UNRESOLVED
    }
    required_lower = {
        index: sp.Rational(number - 2, number - 1)
        for index, number in chromatic_numbers.items()
    }
    assert set(required_lower.values()) == {sp.Rational(1, 2), sp.Rational(2, 3)}

    containment_pairs: list[tuple[int, int]] = []
    for source_id, target_id in permutations(sorted(UNRESOLVED), 2):
        source, target = atlas[source_id], atlas[target_id]
        if len(source) != len(target):
            continue
        if source.number_of_edges() < target.number_of_edges():
            continue
        if nx.algorithms.isomorphism.GraphMatcher(
            source, target
        ).subgraph_is_monomorphic():
            containment_pairs.append((source_id, target_id))
    assert len(containment_pairs) == 108

    target_domain_loci: dict[tuple[int, int], sp.Set] = {}
    applicable_loci: dict[tuple[int, int], sp.Set] = {}
    for source_id, target_id in containment_pairs:
        gap = sp.factor(targets[source_id] - targets[target_id])
        target_locus = positive_length_nonnegative_locus(
            gap, p, required_lower[target_id]
        )
        if target_locus != sp.EmptySet:
            target_domain_loci[(source_id, target_id)] = target_locus

        premise_lower = max(required_lower[source_id], required_lower[target_id])
        applicable_locus = positive_length_nonnegative_locus(gap, p, premise_lower)
        if applicable_locus != sp.EmptySet:
            applicable_loci[(source_id, target_id)] = applicable_locus

    expected_applicable_loci = {
        (188, 153): sp.Interval(sp.Rational(1, 2), sp.Rational(3, 5)),
        (188, 171): sp.Interval(sp.Rational(1, 2), sp.Rational(2, 3)),
        (199, 181): sp.Interval(sp.Rational(2, 3), sp.Rational(3, 4)),
    }
    assert applicable_loci == expected_applicable_loci

    # Four further target-gap loci occur only below the source theorem's
    # required p >= 2/3 premise, so they are not conditional implications.
    expected_target_only_loci = expected_applicable_loci | {
        (194, 153): sp.Interval(sp.Rational(1, 2), sp.Rational(4, 7)),
        (194, 171): sp.Interval(sp.Rational(1, 2), sp.Rational(3, 5)),
        (196, 153): sp.Interval(sp.Rational(1, 2), sp.Rational(4, 7)),
        (196, 171): sp.Interval(sp.Rational(1, 2), sp.Rational(3, 5)),
    }
    assert target_domain_loci == expected_target_only_loci

    # Nontrivial self-amalgams or full whiskerings of any unresolved base
    # have more than six vertices, so they cannot yield another scoped row.
    minimum_unresolved_order = min(len(atlas[index]) for index in UNRESOLVED)
    assert minimum_unresolved_order == 5
    assert 2 * minimum_unresolved_order > 6  # full whiskering
    assert 2 * minimum_unresolved_order - 1 > 6  # vertex self-amalgam
    assert 2 * minimum_unresolved_order - 2 > 6  # edge self-amalgam

    # Check that the leaf targets really are all p times the house target.
    for target_id in leaf_candidates:
        assert sp.factor(phi(atlas[target_id], p, x) - p * phi_43) == 0

    print(f"unresolved rows: {len(UNRESOLVED)}")
    print(f"certified universal-cone arrows: {cone_arrows}")
    print(f"one-leaf structural candidates (not arrows): {leaf_candidates}")
    print(f"chi_43(x) = {chi_43}")
    print(f"chi_196(x) = {chi_196}")
    print(f"Phi_43(p) = {phi_43}")
    print(f"Phi_196(p) = {phi_196}")
    print("lift identity p^5 Phi_43(2-1/p) = Phi_196(p): exact")
    print("range arrow 188 -> 171 on [1/2, 2/3]: exact")
    print("range arrow 188 -> 153 on [1/2, 3/5]: exact")
    print("range arrow 199 -> 181 on [2/3, 3/4]: exact")
    print(f"ordered spanning-containment pairs audited: {len(containment_pairs)}")
    print("applicable positive-length target-gap loci (exhaustive):")
    for pair, locus in sorted(applicable_loci.items()):
        print(f"  {pair[0]} -> {pair[1]}: {locus}")


if __name__ == "__main__":
    main()
