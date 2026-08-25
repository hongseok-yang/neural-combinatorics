"""Exact, low-memory audit for notes/four_self_amalgam_partial_ranges.tex.

Besides the elementary Goodman/pure-chordal comparison, this checks the
stronger comparison obtained from Fisher's sharp triangle-density band.
"""

from fractions import Fraction

import networkx as nx
import sympy as sp


p = sp.symbols("p")
s = 2 * p - 1
ATLAS = nx.graph_atlas_g()


def edge_set(graph):
    return {tuple(sorted(edge)) for edge in graph.edges()}


def check_isomorphism(source, target, mapping):
    assert set(mapping) == set(source)
    assert set(mapping.values()) == set(target)
    mapped_edges = {
        tuple(sorted((mapping[u], mapping[v]))) for u, v in source.edges()
    }
    assert mapped_edges == edge_set(target)


def eval_fraction(coefficients, value):
    result = Fraction(0)
    for coefficient in coefficients:
        result = result * value + coefficient
    return result


def sign_variations(values):
    """Number of sign changes after deleting exact zeros."""
    signs = [int(sp.sign(value)) for value in values if value != 0]
    return sum(left * right < 0 for left, right in zip(signs, signs[1:]))


# Atlas 153: two diamonds glued along the independent root {0,2}.
h153 = ATLAS[153]
s153 = h153.copy()
s153.add_edges_from([(0, 3), (2, 4)])
assert edge_set(h153) <= edge_set(s153)
assert edge_set(s153) - edge_set(h153) == {(0, 3), (2, 4)}
assert s153.subgraph([0, 2]).number_of_edges() == 0
check_isomorphism(
    s153.subgraph([0, 2, 1, 5]),
    ATLAS[17],
    {1: 0, 0: 1, 5: 2, 2: 3},
)
check_isomorphism(
    s153.subgraph([0, 2, 3, 4]),
    ATLAS[17],
    {3: 0, 0: 1, 4: 2, 2: 3},
)


# Atlas 171, 174, 188: two Atlas-47 copies glued along a four-vertex path.
clone_cases = {
    171: {
        "roots": (0, 3),
        "core": [1, 2, 4, 5],
        "added": {(0, 2), (1, 3)},
        "maps": [
            {1: 0, 0: 1, 4: 2, 5: 3, 2: 4},
            {1: 0, 3: 1, 4: 2, 5: 3, 2: 4},
        ],
    },
    174: {
        "roots": (0, 4),
        "core": [1, 2, 3, 5],
        "added": {(0, 5), (2, 4)},
        "maps": [
            {1: 0, 0: 1, 3: 2, 2: 3, 5: 4},
            {1: 0, 4: 1, 3: 2, 2: 3, 5: 4},
        ],
    },
    188: {
        "roots": (1, 4),
        "core": [0, 2, 3, 5],
        "added": {(0, 4)},
        "maps": [
            {3: 0, 1: 1, 5: 2, 0: 3, 2: 4},
            {3: 0, 4: 1, 5: 2, 0: 3, 2: 4},
        ],
    },
}

for atlas_id, data in clone_cases.items():
    graph = ATLAS[atlas_id]
    supergraph = graph.copy()
    supergraph.add_edges_from(data["added"])
    assert edge_set(graph) <= edge_set(supergraph)
    assert edge_set(supergraph) - edge_set(graph) == data["added"]
    assert nx.is_isomorphic(supergraph.subgraph(data["core"]), nx.path_graph(4))
    for root, mapping in zip(data["roots"], data["maps"]):
        branch = supergraph.subgraph(data["core"] + [root])
        check_isomorphism(branch, ATLAS[47], mapping)
    # The two rooted maps agree on every core vertex.
    assert all(data["maps"][0][v] == data["maps"][1][v] for v in data["core"])


# Exact chromatic targets.
q_polynomials = {
    153: 7 * p**3 - 12 * p**2 + 8 * p - 2,
    171: 11 * p**3 - 20 * p**2 + 13 * p - 3,
    174: 13 * p**3 - 25 * p**2 + 17 * p - 4,
    188: 17 * p**3 - 33 * p**2 + 22 * p - 5,
}
r_polynomials = {
    153: 8 * p**3 - 11 * p**2 + 7 * p - 2,
    171: 32 * p**4 - 59 * p**3 + 41 * p**2 - 12 * p + 1,
    174: 32 * p**4 - 61 * p**3 + 44 * p**2 - 13 * p + 1,
    188: 32 * p**4 - 65 * p**3 + 48 * p**2 - 14 * p + 1,
}
lower_bounds = {
    153: p**2 * s**4,
    171: s**6,
    174: s**6,
    188: s**6,
}

x = sp.symbols("x")
for atlas_id, q_poly in q_polynomials.items():
    chromatic = nx.chromatic_polynomial(ATLAS[atlas_id]).as_expr()
    target = sp.factor(
        sp.cancel((1 - p) ** 6 * chromatic.subs(x, 1 / (1 - p)))
    )
    assert sp.expand(target - p * s * q_poly) == 0
    expected_gap = (
        p * (p - 1) * s * r_polynomials[atlas_id]
        if atlas_id == 153
        else (p - 1) * s * r_polynomials[atlas_id]
    )
    assert sp.expand(lower_bounds[atlas_id] - target - expected_gap) == 0


# Strict monotonicity on [1/2,1] and unique endpoint roots.
expected_discriminants = {
    153: -188,
    171: -233324,
    174: -669356,
    188: -651240,
}
expected_half_derivatives = {
    153: Fraction(2),
    171: Fraction(3, 4),
    174: Fraction(5, 4),
    188: Fraction(5, 4),
}
expected_half_values = {
    153: Fraction(-1, 4),
    171: Fraction(-1, 8),
    174: Fraction(-1, 8),
    188: Fraction(-1, 8),
}
expected_one_values = {153: 2, 171: 3, 174: 3, 188: 2}

for atlas_id, r_poly in r_polynomials.items():
    derivative = sp.diff(r_poly, p)
    assert sp.discriminant(derivative, p) == expected_discriminants[atlas_id]
    assert Fraction(derivative.subs(p, sp.Rational(1, 2))) == expected_half_derivatives[atlas_id]
    assert Fraction(r_poly.subs(p, sp.Rational(1, 2))) == expected_half_values[atlas_id]
    assert int(r_poly.subs(p, 1)) == expected_one_values[atlas_id]


# Finite-decimal rational endpoint brackets.
brackets = {
    153: ("0.6128767076", "0.6128767077"),
    171: ("0.6292381397", "0.6292381398"),
    174: ("0.5927496223", "0.5927496224"),
    188: ("0.6121757702", "0.6121757703"),
}
coefficient_lists = {
    atlas_id: [int(c) for c in sp.Poly(poly, p).all_coeffs()]
    for atlas_id, poly in r_polynomials.items()
}

for atlas_id, (left_text, right_text) in brackets.items():
    left = Fraction(left_text)
    right = Fraction(right_text)
    left_value = eval_fraction(coefficient_lists[atlas_id], left)
    right_value = eval_fraction(coefficient_lists[atlas_id], right)
    assert left_value < 0 < right_value
    midpoint_coverage = 200 * (float((left + right) / 2) - 0.5)
    print(
        f"Atlas {atlas_id} elementary: {left_text} < gamma < {right_text}; "
        f"R(left)={left_value}; R(right)={right_value}; "
        f"coverage~{midpoint_coverage:.6f}%"
    )


# Fisher-strengthened comparison.  On Fisher's k=2 band, use
#   p=(1-y)(1+3y)/2,  g=(3/2)y(1-y)^2 <= t(K3,W).
# The triangle-sensitive pure-chordal and self-amalgam bounds are
#   t(153,W) >= g^4/p^2,
#   t(H,W)   >= g^6/p^6, H=171,174,188.
y = sp.symbols("y")
p_y = (1 - y) * (1 + 3 * y) / 2
g_y = sp.Rational(3, 2) * y * (1 - y) ** 2

# These primitive integer factors have constant term 2.  After clearing the
# positive powers of p, the strengthened gaps are a positive factor times C_H.
fisher_c_polynomials = {
    153: (
        -15309 * y**10
        + 25515 * y**9
        - 7614 * y**8
        - 5832 * y**7
        - 702 * y**6
        + 4266 * y**5
        - 1524 * y**4
        + 248 * y**3
        - 69 * y**2
        - 5 * y
        + 2
    ),
    171: (
        -1948617 * y**14
        + 649539 * y**13
        + 1968300 * y**12
        - 354294 * y**11
        - 923643 * y**10
        + 21141 * y**9
        + 83106 * y**8
        + 173988 * y**7
        - 64071 * y**6
        + 4437 * y**5
        - 2640 * y**4
        - 494 * y**3
        + 11 * y**2
        + 19 * y
        + 2
    ),
    174: (
        -2302911 * y**14
        + 767637 * y**13
        + 2165130 * y**12
        - 472392 * y**11
        - 949887 * y**10
        + 82377 * y**9
        + 86022 * y**8
        + 161352 * y**7
        - 63261 * y**6
        + 6039 * y**5
        - 3282 * y**4
        - 1024 * y**3
        - 101 * y**2
        + 11 * y
        + 2
    ),
    188: (
        -3011499 * y**14
        + 1003833 * y**13
        + 2794986 * y**12
        - 629856 * y**11
        - 1159839 * y**10
        + 152361 * y**9
        + 126846 * y**8
        + 136080 * y**7
        - 75249 * y**6
        + 8595 * y**5
        - 1002 * y**4
        - 560 * y**3
        - 69 * y**2
        + 11 * y
        + 2
    ),
}

for atlas_id, c_poly in fisher_c_polynomials.items():
    target_y = sp.expand(
        p_y * (2 * p_y - 1) * q_polynomials[atlas_id].subs(p, p_y)
    )
    if atlas_id == 153:
        cleared_gap = sp.expand(g_y**4 - p_y**2 * target_y)
        expected = y * (1 - y) ** 3 * c_poly / 64
    else:
        cleared_gap = sp.expand(g_y**6 - p_y**6 * target_y)
        expected = y * (1 - y) ** 7 * c_poly / 1024
    assert sp.expand(cleared_gap - expected) == 0


# Sturm's theorem: C_H has exactly one zero on the whole Fisher parameter
# interval (0,1/3).  The variations are evaluated with exact rationals.
expected_sturm_variations = {
    153: (6, 5),
    171: (8, 7),
    174: (8, 7),
    188: (8, 7),
}
for atlas_id, c_poly in fisher_c_polynomials.items():
    sequence = sp.sturm(c_poly, y)
    variation_zero = sign_variations([term.subs(y, 0) for term in sequence])
    variation_third = sign_variations(
        [term.subs(y, sp.Rational(1, 3)) for term in sequence]
    )
    assert (variation_zero, variation_third) == expected_sturm_variations[atlas_id]
    assert sp.count_roots(c_poly, 0, sp.Rational(1, 3)) == 1
    assert c_poly.subs(y, 0) == 2


# Exact finite-decimal isolating brackets for the Fisher parameter and the
# corresponding density endpoint.  All comparisons below are Fraction-only.
fisher_brackets = {
    153: {
        "y": ("0.1534486672074800", "0.1534486672074801"),
        "p": ("0.6181289270058", "0.6181289270059"),
    },
    171: {
        "y": ("0.1790286678151776", "0.1790286678151777"),
        "p": ("0.6309517719656", "0.6309517719657"),
    },
    174: {
        "y": ("0.1124274870396899", "0.1124274870396900"),
        "p": ("0.5934675772766", "0.5934675772767"),
    },
    188: {
        "y": ("0.1459379567956481", "0.1459379567956482"),
        "p": ("0.6139911259451", "0.6139911259452"),
    },
}


def fisher_density(parameter):
    return (1 - parameter) * (1 + 3 * parameter) / 2


for atlas_id, data in fisher_brackets.items():
    y_left_text, y_right_text = data["y"]
    p_left_text, p_right_text = data["p"]
    y_left, y_right = Fraction(y_left_text), Fraction(y_right_text)
    p_left, p_right = Fraction(p_left_text), Fraction(p_right_text)
    coefficients = [
        int(coefficient)
        for coefficient in sp.Poly(fisher_c_polynomials[atlas_id], y).all_coeffs()
    ]
    c_left = eval_fraction(coefficients, y_left)
    c_right = eval_fraction(coefficients, y_right)
    assert c_left > 0 > c_right
    assert p_left < fisher_density(y_left)
    assert fisher_density(y_right) < p_right
    midpoint_coverage = 200 * (float((p_left + p_right) / 2) - 0.5)
    print(
        f"Atlas {atlas_id} Fisher: {y_left_text} < eta < {y_right_text}; "
        f"{p_left_text} < beta < {p_right_text}; "
        f"C(left)>0>C(right); coverage~{midpoint_coverage:.6f}%"
    )

print("All self-amalgam, Fisher/Sturm, polynomial, and endpoint checks passed.")
