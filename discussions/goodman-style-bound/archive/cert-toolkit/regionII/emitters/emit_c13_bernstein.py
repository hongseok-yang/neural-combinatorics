#!/usr/bin/env python3
"""Emit exact C13 Bernstein coefficient payloads for Lean.

This script proves nothing.  It rebuilds the C13 path kernels with SymPy,
performs exact rational Bernstein conversion/subdivision, and serializes only
the boxes and coefficients.  Lean checks coefficient signs and proves every
identity with the formal kernel definitions.
"""
from __future__ import annotations

from itertools import product
from pathlib import Path
import sys

sys.dont_write_bytecode = True

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOT = ROOT.parent
sys.path.insert(0, str(SOURCE_ROOT))

import odd_cycle_c13_checker as oc  # noqa: E402
import c13_frontier_certificate_search as frontier  # noqa: E402

OUTPUT = ROOT / "OddCycleBound" / "RegionII" / "Certificate" / "C13Generated.lean"


def rational(value) -> sp.Rational:
    value = sp.factor(value)
    if not value.is_Rational:
        raise TypeError(f"expected a rational, got {value}")
    return sp.Rational(value)


def lean_rat(value) -> str:
    value = rational(value)
    num, den = int(value.p), int(value.q)
    if den == 1:
        return str(num)
    if num < 0:
        return f"(-{-num} / {den})"
    return f"({num} / {den})"


def lean_raw_rat(value) -> str:
    value = rational(value)
    return f"⟨{int(value.p)}, {int(value.q)}⟩"


def bernstein_coefficients(poly, variables, bounds):
    unit = sp.symbols(f"z0:{len(variables)}")
    substituted = sp.expand(poly.subs({
        variable: lo + (hi - lo) * z
        for variable, z, (lo, hi) in zip(variables, unit, bounds)
    }))
    power = sp.Poly(substituted, *unit)
    degrees = tuple(power.degree(z) for z in unit)
    coefficients = dict(power.terms())
    result = []
    for beta in product(*[range(degree + 1) for degree in degrees]):
        value = sp.Rational(0)
        for alpha in product(*[range(index + 1) for index in beta]):
            coefficient = coefficients.get(alpha)
            if coefficient is None:
                continue
            factor = sp.prod(
                sp.Rational(sp.binomial(index, exponent), sp.binomial(degree, exponent))
                for index, exponent, degree in zip(beta, alpha, degrees)
            )
            value += coefficient * factor
        result.append((beta, rational(value)))
    return degrees, result


def staged_cube_coefficients(poly, variables, bounds):
    """Power coefficients and the three successive degree-eight transforms."""
    unit = sp.symbols("z0:3")
    substituted = sp.expand(poly.subs({
        variable: lo + (hi - lo) * z
        for variable, z, (lo, hi) in zip(variables, unit, bounds)
    }))
    power_poly = sp.Poly(substituted, *unit)
    if tuple(power_poly.degree(z) for z in unit) != (8, 8, 8):
        raise RuntimeError("expected a degree-(8,8,8) quadratic cube")
    sparse = dict(power_poly.terms())
    power = [[[rational(sparse.get((i, j, k), 0)) for k in range(9)]
              for j in range(9)] for i in range(9)]

    def ratio(a, b):
        return sp.Rational(sp.binomial(b, a), sp.binomial(8, a))

    stage_two = [[[rational(sum(power[i][j][a] * ratio(a, b) for a in range(9)))
                   for b in range(9)] for j in range(9)] for i in range(9)]
    stage_one = [[[rational(sum(stage_two[i][a][k] * ratio(a, b) for a in range(9)))
                   for k in range(9)] for b in range(9)] for i in range(9)]
    bernstein = [[[rational(sum(stage_one[a][j][k] * ratio(a, b) for a in range(9)))
                   for k in range(9)] for j in range(9)] for b in range(9)]
    flatten = lambda tensor: [tensor[i][j][k]
                              for i in range(9) for j in range(9) for k in range(9)]
    return tuple(map(flatten, (power, stage_two, stage_one, bernstein)))


def subdivide(poly, variables, initial_bounds):
    pending = [tuple(initial_bounds)]
    leaves = []
    while pending:
        bounds = pending.pop()
        degrees, coefficients = bernstein_coefficients(poly, variables, bounds)
        if min(value for _, value in coefficients) > 0:
            leaves.append((bounds, degrees, coefficients))
            continue
        lengths = [hi - lo for lo, hi in bounds]
        coordinate = max(range(len(bounds)), key=lambda i: lengths[i])
        lo, hi = bounds[coordinate]
        midpoint = (lo + hi) / 2
        left, right = list(bounds), list(bounds)
        left[coordinate] = (lo, midpoint)
        right[coordinate] = (midpoint, hi)
        pending.extend((tuple(left), tuple(right)))
    return leaves


def c13_pieces():
    q, lam, linear, x, y, quadratic = frontier.build_c13_pieces()

    n = 13
    q0, moments, paths = oc.path_formulae(n - 1)
    target = (1 - q0) ** n - (1 - q0) * q0 ** (n - 1)
    phi = sp.expand(oc.expression_from_counts(n, q0, paths) - target)
    moment_variables = [moments[j] for j in range(n - 2)]
    phi_poly = sp.Poly(phi, *moment_variables)
    homogeneous = []
    for degree in range(7):
        part = sum(
            coefficient * sp.prod(v ** exponent for v, exponent in zip(moment_variables, monomial))
            for monomial, coefficient in phi_poly.terms()
            if sum(monomial) == degree
        )
        homogeneous.append(sp.expand(part))
    abstract_moments = sp.symbols(f"m0:{n - 1}")
    substitution = {moments[0]: 1}
    substitution.update({moments[j]: abstract_moments[j] for j in range(1, n - 2)})
    normalized = [sp.expand(part.subs(substitution)) for part in homogeneous]
    diagonal = {}
    ell = sp.symbols("ell")
    for degree in (3, 4, 5):
        kernel, eigenvalues = oc.kernel_for(normalized[degree], degree, abstract_moments)
        diagonal[degree] = sp.expand(kernel.subs({eigenvalue: ell for eigenvalue in eigenvalues}))
    return q, lam, linear, x, y, quadratic, ell, diagonal


def emit_certificate(name, bounds, degrees, coefficients):
    lines = [f"def {name} : BernsteinCertificate {len(degrees)} := {{",
             f"  degree := ![{', '.join(map(str, degrees))}]",
             "  terms := ["]
    for index, coefficient in coefficients:
        lines.append(
            f"    {{ index := ![{', '.join(map(str, index))}], "
            f"coefficient := {lean_rat(coefficient)} }},")
    lines.extend(["  ]", "}", ""])
    lines.append(f"def {name}Lower : Fin {len(degrees)} → ℚ := "
                 f"![{', '.join(lean_rat(lo) for lo, _ in bounds)}]")
    lines.append(f"def {name}Upper : Fin {len(degrees)} → ℚ := "
                 f"![{', '.join(lean_rat(hi) for _, hi in bounds)}]")
    lines.append("")
    lines.extend([
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        f"theorem {name}_checked : {name}.check = true := by decide +kernel",
    ])
    lines.append("")
    return "\n".join(lines)


def emit_cube(name, arrays):
    field_names = ("power", "stageTwo", "stageOne", "bernstein")
    lines = []
    for field, values in zip(field_names, arrays):
        array_name = f"{name}{field[0].upper()}{field[1:]}"
        lines.append(f"def {array_name} (i j k : Fin 9) : RationalDatum :=")
        lines.append("  match i.1 with")
        for i in range(9):
            lines.append(f"  | {i} => match j.1 with")
            for j in range(9):
                lines.append(f"    | {j} => match k.1 with")
                for k in range(9):
                    lines.append(f"      | {k} => {lean_raw_rat(values[(i * 9 + j) * 9 + k])}")
                lines.append("      | _ => default")
            lines.append("    | _ => default")
        lines.extend(["  | _ => default", ""])
    lines.extend([
        f"def {name} : BernsteinCube8Data := {{",
        f"  power := {name}Power",
        f"  stageTwo := {name}StageTwo",
        f"  stageOne := {name}StageOne",
        f"  bernstein := {name}Bernstein",
        "}", "",
    ])
    lines.extend([
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        f"theorem {name}_checked :",
        f"    (∀ i j k : Fin 9, cubeCoefficient {name}.stageTwo i j k =",
        f"      ∑ a : Fin 9, cubeCoefficient {name}.power i j a *",
        "        ratBernsteinRatio 8 a k) ∧",
        f"    (∀ i j k : Fin 9, cubeCoefficient {name}.stageOne i j k =",
        f"      ∑ a : Fin 9, cubeCoefficient {name}.stageTwo i a k *",
        "        ratBernsteinRatio 8 a j) ∧",
        f"    (∀ i j k : Fin 9, cubeCoefficient {name}.bernstein i j k =",
        f"      ∑ a : Fin 9, cubeCoefficient {name}.stageOne a j k *",
        "        ratBernsteinRatio 8 a i) ∧",
        f"    (∀ i j k : Fin 9, 0 ≤ cubeCoefficient {name}.bernstein i j k) := by",
        "  decide +kernel",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    q, lam, linear, x, y, quadratic, ell, diagonal = c13_pieces()
    t = sp.symbols("t")
    qlo, qhi = sp.Rational(481, 1000), sp.Rational(49, 100)
    safe_lo, safe_hi = -sp.Rational(1, 2), sp.Rational(7, 50)
    alpha = q + (sp.Rational(1, 2) - q) * t

    frontier_cases = [
        ("c13LinearSafeCertificate", linear, (q, lam), ((qlo, qhi), (safe_lo, safe_hi))),
        ("c13LinearFrontierCertificate", sp.expand(linear.subs(lam, alpha)),
         (q, t), ((qlo, qhi), (sp.Rational(0), sp.Rational(1)))),
        ("c13QuadraticSafeSafeCertificate", quadratic, (q, x, y),
         ((qlo, qhi), (safe_lo, safe_hi), (safe_lo, safe_hi))),
        ("c13QuadraticFrontierSafeCertificate", sp.expand(quadratic.subs(x, alpha)),
         (q, t, y), ((qlo, qhi), (sp.Rational(0), sp.Rational(1)), (safe_lo, safe_hi))),
        ("c13QuadraticFrontierFrontierCertificate",
         sp.expand(quadratic.subs({x: alpha, y: alpha})),
         (q, t), ((qlo, qhi), (sp.Rational(0), sp.Rational(1)))),
    ]

    emitted = []
    summaries = []
    for name, polynomial, variables, bounds in frontier_cases:
        degrees, coefficients = bernstein_coefficients(polynomial, variables, bounds)
        minimum = min(value for _, value in coefficients)
        if minimum <= 0:
            raise RuntimeError(f"{name} failed: minimum coefficient {minimum}")
        emitted.append(emit_certificate(name, bounds, degrees, coefficients))
        summaries.append(f"{name}: 1 box, minimum {minimum}")

        if name in ("c13QuadraticSafeSafeCertificate",
                    "c13QuadraticFrontierSafeCertificate"):
            emitted.append(emit_cube(name.replace("Certificate", "Cube"),
                                     staged_cube_coefficients(polynomial, variables, bounds)))

    diagonal_counts = {}
    for degree in (3, 4, 5):
        leaves = subdivide(diagonal[degree], (q, ell),
                           ((sp.Rational(0), sp.Rational(1, 2)),
                            (-sp.Rational(1, 2), sp.Rational(1, 2))))
        diagonal_counts[degree] = len(leaves)
        for index, (bounds, degrees, coefficients) in enumerate(leaves):
            name = f"c13Diagonal{degree}Certificate{index}"
            emitted.append(emit_certificate(name, bounds, degrees, coefficients))
        summaries.append(f"C13 diagonal K{degree}: {len(leaves)} boxes")

    if diagonal_counts != {3: 2, 4: 2, 5: 3}:
        raise RuntimeError(f"diagonal subdivision regression: {diagonal_counts}")

    text = """import OddCycleBound.RegionII.Certificate.BernsteinCube

/-! Deterministically generated by `cert_scripts/regionII/emit_c13_bernstein.py`. -/

namespace OddCycleBound.RegionII.Certificate

""" + "\n".join(emitted) + "\nend OddCycleBound.RegionII.Certificate\n"
    OUTPUT.write_text(text, encoding="utf-8", newline="\n")
    print("\n".join(summaries))
    print(f"wrote {OUTPUT}")


if __name__ == "__main__":
    main()
