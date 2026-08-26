"""Export a multiplication witness for the Atlas-43 rational Gram matrices.

The mathematical certificate remains ``house_atlas43_rational.json``.  This
derived file merely lets Lean check the two matrix products in stages:

    K = F (I + C),       G = K F^T.

All entries are exact reduced fractions.  To avoid spreading the few enormous
denominators produced by the exact linear solve through every matrix entry,
this witness includes only corrections whose denominator divides ``10^12``.
Lean checks those products entrywise and handles the remaining 81 correction
entries directly in the final coefficient audit.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from rooted_sos_search import fixed_density_key, rooted_basis, rooted_product


def fraction_pair(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def scaled_integer(value: Fraction, denominator: int) -> int:
    scaled = value * denominator
    if scaled.denominator != 1:
        raise AssertionError((value, denominator))
    return scaled.numerator


def block_witness(
    factor: list[list[int]], correction: list[list[Fraction]], denominator: int
):
    rows = len(factor)
    order = len(correction)

    intermediate = []
    for row in factor:
        intermediate.append(
            [
                Fraction(row[j])
                + sum(Fraction(row[i]) * correction[i][j] for i in range(order))
                for j in range(order)
            ]
        )

    # Only the upper triangle is stored.  The checked correction matrix is
    # symmetric, hence so is F (I + C) F^T.
    gram_upper = []
    for a in range(rows):
        gram_upper.append(
            [
                sum(intermediate[a][j] * factor[b][j] for j in range(order))
                for b in range(a, rows)
            ]
        )

    return (
        [[scaled_integer(value, denominator) for value in row] for row in intermediate],
        [[scaled_integer(value, denominator) for value in row] for row in gram_upper],
        gram_upper,
    )


def upper_entry(matrix, a: int, b: int) -> Fraction:
    return matrix[a][b - a] if a <= b else matrix[b][a - b]


def exceptional_entry(
    factor: list[list[int]], exceptional: list[tuple[int, int, Fraction]], a: int, b: int
) -> Fraction:
    total = Fraction(0)
    for i, j, value in exceptional:
        if i == j:
            total += value * factor[a][i] * factor[b][i]
        else:
            total += value * (
                factor[a][i] * factor[b][j] + factor[a][j] * factor[b][i]
            )
    return total


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "certificate",
        nargs="?",
        default="experiments/house_atlas43_rational.json",
    )
    parser.add_argument(
        "output",
        nargs="?",
        default="experiments/house_atlas43_lean_gram.json",
    )
    args = parser.parse_args()

    certificate = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    factors = [certificate["F0"], certificate["F1"]]
    orders = certificate["orders"]
    common_denominator = 10**12
    corrections = [
        [[Fraction(0) for _ in range(order)] for _ in range(order)]
        for order in orders
    ]
    exceptional = [[], []]
    for block, i, j, numerator, denominator in certificate["corrections"]:
        if common_denominator % denominator != 0:
            exceptional[block].append((i, j, Fraction(numerator, denominator)))
            continue
        value = Fraction(numerator, denominator)
        corrections[block][i][j] = value
        corrections[block][j][i] = value

    output = {
        "source_factor_denominator": certificate["factor_denominator"],
        "common_correction_denominator": common_denominator,
    }
    common_grams = []
    for block, (factor, correction) in enumerate(zip(factors, corrections)):
        correction_upper_scaled = [
            [scaled_integer(correction[i][j], common_denominator)
             for j in range(i, len(correction))]
            for i in range(len(correction))
        ]
        intermediate, gram_upper, common_gram = block_witness(
            factor, correction, common_denominator
        )
        output[f"C{block}_common_scaled_upper"] = correction_upper_scaled
        output[f"K{block}_scaled"] = intermediate
        output[f"G{block}_scaled_upper"] = gram_upper
        factor_bound = max(abs(value) for row in factor for value in row)
        correction_bound = max(
            abs(value) for row in correction_upper_scaled for value in row
        )
        intermediate_bound = (
            common_denominator * factor_bound
            + len(correction) * factor_bound * correction_bound
        )
        gram_bound = len(correction) * intermediate_bound * factor_bound
        intermediate_base = 2 * intermediate_bound + 1
        gram_base = 2 * gram_bound + 1
        output[f"factor{block}_bound"] = factor_bound
        output[f"common_correction{block}_scaled_bound"] = correction_bound
        output[f"intermediate{block}_bound"] = intermediate_bound
        output[f"gram{block}_bound"] = gram_bound
        output[f"common_correction{block}_encoded_rows"] = [
            sum(
                scaled_integer(correction[i][j], common_denominator)
                * intermediate_base**j
                for j in range(len(correction))
            )
            for i in range(len(correction))
        ]
        output[f"factor{block}_gram_encoded_columns"] = [
            sum(factor[a][j] * gram_base**a for a in range(len(factor)))
            for j in range(len(correction))
        ]
        common_grams.append(common_gram)

    basis = rooted_basis(3, 1)
    groups: dict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    for a, left in enumerate(basis):
        for b, right in enumerate(basis):
            groups[fixed_density_key(rooted_product(left, right, 3, 1))].append((a, b))

    raw_group_keys = []
    raw_group_totals = []
    for (core, isolated), pairs in sorted(groups.items()):
        totals = [Fraction(0) for _ in range(4)]
        for a, b in pairs:
            coordinates = ((a, b), (a, 64 + b), (64 + a, 64 + b))
            for slot, (row, column) in enumerate(coordinates):
                totals[slot] += upper_entry(common_grams[0], row, column)
                totals[slot] += exceptional_entry(factors[0], exceptional[0], row, column)
            totals[3] += upper_entry(common_grams[1], a, b)
            totals[3] += exceptional_entry(factors[1], exceptional[1], a, b)
        raw_group_keys.append([core, isolated])
        raw_group_totals.append(list(map(fraction_pair, totals)))
    output["raw_group_keys"] = raw_group_keys
    output["raw_group_totals"] = raw_group_totals

    Path(args.output).write_text(
        json.dumps(output, separators=(",", ":")) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
