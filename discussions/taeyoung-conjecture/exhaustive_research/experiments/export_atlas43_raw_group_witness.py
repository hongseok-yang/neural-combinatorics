"""Export integer-scaled exceptional witnesses for the Atlas-43 raw groups.

The exact certificate has only 81 correction entries whose denominators do
not divide the common denominator.  Lean previously summed the corresponding
dense 107x107 and 48x48 matrices in one reduction.  This derived witness
records one common integer denominator per block and the corresponding exact
group totals.  Lean therefore checks large integer sums instead of repeatedly
normalizing enormous intermediate rational fractions.
"""

from __future__ import annotations

import argparse
import functools
import json
import math
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from rooted_sos_search import fixed_density_key, rooted_basis, rooted_product


def exceptional_matrix(certificate: dict, block: int) -> list[list[Fraction]]:
    order = certificate["orders"][block]
    result = [[Fraction(0) for _ in range(order)] for _ in range(order)]
    common_denominator = 10**12
    for entry_block, i, j, numerator, denominator in certificate["corrections"]:
        if entry_block != block or common_denominator % denominator == 0:
            continue
        value = Fraction(numerator, denominator)
        result[i][j] = value
        result[j][i] = value
    return result


def exceptional_total(
    factor: list[list[int]],
    exceptional: list[list[Fraction]],
    pairs: list[tuple[int, int]],
    coordinates,
) -> Fraction:
    total = Fraction(0)
    for i, matrix_row in enumerate(exceptional):
        for a, b in pairs:
            row, column = coordinates(a, b)
            total += factor[row][i] * sum(
                value * factor[column][j]
                for j, value in enumerate(matrix_row)
                if value
            )
    return total


def symmetric_pair_weight(
    factor: list[list[int]],
    pairs: list[tuple[int, int]],
    i: int,
    j: int,
    coordinates,
) -> int:
    result = 0
    for a, b in pairs:
        row, column = coordinates(a, b)
        result += factor[row][i] * factor[column][j]
        if i != j:
            result += factor[row][j] * factor[column][i]
    return result


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
        default="experiments/house_atlas43_raw_group_witness.json",
    )
    args = parser.parse_args()

    certificate = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    factors = [certificate["F0"], certificate["F1"]]
    exceptional = [
        exceptional_matrix(certificate, 0),
        exceptional_matrix(certificate, 1),
    ]
    common_denominator = 10**12
    denominators = [
        [
            denominator
            for entry_block, _i, _j, _numerator, denominator
            in certificate["corrections"]
            if entry_block == block and common_denominator % denominator != 0
        ]
        for block in (0, 1)
    ]
    exceptional_denominators = [
        functools.reduce(math.lcm, values, 1) for values in denominators
    ]
    scaled_entries = [[], []]
    for block, i, j, numerator, denominator in certificate["corrections"]:
        if common_denominator % denominator == 0:
            continue
        scaled_entries[block].append([
            i,
            j,
            numerator * (exceptional_denominators[block] // denominator),
        ])

    basis = rooted_basis(3, 1)
    groups: dict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    for a, left in enumerate(basis):
        for b, right in enumerate(basis):
            key = fixed_density_key(rooted_product(left, right, 3, 1))
            groups[key].append((a, b))

    sorted_groups = sorted(groups.items())
    group_index = [[0 for _ in range(64)] for _ in range(64)]
    for row, (_key, pairs) in enumerate(sorted_groups):
        for a, b in pairs:
            group_index[a][b] = row

    scaled_totals = []
    keys = []
    pair_weights0 = [[[] for _slot in range(3)] for _entry in scaled_entries[0]]
    pair_weights1 = [[] for _entry in scaled_entries[1]]
    for key, pairs in sorted_groups:
        keys.append(list(key))
        totals = [
            exceptional_total(
                factors[0], exceptional[0], pairs,
                lambda a, b: (a, b),
            ),
            exceptional_total(
                factors[0], exceptional[0], pairs,
                lambda a, b: (a, 64 + b),
            ),
            exceptional_total(
                factors[0], exceptional[0], pairs,
                lambda a, b: (64 + a, 64 + b),
            ),
            exceptional_total(
                factors[1], exceptional[1], pairs,
                lambda a, b: (a, b),
            ),
        ]
        scaled = []
        for slot, total in enumerate(totals):
            denominator = exceptional_denominators[0 if slot < 3 else 1]
            value = total * denominator
            if value.denominator != 1:
                raise AssertionError((key, slot, value.denominator))
            scaled.append(value.numerator)
        scaled_totals.append(scaled)
        coordinates0 = [
            lambda a, b: (a, b),
            lambda a, b: (a, 64 + b),
            lambda a, b: (64 + a, 64 + b),
        ]
        for entry_index, (i, j, _value) in enumerate(scaled_entries[0]):
            for slot, coordinates in enumerate(coordinates0):
                pair_weights0[entry_index][slot].append(
                    symmetric_pair_weight(factors[0], pairs, i, j, coordinates)
                )
        for entry_index, (i, j, _value) in enumerate(scaled_entries[1]):
            pair_weights1[entry_index].append(
                symmetric_pair_weight(
                    factors[1], pairs, i, j, lambda a, b: (a, b)
                )
            )

    output = {
        "raw_group_keys": keys,
        "raw_group_index": group_index,
        "pair_weight_bound0": 2 * 4096 * max(
            abs(value) for row in factors[0] for value in row
        ) ** 2,
        "pair_weight_bound1": 2 * 4096 * max(
            abs(value) for row in factors[1] for value in row
        ) ** 2,
        "exceptional_denominator0": exceptional_denominators[0],
        "exceptional_denominator1": exceptional_denominators[1],
        "exceptional_scaled_entries0": scaled_entries[0],
        "exceptional_scaled_entries1": scaled_entries[1],
        "exceptional_pair_weights0": pair_weights0,
        "exceptional_pair_weights1": pair_weights1,
        "exceptional_scaled_group_totals": scaled_totals,
    }
    Path(args.output).write_text(
        json.dumps(output, separators=(",", ":")) + "\n", encoding="utf-8"
    )

    nonzero0 = sum(
        1 for row in exceptional[0] for value in row if value
    )
    nonzero1 = sum(
        1 for row in exceptional[1] for value in row if value
    )
    print(
        f"groups={len(keys)} denominator_bits="
        f"({exceptional_denominators[0].bit_length()},"
        f"{exceptional_denominators[1].bit_length()}) "
        f"directed_exceptionals=({nonzero0},{nonzero1})"
    )


if __name__ == "__main__":
    main()
