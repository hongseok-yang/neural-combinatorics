"""Build a bounded-arithmetic Lean witness for one exact S4 certificate.

The source JSON remains the mathematical certificate.  This derived witness
splits each correction into a dense fixed-denominator part and a short exact
exceptional part, records the two staged products

    K = F (I + C_common),   G_common = K F^T,

and records the four aggregate coefficients of every fixed-density raw graph
group.  Lean checks all staged products and aggregates independently.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from fractions import Fraction
from math import lcm
from pathlib import Path

import numpy as np
import networkx as nx
import sympy as sp
from flint import fmpq, fmpq_mat, fmpz_mat
from networkx.algorithms.polynomials import chromatic_polynomial

from full_s4_interval_sos import raw_by_isolated
from full_s4_rooted_sos import rooted_basis_indices
from rooted_sos_search import fixed_density_key


FINE_SIDECAR_MAX_BYTES = 32_000


def common_correction_denominator(certificate: dict) -> int:
    """Return the rounding denominator used by the rationalizer.

    New certificates record it explicitly.  Older committed certificates do
    not, but their dense preliminary correction makes the unreduced rounding
    denominator the most frequent exact denominator.  Refuse an ambiguous
    inference instead of silently turning almost the whole matrix into the
    exceptional layer.
    """
    explicit = certificate.get("correction_denominator")
    if explicit is not None:
        denominator = int(explicit)
    else:
        denominators = [
            int(entry[4]) for entry in certificate["corrections"]
            if int(entry[3]) != 0
        ]
        if not denominators:
            return 1
        denominator, _ = Counter(denominators).most_common(1)[0]
    if denominator <= 0:
        raise AssertionError("correction denominator must be positive")
    compatible = sum(
        denominator % int(entry[4]) == 0
        for entry in certificate["corrections"]
    )
    if 10 * compatible < 9 * len(certificate["corrections"]):
        raise AssertionError(
            f"ambiguous correction denominator {denominator}: "
            f"only {compatible}/{len(certificate['corrections'])} entries divide it"
        )
    return denominator


def fraction_pair(value: fmpq | Fraction) -> list[int]:
    return [int(value.numerator), int(value.denominator)]


def upper_entry(matrix: fmpq_mat, i: int, j: int) -> fmpq:
    return matrix[i, j]


def sympy_fraction(value: sp.Expr) -> Fraction:
    rational = sp.Rational(value)
    return Fraction(int(rational.p), int(rational.q))


def polynomial_coefficients(expression: sp.Expr, variable: sp.Symbol, degree: int) -> list[Fraction]:
    polynomial = sp.Poly(sp.expand(expression), variable, domain=sp.QQ)
    return [sympy_fraction(polynomial.nth(power)) for power in range(degree + 1)]


def compact_json(payload: object) -> str:
    return json.dumps(payload, separators=(",", ":")) + "\n"


def write_if_changed(path: Path, contents: str) -> None:
    """Preserve mtimes of unchanged Lean sidecars and their compiled users."""
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def write_sequence_chunks(
    output: Path,
    label: str,
    length: int,
    payload_for_slice,
    max_bytes: int = FINE_SIDECAR_MAX_BYTES,
) -> list[dict[str, object]]:
    """Write contiguous outer-array slices below a Lean-friendly size cap."""
    chunks: list[dict[str, object]] = []
    start = 0
    while start < length:
        stop = start + 1
        while stop < length:
            candidate = compact_json(payload_for_slice(start, stop + 1))
            if len(candidate.encode("utf-8")) > max_bytes:
                break
            stop += 1
        payload = payload_for_slice(start, stop)
        contents = compact_json(payload)
        path = output.with_name(
            f"{output.stem}_{label}_{start:03d}_{stop - 1:03d}{output.suffix}"
        )
        write_if_changed(path, contents)
        chunks.append({
            "file": path.name,
            "start": start,
            "stop": stop,
            "bytes": path.stat().st_size,
        })
        start = stop
    return chunks


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument("output")
    args = parser.parse_args()

    sys.set_int_max_str_digits(0)
    certificate_path = Path(args.certificate)
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    if int(certificate.get("polynomial_degree") or 2) != 2:
        raise AssertionError("Lean exporter currently expects polynomial degree two")

    names = certificate["names"]
    if names != ["4", "31", "22", "211", "1111"]:
        raise AssertionError(names)
    symmetry_factors = [24] * 5
    basis_indices = rooted_basis_indices(2, "all")
    if basis_indices != list(map(int, certificate["basis_indices"])):
        raise AssertionError("wrong raw basis")
    # Use the exact integer slices stored in the certificate.  Floating QR can
    # select different pivot columns on different numerical-library builds;
    # the resulting bases are equivalent but must not be mixed with the
    # certificate's factor and correction matrices.
    transforms = [
        np.asarray(certificate["young_bases"][name], dtype=np.int64)
        for name in names
    ]

    factors = [[list(map(int, row)) for row in block] for block in certificate["factors"]]
    orders = list(map(int, certificate["orders"]))
    corrections = [
        [[Fraction(0) for _ in range(order)] for _ in range(order)]
        for order in orders
    ]
    for block, i, j, numerator, denominator in certificate["corrections"]:
        value = Fraction(int(numerator), int(denominator))
        corrections[int(block)][int(i)][int(j)] = value
        corrections[int(block)][int(j)][int(i)] = value
    common_denominator = common_correction_denominator(certificate)

    raw_groups = raw_by_isolated(basis_indices)
    group_keys = sorted(raw_groups)
    pulled_groups = []
    for key in group_keys:
        raw = raw_groups[key]
        pulled_groups.append([
            np.asarray(transform.T @ raw @ transform, dtype=np.int64)
            for transform in transforms
        ])

    common_upper = []
    intermediates = []
    common_gram_upper = []
    common_grams: list[fmpq_mat] = []
    exceptional = []
    factor_bounds = []
    correction_bounds = []
    intermediate_bounds = []
    gram_bounds = []
    for block, (factor, correction, order) in enumerate(zip(factors, corrections, orders)):
        common = [[Fraction(0) for _ in range(order)] for _ in range(order)]
        block_exceptional = []
        for i in range(order):
            for j in range(i, order):
                value = correction[i][j]
                if common_denominator % value.denominator == 0:
                    common[i][j] = common[j][i] = value
                elif value:
                    block_exceptional.append([i, j, value.numerator, value.denominator])
        exceptional.append(block_exceptional)
        scaled_upper = [[
            int(common[i][j] * common_denominator)
            for j in range(i, order)
        ] for i in range(order)]
        common_upper.append(scaled_upper)

        factor_q = fmpq_mat([[fmpq(value) for value in row] for row in factor])
        z = fmpq_mat(order, order)
        for i in range(order):
            for j in range(order):
                z[i, j] = fmpq(common[i][j].numerator, common[i][j].denominator)
            z[i, i] += 1
        intermediate = factor_q * z
        gram = intermediate * factor_q.transpose()
        common_grams.append(gram)
        intermediates.append([
            [int(intermediate[i, j] * common_denominator)
             for j in range(order)]
            for i in range(intermediate.nrows())
        ])
        common_gram_upper.append([
            [int(gram[i, j] * common_denominator)
             for j in range(i, gram.ncols())]
            for i in range(gram.nrows())
        ])

        factor_bound = max(abs(value) for row in factor for value in row)
        correction_bound = max(abs(value) for row in scaled_upper for value in row)
        intermediate_bound = (
            common_denominator * factor_bound
            + order * factor_bound * correction_bound
        )
        gram_bound = order * intermediate_bound * factor_bound
        factor_bounds.append(factor_bound)
        correction_bounds.append(correction_bound)
        intermediate_bounds.append(intermediate_bound)
        gram_bounds.append(gram_bound)

    # Exact full Gram matrices are used only transiently to construct the
    # compact claimed group totals.
    full_grams = []
    for factor, correction, order in zip(factors, corrections, orders):
        factor_q = fmpq_mat([[fmpq(value) for value in row] for row in factor])
        z = fmpq_mat(order, order)
        for i in range(order):
            for j in range(order):
                value = correction[i][j]
                z[i, j] = fmpq(value.numerator, value.denominator)
            z[i, i] += 1
        full_grams.append(factor_q * z * factor_q.transpose())

    group_totals = []
    common_group_totals = []
    group_totals_q: list[list[fmpq]] = []
    for pulled in pulled_groups:
        totals = [fmpq(0) for _ in range(4)]
        common_totals = [fmpq(0) for _ in range(4)]
        for block in range(5):
            size = transforms[block].shape[1]
            matrix = pulled[block]
            gram0 = full_grams[block]
            gram1 = full_grams[block + 5]
            common0 = common_grams[block]
            common1 = common_grams[block + 5]
            for i, j in zip(*np.nonzero(matrix)):
                coefficient = int(matrix[i, j]) * 24
                totals[0] += coefficient * upper_entry(gram0, i, j)
                totals[1] += coefficient * (
                    upper_entry(gram0, i, size + j)
                    + upper_entry(gram0, size + i, j)
                )
                totals[2] += coefficient * upper_entry(gram0, size + i, size + j)
                totals[3] += coefficient * upper_entry(gram1, i, j)
                common_totals[0] += coefficient * upper_entry(common0, i, j)
                common_totals[1] += coefficient * (
                    upper_entry(common0, i, size + j)
                    + upper_entry(common0, size + i, j)
                )
                common_totals[2] += coefficient * upper_entry(common0, size + i, size + j)
                common_totals[3] += coefficient * upper_entry(common1, i, j)
        group_totals_q.append(totals)
        group_totals.append(list(map(fraction_pair, totals)))
        common_group_totals.append(list(map(fraction_pair, common_totals)))

    # Compress the final interval-polynomial identity to small exact equations
    # in the four group totals.  This is independent of the expensive matrix
    # reconstruction: Lean can first check each group total, then check these
    # sparse coefficient rows one at a time.
    left, right = map(sp.Rational, certificate["interval"])
    t = sp.symbols("t")
    p = left + (right - left) * t
    max_isolated = max(isolated for _, isolated in group_keys)
    max_power = max(5, max_isolated + 2)
    density_coefficients = {
        isolated: polynomial_coefficients(p**isolated, t, max_power)
        for isolated in range(max_isolated + 1)
    }
    graph = nx.graph_atlas(int(certificate["atlas"]))
    target_core, target_isolated = fixed_density_key(graph)
    if target_isolated:
        raise AssertionError("S4 interval target must be connected")
    chromatic = chromatic_polynomial(graph)
    chromatic_variable = next(iter(chromatic.free_symbols))
    phi = sp.factor(
        (1 - p) ** graph.number_of_nodes()
        * chromatic.subs(chromatic_variable, 1 / (1 - p))
    )
    if sp.factor(sp.sympify(certificate["phi"]) - phi) != 0:
        raise AssertionError("stored target polynomial does not match the Atlas graph")
    target_coefficients = {
        target_core: polynomial_coefficients(sp.Integer(1), t, max_power),
        0: polynomial_coefficients(-phi, t, max_power),
    }
    coefficient_equations: list[dict[str, object]] = []
    for core in sorted({core for core, _ in group_keys} | set(target_coefficients)):
        for power in range(max_power + 1):
            terms: list[list[int]] = []
            actual = fmpq(0)
            for row, (row_core, isolated) in enumerate(group_keys):
                if row_core != core:
                    continue
                density = density_coefficients[isolated]
                weights = (
                    density[power],
                    density[power - 1] if power >= 1 else Fraction(0),
                    density[power - 2] if power >= 2 else Fraction(0),
                    (density[power - 1] if power >= 1 else Fraction(0))
                    - (density[power - 2] if power >= 2 else Fraction(0)),
                )
                for slot, weight in enumerate(weights):
                    if not weight:
                        continue
                    terms.append([row, slot, weight.numerator, weight.denominator])
                    actual += group_totals_q[row][slot] * fmpq(
                        weight.numerator, weight.denominator
                    )
            target_row = target_coefficients.get(
                core, [Fraction(0) for _ in range(max_power + 1)]
            )
            expected = target_row[power] * int(certificate["factor_denominator"]) ** 2
            if not terms and not expected:
                continue
            if actual != fmpq(expected.numerator, expected.denominator):
                raise AssertionError(
                    f"group coefficient mismatch core={core} power={power}"
                )
            coefficient_equations.append({
                "core_power": [core, power],
                "expected": fraction_pair(expected),
                "terms": terms,
            })

    # Every non-common correction can be put over one exact denominator per
    # block.  This turns diagonal-dominance and exceptional Gram checks into
    # bounded integer arithmetic instead of repeated operations on enormous
    # rational denominators.
    exceptional_denominators = []
    exceptional_scaled = []
    dd_margins_scaled = []
    for block, entries in enumerate(exceptional):
        denominator = lcm(
            common_denominator,
            *(int(entry[3]) for entry in entries),
        )
        scaled_entries = [
            [int(i), int(j), int(numerator) * (denominator // int(entry_denominator))]
            for i, j, numerator, entry_denominator in entries
        ]
        margin = Fraction(*map(int, certificate["dd_margins"][block]))
        scaled_margin = margin * denominator
        if scaled_margin.denominator != 1:
            raise AssertionError((block, "DD margin does not use exceptional denominator"))
        exceptional_denominators.append(denominator)
        exceptional_scaled.append(scaled_entries)
        dd_margins_scaled.append(scaled_margin.numerator)

    exceptional_group_scaled: list[list[list[int]]] = []
    for row, pulled in enumerate(pulled_groups):
        row_values: list[list[int]] = []
        for block in range(10):
            matrix = pulled[block % 5]
            size = transforms[block % 5].shape[1]
            difference = full_grams[block] - common_grams[block]
            denominator = exceptional_denominators[block]

            def scaled_slot(left_offset: int, right_offset: int) -> int:
                total = fmpq(0)
                for i, j in zip(*np.nonzero(matrix)):
                    total += int(matrix[i, j]) * 24 * upper_entry(
                        difference, left_offset + i, right_offset + j
                    )
                scaled = total * denominator
                if scaled.denominator != 1:
                    raise AssertionError((row, block, left_offset, right_offset))
                return int(scaled.numerator)

            if block < 5:
                values = [
                    scaled_slot(0, 0),
                    scaled_slot(0, size) + scaled_slot(size, 0),
                    scaled_slot(size, size),
                    0,
                ]
            else:
                values = [0, 0, 0, scaled_slot(0, 0)]
            row_values.append(values)
        exceptional_group_scaled.append(row_values)

        for slot in range(4):
            rebuilt = fmpq(
                common_group_totals[row][slot][0],
                common_group_totals[row][slot][1],
            )
            for block in range(10):
                rebuilt += fmpq(
                    exceptional_group_scaled[row][block][slot],
                    exceptional_denominators[block],
                )
            if rebuilt != group_totals_q[row][slot]:
                raise AssertionError((row, slot, "exceptional group reconstruction"))

    payload = {
        "source": certificate_path.name,
        "atlas": int(certificate["atlas"]),
        "interval": certificate["interval"],
        "factor_denominator": int(certificate["factor_denominator"]),
        "orders": orders,
        "factors": factors,
        "common_correction_denominator": common_denominator,
        "common_correction_scaled_upper": common_upper,
        "exceptional_denominators": exceptional_denominators,
        "exceptional_scaled": exceptional_scaled,
        "dd_margins_scaled": dd_margins_scaled,
        "intermediate_scaled": intermediates,
        "common_gram_scaled_upper": common_gram_upper,
        "factor_bounds": factor_bounds,
        "common_correction_scaled_bounds": correction_bounds,
        "intermediate_bounds": intermediate_bounds,
        "gram_bounds": gram_bounds,
        "group_keys": group_keys,
        "common_group_totals": common_group_totals,
        "group_totals": group_totals,
        "target_core": target_core,
        "coefficient_equations": coefficient_equations,
        "dd_margins": certificate["dd_margins"],
    }
    output = Path(args.output)
    write_if_changed(output, compact_json(payload))
    # Lean imports only the layer it is checking.  Parsing the former 10 MB
    # all-in-one witness once per generated module needlessly multiplied both
    # elaboration time and memory, so also emit stable sidecars by proof layer.
    parts = {
        "header": {
            key: payload[key]
            for key in (
                "source", "atlas", "interval", "factor_denominator", "orders",
                "factors", "factor_bounds", "common_correction_scaled_bounds",
                "intermediate_bounds", "gram_bounds", "dd_margins",
            )
        },
        "common": {
            key: payload[key]
            for key in (
                "common_correction_denominator",
                "common_correction_scaled_upper", "intermediate_scaled",
                "common_gram_scaled_upper",
            )
        },
        "groups": {
            key: payload[key]
            for key in (
                "group_keys", "common_group_totals", "group_totals",
                "target_core", "coefficient_equations",
            )
        },
    }
    part_sizes = []
    for label, contents in parts.items():
        part_path = output.with_name(f"{output.stem}_{label}{output.suffix}")
        write_if_changed(part_path, compact_json(contents))
        part_sizes.append(f"{label}={part_path.stat().st_size}")

    # The four coarse layers are useful to non-Lean consumers, but some still
    # contain multi-megabyte arrays.  Lean retains a decoded constant for the
    # rest of the current module, so produce a second, fine-grained layer whose
    # leaves are capped at 32 KB.  The manifest is deterministic and drives the
    # generated one-leaf-per-module checker.
    fine_manifest: dict[str, object] = {
        "atlas": payload["atlas"],
        "max_bytes": FINE_SIDECAR_MAX_BYTES,
    }

    meta_path = output.with_name(f"{output.stem}_meta{output.suffix}")
    meta_keys = (
        "source", "atlas", "interval", "factor_denominator", "orders",
        "factor_bounds", "common_correction_denominator",
        "common_correction_scaled_bounds", "intermediate_bounds", "gram_bounds",
        "group_keys", "target_core",
    )
    write_if_changed(meta_path, compact_json({key: payload[key] for key in meta_keys}))
    fine_manifest["meta"] = {"file": meta_path.name, "bytes": meta_path.stat().st_size}

    header_blocks = []
    for block in range(10):
        factor_path = output.with_name(
            f"{output.stem}_factor_block_{block:02d}{output.suffix}"
        )
        write_if_changed(
            factor_path,
            compact_json({"block": block, "data": payload["factors"][block]}),
        )
        margin_path = output.with_name(
            f"{output.stem}_dd_margin_block_{block:02d}{output.suffix}"
        )
        write_if_changed(
            margin_path,
            compact_json({"block": block, "data": payload["dd_margins"][block]}),
        )
        scale_path = output.with_name(
            f"{output.stem}_exceptional_scale_block_{block:02d}{output.suffix}"
        )
        write_if_changed(
            scale_path,
            compact_json({
                "block": block,
                "denominator": payload["exceptional_denominators"][block],
                "common_multiplier": (
                    payload["exceptional_denominators"][block]
                    // common_denominator
                ),
                "dd_margin_scaled": payload["dd_margins_scaled"][block],
            }),
        )
        header_blocks.append({
            "block": block,
            "factor_file": factor_path.name,
            "factor_bytes": factor_path.stat().st_size,
            "margin_file": margin_path.name,
            "margin_bytes": margin_path.stat().st_size,
            "exceptional_scale_file": scale_path.name,
            "exceptional_scale_bytes": scale_path.stat().st_size,
        })
    fine_manifest["header_blocks"] = header_blocks

    common_chunks = []
    common_fields = (
        "common_correction_scaled_upper", "intermediate_scaled",
        "common_gram_scaled_upper",
    )
    for field in common_fields:
        for block, items in enumerate(payload[field]):
            chunks = write_sequence_chunks(
                output,
                f"{field}_block_{block:02d}",
                len(items),
                lambda start, stop, field=field, block=block, items=items: {
                    "field": field,
                    "block": block,
                    "start": start,
                    "data": items[start:stop],
                },
            )
            for chunk in chunks:
                chunk.update({"field": field, "block": block})
            common_chunks.extend(chunks)
    fine_manifest["common_chunks"] = common_chunks

    exceptional_scaled_chunks = []
    for block, items in enumerate(payload["exceptional_scaled"]):
        chunks = write_sequence_chunks(
            output,
            f"exceptional_scaled_block_{block:02d}",
            len(items),
            lambda start, stop, block=block, items=items: {
                "block": block,
                "start": start,
                "data": items[start:stop],
            },
        )
        for chunk in chunks:
            chunk["block"] = block
        exceptional_scaled_chunks.extend(chunks)
    fine_manifest["exceptional_scaled_chunks"] = exceptional_scaled_chunks

    exceptional_group_chunks = []
    for block in range(10):
        items = [exceptional_group_scaled[row][block] for row in range(len(group_keys))]
        chunks = write_sequence_chunks(
            output,
            f"exceptional_group_scaled_block_{block:02d}",
            len(items),
            lambda start, stop, block=block, items=items: {
                "block": block,
                "start": start,
                "data": items[start:stop],
            },
        )
        for chunk in chunks:
            chunk["block"] = block
        exceptional_group_chunks.extend(chunks)
    fine_manifest["exceptional_group_chunks"] = exceptional_group_chunks

    group_chunks = write_sequence_chunks(
        output,
        "group_rows",
        len(payload["group_keys"]),
        lambda start, stop: {
            "start": start,
            "data": [
                payload["common_group_totals"][start:stop],
                payload["group_totals"][start:stop],
            ],
        },
    )
    fine_manifest["group_chunks"] = group_chunks

    coefficient_chunks = []
    for index, equation in enumerate(payload["coefficient_equations"]):
        equation_path = output.with_name(
            f"{output.stem}_coefficient_equation_{index:03d}{output.suffix}"
        )
        write_if_changed(equation_path, compact_json(equation))
        coefficient_chunks.append({
            "file": equation_path.name,
            "index": index,
            "bytes": equation_path.stat().st_size,
        })
    fine_manifest["coefficient_chunks"] = coefficient_chunks

    manifest_path = output.with_name(f"{output.stem}_manifest{output.suffix}")
    write_if_changed(manifest_path, compact_json(fine_manifest))
    fine_sizes = [meta_path.stat().st_size]
    fine_sizes.extend(
        size
        for item in header_blocks
        for size in (
            int(item["factor_bytes"]), int(item["margin_bytes"]),
            int(item["exceptional_scale_bytes"]),
        )
    )
    fine_sizes.extend(
        int(item["bytes"])
        for key in (
            "common_chunks", "exceptional_scaled_chunks", "group_chunks",
            "coefficient_chunks", "exceptional_group_chunks",
        )
        for item in fine_manifest[key]
    )
    print(
        f"wrote {output}: atlas={payload['atlas']} groups={len(group_keys)} "
        f"exceptional={sum(map(len, exceptional))} bytes={output.stat().st_size} "
        + " ".join(part_sizes)
        + f" fine_leaves={len(fine_sizes)} max_fine_bytes={max(fine_sizes)}"
    )


if __name__ == "__main__":
    main()
