"""Emit compact kernel checks for triangular congruence positivity witnesses."""

import argparse
import json
import re
import sys
from pathlib import Path

sys.set_int_max_str_digits(0)
PREFIX = "Taeyoung.Methods.RootedSOS"


def row_tag(c):
    tag = f"CompactS4.Atlas{int(c['atlas'])}"
    suffix = c.get('lean_namespace_suffix', '')
    if suffix:
        assert re.fullmatch(r'[A-Z][A-Za-z0-9_]*', suffix), suffix
        tag += '.'+suffix
    return tag


def table(values):
    if len(values) == 1:
        return f"(.leaf ({values[0]}))"
    middle = len(values) // 2
    return f"(.node {middle} {table(values[:middle])}\n{table(values[middle:])})"


def matrix(name, values):
    columns = len(values[0])
    return (f"private def {name}Data : PackedTable :=\n{table([x for r in values for x in r])}\n\n"
            f"def {name} (i j : Nat) : Int := {name}Data.get (i * {columns} + j)\n")


def packed_product(name, left_name, right_name, result_name, left, right, result, n):
    m, p = len(left), len(right[0])
    assert all(len(row) == n for row in left) and len(right) == n
    assert len(result) == m and all(len(row) == p for row in result)
    left_bound = max(abs(x) for r in left for x in r)
    right_bound = max(abs(x) for r in right for x in r)
    bound = n * left_bound * right_bound
    base = 2 * bound + 1
    encoded = [sum(value * base**j for j, value in enumerate(row)) for row in right]
    return f"""
private def {name}Enc : PackedTable :=
{table(encoded)}

private theorem {name}_left_bound : ∀ (i : Fin {m}) (j : Fin {n}), ({left_name} i j).natAbs ≤ {left_bound} := by decide +kernel
private theorem {name}_right_bound : ∀ (i : Fin {n}) (j : Fin {p}), ({right_name} i j).natAbs ≤ {right_bound} := by decide +kernel
private theorem {name}_result_bound : ∀ (i : Fin {m}) (j : Fin {p}), ({result_name} i j).natAbs ≤ {bound} := by decide +kernel
private theorem {name}_encoded : ∀ i : Fin {n},
    {name}Enc.get i = ∑ j : Fin {p}, {right_name} i j * ({base} : Int)^j.1 := by decide +kernel
private theorem {name}_product : ∀ i : Fin {m},
    shiftedEncoding {base} {bound} (List.ofFn fun j : Fin {p} => {result_name} i j) =
      {bound} * geometricEncoding {base} {p} +
        ∑ j : Fin {n}, {left_name} i j * {name}Enc.get j := by decide +kernel

theorem {name}_exact (i : Fin {m}) (j : Fin {p}) :
    {result_name} i j = ∑ k : Fin {n}, {left_name} i k * {right_name} k j :=
  packed_rect_product_exact {left_name} {right_name} {result_name}
    {left_bound} {right_bound} {bound} {base} (fun i => {name}Enc.get i)
    {name}_left_bound {name}_right_bound {name}_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {name}_encoded {name}_product i j
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    parser.add_argument("--blocks", nargs="+", type=int, default=list(range(10)))
    args = parser.parse_args()
    c = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    tag = row_tag(c)
    root = Path("lean/Taeyoung/Methods/RootedSOS") / Path(*tag.split("."))
    root.mkdir(parents=True, exist_ok=True)
    for block in args.blocks:
        gram = c["gram_scaled"][block]
        witness = c["positivity"][block]
        pre, middle, dominant = (witness[key] for key in ("preconditioner", "intermediate", "dominant"))
        transposed = list(map(list, zip(*pre)))
        n = len(gram)
        stem = f"Block{block:02d}"
        namespace = f"{PREFIX}.{tag}.{stem}"
        data = (f"import {PREFIX}.PackedMatrix\n\nnamespace {namespace}\n"
                "set_option maxRecDepth 1000000\n"
                + "\n".join(matrix(name, values) for name, values in
                             [("G", gram), ("P", pre), ("K", middle), ("B", dominant)])
                + "\ndef Pt (i j : Nat) : Int := P j i\n"
                + f"\nend {namespace}\n")
        (root / f"{stem}Data.lean").write_text(data, encoding="utf-8")
        checks = f"""import {PREFIX}.{tag}.{stem}Data
import {PREFIX}.CongruenceDiagonalDominance

namespace {namespace}
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
"""
        checks += packed_product("GP", "G", "P", "K", gram, pre, middle, n)
        checks += packed_product("PK", "Pt", "K", "B", transposed, middle, dominant, n)
        checks += f"""
private theorem upper : ∀ i j : Fin {n}, j < i → P i j = 0 := by decide +kernel
private theorem diagonal : ∀ i : Fin {n}, P i i ≠ 0 := by decide +kernel
private theorem symm : ∀ i j : Fin {n}, B i j = B j i := by decide +kernel
private theorem dominant : ∀ i : Fin {n},
    (∑ j : Fin {n}, if i = j then 0 else (B i j).natAbs : Nat) ≤ (B i i).toNat := by decide +kernel
private theorem positive : ∀ i : Fin {n}, 0 ≤ B i i := by decide +kernel

theorem gram_nonneg (x : Fin {n} → Real) :
    0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x :=
  matrixQuadratic_nonneg_of_integer_congruence
    (fun i j => G i j) (fun i j => P i j) (fun i j => K i j) (fun i j => B i j)
    upper diagonal GP_exact PK_exact symm dominant positive x

#print axioms gram_nonneg
end {namespace}
"""
        (root / f"{stem}PSD.lean").write_text(checks, encoding="utf-8")
        print(stem, n, "source bytes", len(data.encode()) + len(checks.encode()))


if __name__ == "__main__":
    main()
