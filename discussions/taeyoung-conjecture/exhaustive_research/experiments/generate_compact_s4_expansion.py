"""Emit exact expansion from the small face matrices to the original S4 slices."""

import argparse
import json
from pathlib import Path

from flint import fmpz_mat

from generate_compact_s4_psd import PREFIX, matrix, packed_product, row_tag


def entries(matrix):
    return [[int(x) for x in row] for row in matrix.tolist()]


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
        face, gram = c["face_bases"][block], c["gram_scaled"][block]
        intermediate = fmpz_mat(face) * fmpz_mat(gram)
        full = intermediate * fmpz_mat(face).transpose()
        intermediate, full = entries(intermediate), entries(full)
        m, n = len(face), len(gram)
        stem = f"Block{block:02d}"
        namespace = f"{PREFIX}.{tag}.{stem}"
        data = (f"import {PREFIX}.{tag}.{stem}Data\n\nnamespace {namespace}\n"
                "set_option maxRecDepth 1000000\n"
                + "\n".join(matrix(name, values) for name, values in
                             [("N", face), ("NG", intermediate), ("H", full)])
                + "\ndef Nt (i j : Nat) : Int := N j i\n"
                + f"\nend {namespace}\n")
        (root / f"{stem}ExpansionData.lean").write_text(data, encoding="utf-8")
        checks = f"""import {PREFIX}.{tag}.{stem}ExpansionData

namespace {namespace}
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
"""
        checks += packed_product("NGProduct", "N", "G", "NG", face, gram, intermediate, n)
        checks += packed_product("FullProduct", "NG", "Nt", "H", intermediate,
                                 list(map(list, zip(*face))), full, n)
        checks += f"""
theorem expanded_entries_exact (i j : Fin {m}) :
    H i j = ∑ k : Fin {n}, (∑ l : Fin {n}, N i l * G l k) * N j k := by
  rw [FullProduct_exact]
  apply Finset.sum_congr rfl
  intro k _
  rw [NGProduct_exact]
  rfl

#print axioms expanded_entries_exact
end {namespace}
"""
        (root / f"{stem}Expansion.lean").write_text(checks, encoding="utf-8")
        print(stem, "expanded order", m, "source bytes", len(data.encode())+len(checks.encode()))


if __name__ == "__main__":
    main()
