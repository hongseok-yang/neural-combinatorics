"""Generate bounded checks for the final interval-polynomial coefficients.

The exporter records each coefficient equation as a sparse linear combination
of the 143 four-slot group totals.  This generator gives every equation its
own Lean module, so one very large rational normalization cannot block the
remaining equations or certificates.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def group_module(tag: str, descriptor: dict[str, object]) -> str:
    start = int(descriptor["start"])
    stop = int(descriptor["stop"])
    return f"{tag}GroupRows{start:03d}_{stop - 1:03d}Data"


def group_location(
    tag: str, descriptors: list[dict[str, object]], row: int
) -> tuple[str, int]:
    for descriptor in descriptors:
        start = int(descriptor["start"])
        stop = int(descriptor["stop"])
        if start <= row < stop:
            return group_module(tag, descriptor), row - start
    raise AssertionError(f"missing group row {row}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest")
    parser.add_argument("--tag", required=True)
    parser.add_argument("--lean-root", default="lean/Taeyoung/Methods/RootedSOS")
    args = parser.parse_args()
    if re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.tag) is None:
        raise ValueError(f"invalid Lean tag: {args.tag}")

    manifest_path = Path(args.manifest)
    directory = manifest_path.parent
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    tag = f"S4{args.tag}"
    namespace = f"{tag}CoefficientChecks"
    targets: list[str] = []
    check_modules: list[str] = []

    for descriptor in manifest.get("coefficient_chunks", []):
        index = int(descriptor["index"])
        equation = json.loads(
            (directory / str(descriptor["file"])).read_text(encoding="utf-8")
        )
        terms = equation["terms"]
        data_module = f"{tag}CoefficientEquation{index:03d}Data"
        locations = [
            group_location(tag, manifest["group_chunks"], int(term[0]))
            for term in terms
        ]
        group_imports = list(dict.fromkeys(module for module, _ in locations))
        imports = "\n".join(
            f"import {PREFIX}.{module}"
            for module in [data_module, *group_imports]
        )
        summands = []
        for term_index, ((_, slot, _, _), (module, local_row)) in enumerate(
            zip(terms, locations)
        ):
            summands.append(
                f"  ratPair ({module}.fullTotalComponent {local_row} {int(slot)} 0) "
                f"({module}.fullTotalComponent {local_row} {int(slot)} 1) *\n"
                f"    termWeight {term_index}"
            )
        lhs = " +\n".join(summands) if summands else "  0"
        module = f"{tag}CoefficientEquation{index:03d}Check"
        theorem = f"coefficient_equation_{index:03d}_valid"
        equation_namespace = f"{namespace}.Equation{index:03d}"
        source = f"""{imports}

namespace {PREFIX}.{equation_namespace}

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def ratPair (numerator denominator : Int) : Rat :=
  Rat.ofInt numerator / Rat.ofInt denominator

private def termComponent (term coordinate : Nat) : Int :=
  ((({data_module}.terms[term]?).getD #[])[coordinate]?).getD 0

private def termWeight (term : Nat) : Rat :=
  ratPair (termComponent term 2) (termComponent term 3)

def equationLhs : Rat :=
{lhs}

def equationExpected : Rat :=
  ratPair (({data_module}.expected[0]?).getD 0)
    (({data_module}.expected[1]?).getD 0)

def equationValid : Bool := equationLhs == equationExpected

theorem {theorem} : equationValid = true := by decide +kernel

end {PREFIX}.{equation_namespace}
"""
        write_if_changed(lean_root / f"{module}.lean", source)
        targets.append(f"{PREFIX}.{module}")
        check_modules.append(module)

    umbrella = f"{tag}CoefficientChecks"
    imports = "\n".join(
        f"import {PREFIX}.{module}" for module in check_modules
    )
    fields = "\n".join(
        f"  equation{index:03d} : Equation{index:03d}.equationValid = true"
        for index in range(len(check_modules))
    ) or "  empty : True"
    witnesses = "\n".join(
        f"  equation{index:03d} := Equation{index:03d}.coefficient_equation_{index:03d}_valid"
        for index in range(len(check_modules))
    ) or "  empty := trivial"
    umbrella_source = f"""{imports}

namespace {PREFIX}.{namespace}

/-! Exact coefficient equations for the claimed fixed-density group totals. -/
structure CoefficientIdentityVerified : Prop where
{fields}

theorem coefficient_identity_verified : CoefficientIdentityVerified where
{witnesses}

end {PREFIX}.{namespace}
"""
    write_if_changed(lean_root / f"{umbrella}.lean", umbrella_source)
    targets.append(f"{PREFIX}.{umbrella}")

    target_file = directory / f"{manifest_path.stem}_coefficient_check_targets.txt"
    write_if_changed(target_file, "\n".join(targets) + "\n")
    print(
        f"wrote {len(check_modules)} coefficient checks, "
        f"umbrella={PREFIX}.{umbrella}, targets={target_file}"
    )


if __name__ == "__main__":
    main()
