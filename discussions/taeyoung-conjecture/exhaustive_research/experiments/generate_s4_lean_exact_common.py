"""Generate the proof layer decoding S4 row checks to exact Gram entries."""

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
    meta = json.loads(
        (directory / str(manifest["meta"]["file"])).read_text(encoding="utf-8")
    )
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    tag = f"S4{args.tag}"
    exact_modules: list[str] = []

    for block, header in enumerate(manifest["header_blocks"]):
        factor = json.loads(
            (directory / str(header["factor_file"])).read_text(encoding="utf-8")
        )["data"]
        rows = len(factor)
        order = int(meta["orders"][block])
        check_namespace = f"{tag}Block{block:02d}Checks"
        checks_module = f"{tag}Block{block:02d}Checks"
        data_module = f"{tag}Block{block:02d}Data"
        exact_module = f"{tag}Block{block:02d}Exact"
        source = f"""import {PREFIX}.EncodedGram
import {PREFIX}.{checks_module}

/-! Exact common-correction matrix identities for certificate block {block}. -/

namespace {PREFIX}.{check_namespace}

set_option maxRecDepth 100000

theorem intermediate_entries_exact (row : Fin factorRows) (j : Fin order) :
    claimedIntermediateScaled row j =
      expectedIntermediate commonCorrectionDenominator FInt
        claimedCommonCScaled row j := by
  have h := all_intermediate_entries_valid row j
  simpa only [intermediateEntryValid, beq_iff_eq] using h

theorem common_gram_entries_exact (row col : Fin factorRows) :
    claimedCommonGramScaled row col =
      expectedGram FInt claimedIntermediateScaled row col := by
  have h := all_gram_entries_valid row col
  simpa only [gramEntryValid, beq_iff_eq] using h

end {PREFIX}.{check_namespace}
"""
        write_if_changed(lean_root / f"{exact_module}.lean", source)
        exact_modules.append(exact_module)

    umbrella = f"{tag}CommonExact"
    bundle_namespace = f"{tag}CommonExact"
    fields = []
    witnesses = []
    for block in range(10):
        check = f"{tag}Block{block:02d}Checks"
        fields.extend((
            f"  intermediate{block:02d} : ∀ (row : Fin {check}.factorRows) "
            f"(col : Fin {check}.order),\n"
            f"    {check}.claimedIntermediateScaled row col =\n"
            f"      expectedIntermediate {check}.commonCorrectionDenominator "
            f"{check}.FInt {check}.claimedCommonCScaled row col",
            f"  gram{block:02d} : ∀ (row col : Fin {check}.factorRows),\n"
            f"    {check}.claimedCommonGramScaled row col =\n"
            f"      expectedGram {check}.FInt {check}.claimedIntermediateScaled row col",
        ))
        witnesses.extend((
            f"  intermediate{block:02d} := {check}.intermediate_entries_exact",
            f"  gram{block:02d} := {check}.common_gram_entries_exact",
        ))
    umbrella_source = (
        "\n".join(f"import {PREFIX}.{module}" for module in exact_modules)
        + f"""

namespace {PREFIX}.{bundle_namespace}

structure CommonGramVerified : Prop where
{chr(10).join(fields)}

theorem common_gram_verified : CommonGramVerified where
{chr(10).join(witnesses)}

end {PREFIX}.{bundle_namespace}
"""
    )
    write_if_changed(
        lean_root / f"{umbrella}.lean",
        umbrella_source,
    )
    print(f"wrote {len(exact_modules)} exact modules, umbrella={PREFIX}.{umbrella}")


if __name__ == "__main__":
    main()
