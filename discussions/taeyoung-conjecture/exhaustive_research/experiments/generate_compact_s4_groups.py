"""A balanced lookup checked against the existing S4 graph-isomorphism witnesses."""

import json
from pathlib import Path

from generate_compact_s4_psd import PREFIX, table


def main():
    manifest_path = Path("experiments/s4_lean_classification_manifest.json")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    values = []
    for chunk in manifest["decoded_group_lookup_chunks"]:
        payload = json.loads((manifest_path.parent / chunk["file"]).read_text(encoding="utf-8"))
        assert payload["start"] * 256 == len(values)
        values.extend(x for layer in payload["data"] for row in layer for x in row)
    assert len(values) == 57 * 16 * 16 and all(0 <= x < 143 for x in values)
    root = Path("lean/Taeyoung/Methods/RootedSOS/CompactS4")
    root.mkdir(parents=True, exist_ok=True)
    data = f"""import {PREFIX}.PackedMatrix

namespace {PREFIX}.CompactS4
set_option maxRecDepth 1000000

private def groupsData : PackedTable :=
{table(values)}

def lookupGroup (index : Fin 57) (left right : Fin 16) : Fin 143 :=
  ⟨(groupsData.get ((index.1 * 16 + left.1) * 16 + right.1)).toNat % 143,
    Nat.mod_lt _ (by decide)⟩

end {PREFIX}.CompactS4
"""
    (root / "GroupsData.lean").write_text(data, encoding="utf-8")
    proof = f"""import {PREFIX}.CompactS4.GroupsData
import {PREFIX}.S4ClassificationDensity

namespace {PREFIX}.CompactS4
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem lookupGroup_eq : ∀ index : Fin 57, ∀ left right : Fin 16,
    lookupGroup index left right = S4Classification.witnessGroup index left right := by
  decide +kernel

def pairGroup (a b : Fin 352) : Fin 143 :=
  lookupGroup (S4Classification.pairUnionIndex a b)
    (S4Classification.pairLeftBranchFin a) (S4Classification.pairRightBranchFin b)

theorem pairGroup_eq (a b : Fin 352) :
    pairGroup a b = S4Classification.pairWitnessGroup a b := by
  exact lookupGroup_eq _ _ _

theorem pair_density
    {{Ω : Type*}} [MeasurableSpace Ω] {{μ : MeasureTheory.Measure Ω}}
    [MeasureTheory.IsProbabilityMeasure μ]
    (a b : Fin 352) (W : Taeyoung.Graphon Ω μ) :
    Taeyoung.homDensity (S4Flags.gluedGraph a b) W =
      Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey (pairGroup a b)).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 (pairGroup a b)) W := by
  rw [pairGroup_eq]
  exact S4Classification.pair_density_classified a b W

#print axioms pair_density
end {PREFIX}.CompactS4
"""
    (root / "Groups.lean").write_text(proof, encoding="utf-8")
    print("wrote two common group modules", len(data.encode()), "data bytes")


if __name__ == "__main__":
    main()
