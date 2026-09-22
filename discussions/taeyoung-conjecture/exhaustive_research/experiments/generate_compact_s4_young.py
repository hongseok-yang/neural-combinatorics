"""Check the complete shared Young pullback with bounded positional encodings.

Sparse columns are the primary definition of the linear forms. No rank,
irreducibility or dense/sparse equality claim is needed for SOS soundness.
"""

import argparse
import json
from pathlib import Path

from generate_compact_s4_psd import PREFIX, matrix, table

BASE = 1153
BOUND = 576


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--blocks", nargs="+", type=int, default=[4])
    args = parser.parse_args()
    common = json.loads(Path("experiments/s4_lean_common.json").read_text(encoding="utf-8"))
    root = Path("lean/Taeyoung/Methods/RootedSOS/CompactS4")
    for block in args.blocks:
        tag = common["names"][block]
        dense = common["young_bases"][tag]
        d = len(dense[0])
        columns = [[(a, row[i]) for a, row in enumerate(dense) if row[i]] for i in range(d)]
        counts = [len(c) for c in columns]
        max_values = [max(abs(v) for _, v in c) for c in columns]
        assert max(c*v for c,v in zip(counts,max_values)) <= 24
        width = max(counts)
        indices = [[a for a, _ in c]+[0]*(width-len(c)) for c in columns]
        values = [[v for _, v in c]+[0]*(width-len(c)) for c in columns]
        powers = [BASE**g for g in range(143)]
        offset = BOUND * sum(powers)
        encoded = [[offset for _ in range(d)] for _ in range(d)]
        for g, group in enumerate(common["pulled_groups"]):
            for i,j,value in group[block]:
                encoded[i][j] += value*powers[g]
        assert all(x>=0 for row in encoded for x in row)
        namespace = f"{PREFIX}.CompactS4.Young{tag}"
        data = f"""import {PREFIX}.PackedMatrix

namespace {namespace}
set_option maxRecDepth 1000000

private def countsData : PackedTable := {table(counts)}
private def maxValuesData : PackedTable := {table(max_values)}
def count (i : Fin {d}) : Nat := (countsData.get i).toNat
def maxValue (i : Fin {d}) : Nat := (maxValuesData.get i).toNat
{matrix('indexValue',indices)}
{matrix('weight',values)}
{matrix('codeValue',encoded)}
def root (i : Fin {d}) (k : Fin (count i)) : Fin 352 :=
  ⟨(indexValue i k).toNat % 352, Nat.mod_lt _ (by decide)⟩
def value (i : Fin {d}) (k : Fin (count i)) : Int := weight i k
def code (i j : Fin {d}) : Nat := (codeValue i j).toNat

def TInt (a : Fin 352) (i : Fin {d}) : Int :=
  ∑ k : Fin (count i), if root i k = a then value i k else 0

theorem count_bound : ∀ i : Fin {d}, count i * maxValue i ≤ 24 := by decide +kernel
theorem value_bound : ∀ i : Fin {d}, ∀ k : Fin (count i), (value i k).natAbs ≤ maxValue i := by decide +kernel

end {namespace}
"""
        (root/f"Young{tag}Data.lean").write_text(data,encoding="utf-8")
        base = f"""import {PREFIX}.CompactS4.Young{tag}Data
import {PREFIX}.CompactS4.Groups
import {PREFIX}.PackedCoefficients

namespace {namespace}
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def powersData : PackedTable := {table(powers)}
def groupPower (g : Fin 143) : Int := powersData.get g
theorem groupPower_exact : ∀ g : Fin 143, groupPower g = ({BASE} : Int)^g.1 := by decide +kernel

def groupCoefficient (i j : Fin {d}) (g : Fin 143) : Int :=
  groupedCoefficient (fun a b => pairGroup (root i a) (root j b)) (value i) (value j) g

def pulled (g : Fin 143) (i j : Fin {d}) : Int := decodeSignedDigit {BASE} {BOUND} (code i j) g

theorem groupCoefficient_bound (i j : Fin {d}) (g : Fin 143) :
    (groupCoefficient i j g).natAbs ≤ {BOUND} := by
  have h := groupedCoefficient_bound
    (fun a b => pairGroup (root i a) (root j b)) (value i) (value j)
    (maxValue i) (maxValue j) (value_bound i) (value_bound j) g
  simp only [Fintype.card_fin] at h
  have hm := Nat.mul_le_mul (count_bound i) (count_bound j)
  have he : count i * (count j * (maxValue i * maxValue j)) =
      (count i * maxValue i) * (count j * maxValue j) := by ring
  exact h.trans (by simpa only [he] using hm)

def codeIdentity (i j : Fin {d}) : Prop :=
  (code i j : Int) = {offset} +
    ∑ a : Fin (count i), ∑ b : Fin (count j),
      value i a * value j b * groupPower (pairGroup (root i a) (root j b))

instance (i j : Fin {d}) : Decidable (codeIdentity i j) := by
  unfold codeIdentity
  infer_instance

theorem pulled_exact_of_code (i j : Fin {d}) (h : codeIdentity i j) (g : Fin 143) :
    pulled g i j = groupCoefficient i j g := by
  apply groupedCoefficient_of_encoding
    (fun a b => pairGroup (root i a) (root j b)) (value i) (value j)
    (by decide) (groupCoefficient_bound i j)
  have hoff : ({BOUND} : Int) * geometricEncoding {BASE} 143 = {offset} := by decide +kernel
  simp only [Nat.cast_ofNat]
  rw [hoff]
  simpa only [codeIdentity, groupPower_exact] using h

end {namespace}
"""
        (root/f"Young{tag}Base.lean").write_text(base,encoding="utf-8")
        chunk_size=13
        chunks=[]
        for start in range(0,d,chunk_size):
            stop=min(start+chunk_size,d)
            name=f"Young{tag}Rows{start:02d}"
            row_checks="\n".join(
                f"private theorem code_fixed_{i:02d} : ∀ j : Fin {d}, codeIdentity {i} j := by decide +kernel"
                for i in range(start,stop))
            row_cases="\n".join(f"  · exact code_fixed_{i:02d} j" for i in range(start,stop))
            proof=f"""import {PREFIX}.CompactS4.Young{tag}Base

namespace {namespace}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

{row_checks}

theorem code_rows_{start:02d} : ∀ k : Fin {stop-start}, ∀ j : Fin {d},
    codeIdentity ⟨{start}+k.1, by omega⟩ j := by
  intro k j
  fin_cases k
{row_cases}

end {namespace}
"""
            (root/f"{name}.lean").write_text(proof,encoding="utf-8")
            chunks.append((start,stop,name))
        imports="\n".join(f"import {PREFIX}.CompactS4.{name}" for _,_,name in chunks)
        cases=""
        for start,stop,_ in chunks:
            cases+=f"""  by_cases h : i.1 < {stop}
  · let k : Fin {stop-start} := ⟨i.1-{start}, by omega⟩
    have hi : (⟨{start}+k.1, by omega⟩ : Fin {d}) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [hi] using code_rows_{start:02d} k j
"""
        final=f"""{imports}
import {PREFIX}.SparseFlagCoefficients

namespace {namespace}

theorem code_identity (i j : Fin {d}) : codeIdentity i j := by
{cases}  omega

theorem pulled_exact (g : Fin 143) (i j : Fin {d}) :
    pulled g i j = groupCoefficient i j g := pulled_exact_of_code i j (code_identity i j) g

theorem pair_basis_density
    {{Ω : Type*}} [MeasurableSpace Ω] {{μ : MeasureTheory.Measure Ω}}
    [MeasureTheory.IsProbabilityMeasure μ]
    (i j : Fin {d}) (W : Taeyoung.Graphon Ω μ) :
    (∑ a : Fin 352, ∑ b : Fin 352, (TInt a i : Real) * (TInt b j : Real) *
      Taeyoung.homDensity (S4Flags.gluedGraph a b) W) =
      ∑ g : Fin 143, (pulled g i j : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W) := by
  let f : Fin 143 → Real := fun g =>
    Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
      Taeyoung.homDensity (S4Classification.coreGraph6 g) W
  calc
    _ = ∑ a : Fin 352, ∑ b : Fin 352,
        (TInt a i : Real) * (TInt b j : Real) * f (pairGroup a b) := by
      simp_rw [pair_density]
      rfl
    _ = ∑ g : Fin 143, (groupCoefficient i j g : Real) * f g :=
      sparseVector_pair_grouped pairGroup (root i) (root j) (value i) (value j) f
    _ = _ := by simp only [pulled_exact]; rfl

#print axioms pulled_exact
#print axioms pair_basis_density
end {namespace}
"""
        (root/f"Young{tag}.lean").write_text(final,encoding="utf-8")
        print('Young',tag,'dimension',d,'files',3+len(chunks),'data bytes',len(data.encode()))


if __name__=="__main__":
    main()
