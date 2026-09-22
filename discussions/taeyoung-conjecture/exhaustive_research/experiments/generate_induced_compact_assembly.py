"""Assemble an induced interval and its complete two-piece catalogue bound.

This exporter writes ordinary kernel-checked Lean proofs, not trusted evidence.
The catalogue example is staged until the complete fresh build passes.
"""

import argparse
import json
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--atlas', type=int, required=True, choices=[130, 203])
    parser.add_argument('--trace-stages', action='store_true', help='Temporary development diagnostics.')
    args = parser.parse_args()
    atlas = args.atlas
    example_path = Path(f'lean/Taeyoung/Examples/Graph{atlas}.lean')
    assert 'formalization := .verified' not in example_path.read_text(encoding='utf-8'), 'Preserve accepted row sources.'

    def adapt(text):
        if atlas == 130:
            return text
        text = text.replace('target130', 'target203').replace('graph130', 'graph203')
        text = text.replace('satisfiesLowerBound_130', 'satisfiesLowerBound_203')
        text = text.replace('(2 : Real)/3', '(3 : Real)/4').replace('(1 : Real)/2', '(2 : Real)/3')
        text = text.replace('(3+s)/6', '(8+s)/12')
        text = text.replace('let s := 6*cliqueDensity 2 W-3', 'let s := 12*cliqueDensity 2 W-8')
        text = text.replace('Induced.penaltyCoefficient_eval ', 'Induced.penaltyCoefficient_eval_twoThirdsThreeQuarters ')
        return text.replace('atlas130/lower_stage.txt', 'atlas203/lower_stage.txt')
    parent = f'Taeyoung.Methods.RootedSOS.CompactS4.Atlas{atlas}'
    prefix = 'Taeyoung.Methods.RootedSOS'
    out = Path('lean') / Path(*parent.split('.'))
    common = json.loads(Path('experiments/induced_six_sparse_witness.json').read_text(encoding='utf-8'))
    assembly = json.loads(Path(f'lean/verification_runs/atlas{atlas}/lower_interval_assembly.json').read_text(encoding='utf-8'))
    body = assembly['imports'] + f'''
import {prefix}.MatrixContraction
import {prefix}.Induced.Six.FlatBlocks

namespace {parent}
{assembly['theorem']}
end {parent}

namespace {parent}.Lower
open Finset MeasureTheory Taeyoung
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]

def weightedRight (k : Fin 3632) (s : Real) : Real :=
  (right k 0 : Real)*(1-s)^2+(right k 1 : Real)*s*(1-s)+(right k 2 : Real)*s^2
def weightedGroup (g : Fin 156) (s : Real) : Real :=
  (groupTotal g 0 : Real)*(1-s)^2+(groupTotal g 1 : Real)*s*(1-s)+(groupTotal g 2 : Real)*s^2
def residualValue (g : Fin 156) (s : Real) : Real :=
  ∑ k : Fin 6, (residualCoefficient g k : Real)*Induced.basis 5 s k.1
def multiplierValue (j : Fin 11) (s : Real) : Real :=
  Induced.bernstein4 (fun k => multiplier j k) s
'''
    for ti, d in enumerate(common['block_dimensions']):
        idx = f'Induced.Six.blockIndex{ti:02d} i j'
        A, B = f'Block{2*ti:02d}.H', f'Block{2*ti+1:02d}.H'
        start, stop = common['block_offsets'][ti:ti+2]
        body += f'''
theorem blockRight{ti:02d} (i j : Fin {d}) (u : Fin 3) :
    right ({idx}) u =
      if u.1 = 0 then {A} i j
      else if u.1 = 1 then {A} i ({d}+j.1)+{A} ({d}+i.1) j+{B} i j
      else {A} ({d}+i.1) ({d}+j.1) := by
  rw [((rightCheck_all ({idx})).1 u).2]
  unfold expandedRight
'''
        for prev in range(ti):
            bound = common['block_offsets'][prev+1]
            body += f'''  have h{prev} : ¬ ({idx}).1 < {bound} := by
    rw [Induced.Six.blockIndex{ti:02d}_val]; omega
  rw [if_neg h{prev}]
'''
        if ti < 13:
            body += f'''  have hi : ({idx}).1 < {stop} := by
    rw [Induced.Six.blockIndex{ti:02d}_val]; omega
  rw [if_pos hi]
'''
        body += f'''  have ha : (({idx}).1-{start})/{d} = i.1 := by
    rw [Induced.Six.blockIndex{ti:02d}_val]; omega
  have hb : (({idx}).1-{start})%{d} = j.1 := by
    rw [Induced.Six.blockIndex{ti:02d}_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix{ti:02d} (i j : Fin {d}) (s : Real) :
    weightedRight ({idx}) s = Type{ti:02d}.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients {A} {B}
    (fun u => right ({idx}) u) i j (blockRight{ti:02d} i j) s

theorem blockNonneg{ti:02d} (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin {d}, ∑ j : Fin {d}, weightedRight ({idx}) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g ({idx}) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix{ti:02d}, Induced.Six.blockPulled{ti:02d}]
  exact Induced.Six.Family{ti:02d}.gram_nonneg W (Type{ti:02d}.matrix s)
    (Type{ti:02d}.matrix_nonneg hs0 hs1)
'''
    terms = [f'(blockNonneg{i:02d} W s hs0 hs1)' for i in range(14)]
    positive = terms[0]
    for term in terms[1:]:
        positive = f'(add_nonneg {positive} {term})'
    body += f'''
theorem dense_nonneg (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ k : Fin 3632, weightedRight k s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g k : Real)*Induced.Six.density g W) := by
  rw [Induced.Six.sum_all_blocks]
  exact {positive}

theorem group_nonneg (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ g : Fin 156, weightedGroup g s*Induced.Six.density g W := by
  let w : Fin 3 → Real := fun u => if u.1 = 0 then (1-s)^2 else if u.1 = 1 then s*(1-s) else s^2
  have hw0 : w 0 = (1-s)^2 := rfl
  have hw1 : w 1 = s*(1-s) := rfl
  have hw2 : w 2 = s^2 := rfl
  have he := integer_contraction_eval (U := Fin 3) Induced.Six.Sparse.pulled
    (fun k u => right k u) (fun g u => groupTotal g u) groupTotal_exact w
    (fun g => Induced.Six.density g W)
  simp only [Fin.sum_univ_three, hw0, hw1, hw2] at he
  norm_num at he
  have h := dense_nonneg W s hs0 hs1
  unfold weightedRight at h
  unfold weightedGroup
  simp only [mul_assoc] at h ⊢
  rwa [← he]

theorem coefficient_identity (g : Fin 156) (s : Real) :
    (denominator : Real)*(Target.coefficient g : Real) -
      (denominator : Real)*target130 ((3+s)/6)*(Induced.Six.HomIdentities.plainCoefficient 0 g : Real) =
      weightedGroup g s+residualValue g s+
        ∑ j : Fin 11, multiplierValue j s*((Induced.Six.HomIdentities.edgeCoefficient j g : Real)-
          (3+s)/6*(Induced.Six.HomIdentities.plainCoefficient j g : Real)) := by
  have he := congrArg (fun f : Fin 6 → Int => ∑ k : Fin 6, (f k : Real)*Induced.basis 5 s k.1)
    (funext (fun k => (coefficientCheck_all g k).2))
  simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib] at he
  have hc :
      (∑ k : Fin 6, (((Nat.choose 5 k.1 : Int)*(denominator*Target.coefficient g) : Int) : Real)*
        Induced.basis 5 s k.1) = ((denominator*Target.coefficient g : Int) : Real) := by
    simpa only [Int.cast_mul] using Induced.constantCoefficient_eval (denominator*Target.coefficient g) s
  rw [hc] at he
  have ht :
      (∑ k : Fin 6, ((targetNumerator k*Induced.Six.HomIdentities.plainCoefficient 0 g : Int) : Real)*Induced.basis 5 s k.1) =
        (denominator : Real)*target130 ((3+s)/6)*(Induced.Six.HomIdentities.plainCoefficient 0 g : Real) := by
    rw [← targetNumerator_eval]
    simp only [Int.cast_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_right_comm _ _ _
  rw [ht] at he
  simp only [Int.cast_add, add_mul, Finset.sum_add_distrib] at he
  rw [Induced.quadraticCoefficient_eval] at he
  have hp :
      (∑ k : Fin 6, ((∑ j : Fin 11, Induced.penaltyCoefficient
        (Induced.Six.HomIdentities.plainCoefficient j g) (Induced.Six.HomIdentities.edgeCoefficient j g)
        (fun k => multiplier j k) (fun k => leftMultiplier j k) (fun k => rightMultiplier j k) k : Int) : Real)*
          Induced.basis 5 s k.1) =
        ∑ j : Fin 11, multiplierValue j s*((Induced.Six.HomIdentities.edgeCoefficient j g : Real)-
          (3+s)/6*(Induced.Six.HomIdentities.plainCoefficient j g : Real)) := by
    simp only [Int.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Induced.penaltyCoefficient_eval _ _ _ _ _
      (fun k => (multiplier_relations j k).1) (fun k => (multiplier_relations j k).2) s
  rw [hp] at he
  simpa only [Int.cast_mul, weightedGroup, residualValue] using he

private theorem density_eq_of_graph_eq {{n : Nat}}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) : homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

theorem interval_identity (W : Graphon Ω μ) (s : Real) (hp : (3+s)/6 = cliqueDensity 2 W) :
    (denominator : Real)*(homDensity graph130 W-target130 ((3+s)/6)) =
      (∑ g : Fin 156, weightedGroup g s*Induced.Six.density g W)+
        ∑ g : Fin 156, residualValue g s*Induced.Six.density g W := by
  have he := Induced.evaluated_coefficient_identity
    (fun g : Fin 156 => (Target.coefficient g : Real))
    (fun g => (Induced.Six.HomIdentities.plainCoefficient 0 g : Real))
    (fun g => weightedGroup g s) (fun g => residualValue g s)
    (fun g => Induced.Six.density g W) (fun j : Fin 11 => multiplierValue j s)
    (fun j g => (Induced.Six.HomIdentities.plainCoefficient j g : Real))
    (fun j g => (Induced.Six.HomIdentities.edgeCoefficient j g : Real))
    (denominator : Real) ((denominator : Real)*target130 ((3+s)/6)) ((3+s)/6)
    (fun g => coefficient_identity g s)
  have ht : (∑ g : Fin 156, (Target.coefficient g : Real)*Induced.Six.density g W) =
      homDensity graph130 W := by
    calc
      _ = homDensity Target.graph W := (Target.density_expansion W).symm
      _ = homDensity graph130 W := density_eq_of_graph_eq _ _ W rfl
  rw [ht, Induced.Six.HomIdentities.plain_expansion, Induced.Six.HomIdentities.empty_density, mul_one] at he
  simp_rw [Induced.Six.HomIdentities.edge_expansion, Induced.Six.HomIdentities.plain_expansion,
    Induced.Six.HomIdentities.fixed_density, ← hp] at he
  simpa only [sub_self, mul_zero, Finset.sum_const_zero, add_zero, mul_sub] using he

theorem lower_graphon_bound (W : Graphon Ω μ) (hp0 : (1 : Real)/2 ≤ cliqueDensity 2 W)
    (hp1 : cliqueDensity 2 W ≤ (2 : Real)/3) :
    target130 (cliqueDensity 2 W) ≤ homDensity graph130 W := by
  let s := 6*cliqueDensity 2 W-3
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hp : (3+s)/6 = cliqueDensity 2 W := by dsimp [s]; ring
  have he := interval_identity W s hp
  rw [hp] at he
  have hr : 0 ≤ ∑ g : Fin 156, residualValue g s*Induced.Six.density g W := by
    apply Finset.sum_nonneg
    intro g _
    apply mul_nonneg _ (Induced.Six.density_nonneg g W)
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg _ (Induced.basis_nonneg 5 k.1 hs0 hs1)
    exact_mod_cast (coefficientCheck_all g k).1
  have hn : 0 ≤ (denominator : Real)*(homDensity graph130 W-target130 (cliqueDensity 2 W)) := by
    rw [he]
    exact add_nonneg (group_nonneg W s hs0 hs1) hr
  have hd : (0 : Real) < (denominator : Real) := by norm_num [denominator]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp hn)
#print axioms lower_graphon_bound
end {parent}.Lower
'''
    if args.trace_stages:
        body = re.sub(r'(?m)^(?=(?:private )?theorem ([A-Za-z0-9_.]+))',
                      lambda m: f'run_cmd Lean.Elab.Command.liftIO (IO.FS.writeFile "verification_runs/atlas130/lower_stage.txt" "checking {m[1]}")\n', body)
    (out/'LowerCertificate.lean').write_text(adapt(body), encoding='utf-8')
    certificate=f'''import {parent}.UpperCertificate
import {parent}.LowerCertificate
namespace {parent}
open MeasureTheory Taeyoung
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]
theorem graphon_bound (W : Graphon Ω μ) (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) :
    target130 (cliqueDensity 2 W) ≤ homDensity graph130 W := by
  by_cases h : cliqueDensity 2 W ≤ (2 : Real)/3
  · exact Lower.lower_graphon_bound W hp h
  · exact upper_graphon_bound W (le_of_lt (lt_of_not_ge h))
theorem satisfiesLowerBound_130 : SatisfiesLowerBound graph130 :=
  satisfiesLowerBound_130_of_bound (fun W hp => graphon_bound W hp)
#print axioms satisfiesLowerBound_130
end {parent}
'''
    (out/'Certificate.lean').write_text(adapt(certificate), encoding='utf-8')
    example = Path(f'lean/Taeyoung/Examples/Graph{atlas}.lean').read_text(encoding='utf-8')
    assert 'formalization := .unresolved' in example
    example = example.replace('import Taeyoung.Foundation', f'import {parent}.Certificate')
    example = example.replace('formalization := .unresolved', 'formalization := .verified')
    first = example.index('/-- The full mathematical bound')
    last = example.index(f'end Taeyoung.Examples.Graph{atlas}')
    example = example[:first] + f'''/-- Complete catalogue bound, with both density intervals checked in Lean. -/
theorem status : SatisfiesLowerBound graph :=
  {parent}.satisfiesLowerBound_{atlas}

#print axioms status

''' + example[last:]
    staged = Path(f'lean/verification_runs/atlas{atlas}/prepared/Graph{atlas}.lean')
    staged.parent.mkdir(parents=True, exist_ok=True)
    staged.write_text(example, encoding='utf-8')
    print('Generated LowerCertificate, complete Certificate, and staged example; live example unmodified.')


if __name__ == '__main__':
    main()
