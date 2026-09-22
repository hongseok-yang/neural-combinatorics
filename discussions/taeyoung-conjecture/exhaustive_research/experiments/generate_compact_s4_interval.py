"""Generate exact half- or third-interval polynomial checks for compact rows."""

import argparse
import json
from pathlib import Path

from generate_compact_s4_psd import PREFIX, table
import generate_compact_s4_group_totals as groups


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('witness')
    args=parser.parse_args()
    w=json.loads(Path(args.witness).read_text(encoding='utf-8'))
    atlas=w['atlas']
    assert w['empty_group']==0
    scale=w['scale']
    offset=w['affine_offset']
    divisor=w['affine_denominator']
    generic=w.get('coefficient_kind')=='affine_degree_five'
    assert generic or (offset,divisor,scale) in [(1,2,16),(2,3,81),(2,3,243),(3,4,256)]
    coefficient='intervalCoefficient' if divisor==2 else 'thirdIntervalCoefficient'
    coefficient_module='IntervalCoefficients' if divisor==2 else 'ThirdIntervalCoefficients'
    if scale==243:
        coefficient='thirdDegreeFiveCoefficient'
        coefficient_module='ThirdDegreeFiveCoefficients'
    if divisor==4:
        coefficient='quarterIntervalCoefficient'
        coefficient_module='QuarterIntervalCoefficients'
    affine_point=f'({offset}+s)/{divisor}'
    coefficient_eval=f'{coefficient}_eval _ (isolated_bound g)'
    if generic:
        assert scale==divisor**5
        step=w['affine_step']
        coefficient=f'affineIntervalCoefficient {offset} {step} {divisor}'
        coefficient_module='AffineIntervalCoefficients'
        coefficient_eval=f'affineIntervalCoefficient_eval {offset} {step} {divisor} _ (by decide) (isolated_bound g)'
        affine_point=f'({offset}+{step}*s)/{divisor}'
    polynomial=' + '.join(f'({v})*s^{j}' for j,v in enumerate(w['target_coefficients']))
    coefficient_cases=''.join(f'if j = {j} then ({v}) else '
                              for j,v in enumerate(w['target_coefficients'][:-1]))
    coefficient_cases+=f"({w['target_coefficients'][-1]})"
    groups.configure(atlas, w.get('lean_namespace_suffix', ''))
    NS,write,chunks=groups.NS,groups.write,groups.chunks
    target=w['target_group']
    den=w['denominator']
    write('IntervalBase',f'''import {NS}.GroupData
import {PREFIX}.CompactS4.Atlas{atlas}.Coloring
import {PREFIX}.CompactS4.Groups
import {PREFIX}.{coefficient_module}

namespace {NS}
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def representativeData : PackedTable := {table(w['representatives'])}
def representative (g : Fin 143) : Fin 143 :=
  ⟨(representativeData.get g).toNat % 143, Nat.mod_lt _ (by decide)⟩

theorem isolated_bound : ∀ g : Fin 143, (S4Classification.groupKey g).2 ≤ 3 := by decide +kernel

private theorem core_codes : ∀ g : Fin 143,
    adjacencyCode (S4Classification.coreGraph6 g) =
      adjacencyCode (S4Classification.coreGraph6 (representative g)) := by decide +kernel

theorem core_eq (g : Fin 143) : S4Classification.coreGraph6 g =
    S4Classification.coreGraph6 (representative g) := (adjacencyCode_eq_iff _ _).mp (core_codes g)

theorem target_core : S4Classification.coreGraph6 {target} = graph{atlas} :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)

theorem empty_core : S4Classification.coreGraph6 0 = (⊥ : SimpleGraph (Fin 6)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)

def polynomialCoefficient (g : Fin 143) (j : Fin 6) : Int :=
  {coefficient} (S4Classification.groupKey g).2
    (groupTotal g 0) (groupTotal g 1 + groupTotal g 3)
    (groupTotal g 2 - groupTotal g 3) j

def targetCoefficient (r : Fin 143) (j : Fin 6) : Int :=
  (if r = {target} then (if j = 0 then {scale}*{den} else 0) else 0) -
  (if r = 0 then {den} *
    ({coefficient_cases}) else 0)

def polynomialCheck (r : Fin 143) : Prop := ∀ j : Fin 6,
  (∑ g : Fin 143, if representative g = r then polynomialCoefficient g j else 0) =
    targetCoefficient r j

instance (r : Fin 143) : Decidable (polynomialCheck r) := by unfold polynomialCheck; infer_instance

end {NS}
''')
    imports,thm=chunks('IntervalChecks','IntervalBase','polynomialCheck',143,26,1)
    final=imports+f'''
namespace {NS}
open Finset
{thm}
theorem group_polynomial_eval (g : Fin 143) (s : Real) :
    (∑ j : Fin 6, (polynomialCoefficient g j : Real)*s^j.1) =
      {scale}*({affine_point})^(S4Classification.groupKey g).2 *
        ((groupTotal g 0 : Real)+(groupTotal g 1 : Real)*s+
          (groupTotal g 2 : Real)*s^2+(groupTotal g 3 : Real)*s*(1-s)) := by
  rw [show polynomialCoefficient g = {coefficient} (S4Classification.groupKey g).2
      (groupTotal g 0) (groupTotal g 1 + groupTotal g 3)
      (groupTotal g 2 - groupTotal g 3) from rfl]
  rw [{coefficient_eval}]
  norm_num only [Nat.cast_ofNat]
  push_cast
  ring

theorem target_coefficient_eval (r : Fin 143) (s : Real) :
    (∑ j : Fin 6, (targetCoefficient r j : Real)*s^j.1) =
      (if r = {target} then {scale}*{den} else 0) -
      (if r = 0 then {den}*({polynomial}) else 0) := by
  by_cases h : r = {target} <;> by_cases h0 : r = 0 <;>
    simp [targetCoefficient,Fin.sum_univ_succ,h,h0] <;> ring

theorem group_identity (s : Real) (f : Fin 143 → Real) :
    {scale}*(∑ g : Fin 143,
      ((groupTotal g 0 : Real)+(groupTotal g 1 : Real)*s+
        (groupTotal g 2 : Real)*s^2+(groupTotal g 3 : Real)*s*(1-s)) *
        (({affine_point})^(S4Classification.groupKey g).2 * f (representative g))) =
      {den}*({scale}*f {target}-({polynomial})*f 0) := by
  calc
    _ = ∑ g : Fin 143,
        (∑ j : Fin 6, (polynomialCoefficient g j : Real)*s^j.1)*f (representative g) := by
      simp only [Finset.mul_sum, group_polynomial_eval]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = ∑ r : Fin 143,
        (∑ j : Fin 6, (targetCoefficient r j : Real)*s^j.1)*f r :=
      group_coefficients_eval representative polynomialCoefficient targetCoefficient
        (fun r j => polynomialCheck_all r j) (fun j => s^j.1) f
    _ = _ := by
      simp only [target_coefficient_eval, sub_mul, ite_mul, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

#print axioms group_identity
end {NS}
'''
    write('Interval',final)
    print(f'Generated 8 Atlas{atlas} interval-identity files')


if __name__=='__main__':
    main()
