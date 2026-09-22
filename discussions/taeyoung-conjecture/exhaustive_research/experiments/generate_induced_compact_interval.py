"""Generate the exact degree-five lower-interval coefficient identity."""

import argparse
import json
import math
from pathlib import Path

import generate_compact_s4_group_totals as chunks
from generate_compact_s4_psd import PREFIX,matrix,table


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('candidate')
    args=parser.parse_args()
    c=json.loads(Path(args.candidate).read_text(encoding='utf-8'))
    common=json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    atlas=c['atlas']
    assert c['interval'] in [['1/2','2/3'],['2/3','3/4']]
    is203 = c['interval']==['2/3','3/4']
    relations=('3*leftMultiplier j k = 2*multiplier j k ∧ 4*rightMultiplier j k = 3*multiplier j k'
               if is203 else '2*leftMultiplier j k = multiplier j k ∧ 3*rightMultiplier j k = 2*multiplier j k')
    point='(8+s)/12' if is203 else '(3+s)/6'
    extra_import=f'import {PREFIX}.Induced.AffineBernstein\n' if is203 else ''
    D=c['denominator']
    residual=[[math.comb(5,k)*v*common['orbit_sizes'][g] for k,v in enumerate(row)]
              for g,row in enumerate(c['slacks'])]
    target=[math.comb(5,k)*v for k,v in enumerate(c['target_bernstein'])]
    assert all(v>=0 for row in residual for v in row)
    chunks.configure(atlas)
    parent=chunks.NS;ns=parent+'.Lower'
    hi='Induced.Six.HomIdentities'
    body=f'''import {parent}.LowerContraction
import {parent}.LowerTarget
import {PREFIX}.Induced.Six.HomIdentities
import {PREFIX}.Induced.CoefficientIdentity
{extra_import}\
namespace {ns}
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
def denominator : Int := {D}
{matrix('residualCoefficient',residual)}
{matrix('multiplier',c['multipliers'])}
{matrix('leftMultiplier',c['left_multipliers'])}
{matrix('rightMultiplier',c['right_multipliers'])}
private def targetNumeratorData : PackedTable := {table(target)}
def targetNumerator (k : Fin 6) : Int := targetNumeratorData.get k
theorem multiplier_relations : ∀ (j : Fin 11) (k : Fin 5),
    {relations} := by decide +kernel
theorem targetNumerator_eval (s : Real) :
    (∑ k : Fin 6, (targetNumerator k : Real)*Induced.basis 5 s k.1) =
      denominator*target{atlas} ({point}) := by
  simp [targetNumerator, targetNumeratorData, denominator, target{atlas},
    Induced.basis, Fin.sum_univ_succ, PackedTable.get]
  ring
def coefficientCheck (g : Fin 156) : Prop := ∀ k : Fin 6,
  0 ≤ residualCoefficient g k ∧
  (Nat.choose 5 k.1 : Int)*(denominator*Target.coefficient g) -
    targetNumerator k*{hi}.plainCoefficient 0 g =
      Induced.quadraticCoefficient (groupTotal g 0) (groupTotal g 1) (groupTotal g 2) k +
        residualCoefficient g k +
        ∑ j : Fin 11, Induced.penaltyCoefficient ({hi}.plainCoefficient j g) ({hi}.edgeCoefficient j g)
          (fun k => multiplier j k) (fun k => leftMultiplier j k) (fun k => rightMultiplier j k) k
instance (g : Fin 156) : Decidable (coefficientCheck g) := by unfold coefficientCheck; infer_instance
end {ns}
'''
    chunks.write('LowerIntervalBase',body)
    imports,thm=chunks.chunks('LowerIntervalChecks','LowerIntervalBase','Lower.coefficientCheck',156,78,1)
    output=Path(f'lean/verification_runs/atlas{atlas}/lower_interval_assembly.json')
    output.write_text(json.dumps(dict(imports=imports,theorem=thm),indent=2)+'\n',encoding='utf-8')
    print(f'Generated three interval data/check files for Atlas{atlas}.',flush=True)


if __name__=='__main__':
    main()
