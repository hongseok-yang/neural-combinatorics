"""Induced-completion expansions of four-vertex graphs and their disjoint edges."""

import argparse
import json
from pathlib import Path

from generate_compact_s4_psd import table

PARENT='Taeyoung.Methods.RootedSOS.Induced.Six'
ROOT=Path('lean/Taeyoung/Methods/RootedSOS/Induced/Six')


def render(common,ns,required,graph_expression,extra_import=''):
    present=[i for i in range(15) if required>>i&1]
    free=[i for i in range(15) if not required>>i&1]
    d,f=len(present),len(free)
    size=2**f
    chunk=min(512,size);blocks=size//chunk
    base,bound=common['histogram_base'],common['histogram_bound']
    offset=bound*sum(base**g for g in range(156))
    completions=[required+sum(1<<e for k,e in enumerate(free) if a>>k&1) for a in range(size)]
    powers=[base**common['classification'][mask][0] for mask in completions]
    histograms=[sum(powers[start:start+chunk]) for start in range(0,size,chunk)]
    code=offset+sum(histograms)
    inverse=['']*15
    for i,e in enumerate(present):inverse[e]=f'Sum.inl {i}'
    for i,e in enumerate(free):inverse[e]=f'Sum.inr {i}'
    text=f'''import {PARENT}.Classification
import {PARENT}.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding
{extra_import}
namespace {ns}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := {graph_expression}
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin {d} → Fin 15 := ![{', '.join(map(str,present))}]
def freeIndex : Fin {f} → Fin 15 := ![{', '.join(map(str,free))}]
def edgeMap : Fin {d} ⊕ Fin {f} → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin {d} ⊕ Fin {f} := ![{', '.join(inverse)}]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin {d} ⊕ Fin {f} ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin {d} => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin {d} => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin {size}) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := {table(histograms)}
def histogram (b : Fin {blocks}) : Int := histogramData.get b
def countCode : Nat := {code}
def coefficient (g : Fin 156) : Int := decodeSignedDigit {base} {bound} countCode g
private theorem count_total : (countCode : Int) = {offset} + ∑ b, histogram b := by decide +kernel
'''
    for b in range(blocks):
        text+=f'''private theorem block_{b:03d} : histogram {b} =
    ∑ i : Fin {chunk}, groupPower (host (completion (finProdFinEquiv (({b} : Fin {blocks}),i)))) := by decide +kernel
'''
    text+=f'''theorem histogram_exact (b : Fin {blocks}) : histogram b =
    ∑ i : Fin {chunk}, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
'''+''.join(f'  · exact block_{b:03d}\n' for b in range(blocks))
    text+=f'''
theorem countCode_exact : (countCode : Int) = ({bound} : Int)*geometricEncoding {base} 156 +
    ∑ a : Fin {size}, ({base} : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin {blocks} × Fin {chunk} ≃ Fin {size}).sum_comp
    (fun a : Fin {size} => ({base} : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin {size}, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin {f} → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin {size} => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end {ns}
'''
    return text


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--atlas',type=int)
    args=parser.parse_args()
    common=json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    if args.atlas is not None:
        candidate=json.loads(Path(f'experiments/atlas{args.atlas}_compact_lower_candidate.json').read_text(encoding='utf-8'))
        atlas=args.atlas
        parent=f'Taeyoung.Methods.RootedSOS.CompactS4.Atlas{atlas}'
        path=Path(f'lean/Taeyoung/Methods/RootedSOS/CompactS4/Atlas{atlas}/LowerTarget.lean')
        path.write_text(render(common,parent+'.Lower.Target',candidate['target_code'],f'{parent}.graph{atlas}',
                               f'import {parent}.Coloring'),encoding='utf-8')
        print(path,path.stat().st_size,flush=True)
        return
    for j,code in enumerate(common['four_codes']):
        for is_edge in (False,True):
            mask=code|(1<<14) if is_edge else code
            edges=[tuple(e) for i,e in enumerate(common['pairs']) if mask>>i&1]
            stem=f'Hom{"Edge" if is_edge else ""}{j:02d}'
            path=ROOT/f'{stem}.lean'
            path.write_text(render(common,PARENT+'.'+stem,mask,f'graphFromEdges 6 {edges}'),encoding='utf-8')
            print(stem,path.stat().st_size,flush=True)


if __name__=='__main__':
    main()
