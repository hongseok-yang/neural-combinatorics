"""Join the 22 shared homomorphism expansions with disjoint-edge identities."""

import json
from pathlib import Path


def main():
    common=json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    parent='Taeyoung.Methods.RootedSOS.Induced.Six'
    ns=parent+'.HomIdentities'
    text='\n'.join(f'import {parent}.Hom{edge}{i:02d}' for i in range(11) for edge in ('','Edge'))+'\n'
    text+=f'''import Taeyoung.Foundation.DisjointUnion
import Taeyoung.Methods.RootedSOS.GraphCanonical
namespace {ns}
open Finset MeasureTheory Taeyoung
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]
private theorem density_eq_of_graph_eq {{n : Nat}}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) : homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl
'''
    for i,code in enumerate(common['four_codes']):
        edges=[tuple(e) for k,e in enumerate(common['pairs']) if code>>k&1]
        text+=f'''
private def core{i:02d} : SimpleGraph (Fin 4) := graphFromEdges 4 {edges}
private instance : DecidableRel core{i:02d}.Adj := by unfold core{i:02d}; infer_instance
private theorem plain_graph{i:02d} : Hom{i:02d}.graph = core{i:02d}.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph{i:02d} : HomEdge{i:02d}.graph = disjointUnion core{i:02d} (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed{i:02d} (W : Graphon Ω μ) :
    homDensity HomEdge{i:02d}.graph W = cliqueDensity 2 W*homDensity Hom{i:02d}.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph{i:02d}, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph{i:02d}, homDensity_disjointUnion]
  exact mul_comm _ _
'''
    text+='\ndef plainCoefficient : Fin 11 → Fin 156 → Int := !['+', '.join(f'Hom{i:02d}.coefficient' for i in range(11))+']\n'
    text+='def edgeCoefficient : Fin 11 → Fin 156 → Int := !['+', '.join(f'HomEdge{i:02d}.coefficient' for i in range(11))+']\n'
    text+='noncomputable def plainDensity (W : Graphon Ω μ) : Fin 11 → Real := !['+', '.join(f'homDensity Hom{i:02d}.graph W' for i in range(11))+']\n'
    text+='noncomputable def edgeDensity (W : Graphon Ω μ) : Fin 11 → Real := !['+', '.join(f'homDensity HomEdge{i:02d}.graph W' for i in range(11))+']\n'
    text+='''theorem plain_expansion (j : Fin 11) (W : Graphon Ω μ) :
    (∑ g : Fin 156, (plainCoefficient j g : Real)*density g W) = plainDensity W j := by
  fin_cases j
'''+''.join(f'  · exact (Hom{i:02d}.density_expansion W).symm\n' for i in range(11))
    text+='''theorem edge_expansion (j : Fin 11) (W : Graphon Ω μ) :
    (∑ g : Fin 156, (edgeCoefficient j g : Real)*density g W) = edgeDensity W j := by
  fin_cases j
'''+''.join(f'  · exact (HomEdge{i:02d}.density_expansion W).symm\n' for i in range(11))
    text+='''theorem fixed_density (j : Fin 11) (W : Graphon Ω μ) :
    edgeDensity W j = cliqueDensity 2 W*plainDensity W j := by
  fin_cases j
'''+''.join(f'  · exact fixed{i:02d} W\n' for i in range(11))
    text+='''theorem empty_density (W : Graphon Ω μ) : plainDensity W 0 = 1 := by
  change homDensity Hom00.graph W = 1
  have he : Hom00.graph.edgeFinset = ∅ := by decide +kernel
  simp [homDensity, graphWeight, he]
#print axioms fixed_density
'''+f'end {ns}\n'
    path=Path('lean/Taeyoung/Methods/RootedSOS/Induced/Six/HomIdentities.lean')
    path.write_text(text,encoding='utf-8')
    print(path,path.stat().st_size,flush=True)


if __name__=='__main__':
    main()
