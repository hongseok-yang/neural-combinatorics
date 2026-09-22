import Taeyoung.Methods.RootedSOS.Induced.Six.Hom00
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge00
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom01
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge01
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom02
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge02
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom03
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge03
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom04
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge04
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom05
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge05
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom06
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge06
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom07
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge07
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom08
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge08
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom09
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge09
import Taeyoung.Methods.RootedSOS.Induced.Six.Hom10
import Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge10
import Taeyoung.Foundation.DisjointUnion
import Taeyoung.Methods.RootedSOS.GraphCanonical
namespace Taeyoung.Methods.RootedSOS.Induced.Six.HomIdentities
open Finset MeasureTheory Taeyoung
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
private theorem density_eq_of_graph_eq {n : Nat}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) : homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

private def core00 : SimpleGraph (Fin 4) := graphFromEdges 4 []
private instance : DecidableRel core00.Adj := by unfold core00; infer_instance
private theorem plain_graph00 : Hom00.graph = core00.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph00 : HomEdge00.graph = disjointUnion core00 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed00 (W : Graphon Ω μ) :
    homDensity HomEdge00.graph W = cliqueDensity 2 W*homDensity Hom00.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph00, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph00, homDensity_disjointUnion]
  exact mul_comm _ _

private def core01 : SimpleGraph (Fin 4) := graphFromEdges 4 [(2, 3)]
private instance : DecidableRel core01.Adj := by unfold core01; infer_instance
private theorem plain_graph01 : Hom01.graph = core01.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph01 : HomEdge01.graph = disjointUnion core01 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed01 (W : Graphon Ω μ) :
    homDensity HomEdge01.graph W = cliqueDensity 2 W*homDensity Hom01.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph01, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph01, homDensity_disjointUnion]
  exact mul_comm _ _

private def core02 : SimpleGraph (Fin 4) := graphFromEdges 4 [(1, 3), (2, 3)]
private instance : DecidableRel core02.Adj := by unfold core02; infer_instance
private theorem plain_graph02 : Hom02.graph = core02.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph02 : HomEdge02.graph = disjointUnion core02 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed02 (W : Graphon Ω μ) :
    homDensity HomEdge02.graph W = cliqueDensity 2 W*homDensity Hom02.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph02, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph02, homDensity_disjointUnion]
  exact mul_comm _ _

private def core03 : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 1), (2, 3)]
private instance : DecidableRel core03.Adj := by unfold core03; infer_instance
private theorem plain_graph03 : Hom03.graph = core03.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph03 : HomEdge03.graph = disjointUnion core03 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed03 (W : Graphon Ω μ) :
    homDensity HomEdge03.graph W = cliqueDensity 2 W*homDensity Hom03.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph03, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph03, homDensity_disjointUnion]
  exact mul_comm _ _

private def core04 : SimpleGraph (Fin 4) := graphFromEdges 4 [(1, 2), (1, 3), (2, 3)]
private instance : DecidableRel core04.Adj := by unfold core04; infer_instance
private theorem plain_graph04 : Hom04.graph = core04.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph04 : HomEdge04.graph = disjointUnion core04 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed04 (W : Graphon Ω μ) :
    homDensity HomEdge04.graph W = cliqueDensity 2 W*homDensity Hom04.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph04, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph04, homDensity_disjointUnion]
  exact mul_comm _ _

private def core05 : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 3), (1, 3), (2, 3)]
private instance : DecidableRel core05.Adj := by unfold core05; infer_instance
private theorem plain_graph05 : Hom05.graph = core05.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph05 : HomEdge05.graph = disjointUnion core05 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed05 (W : Graphon Ω μ) :
    homDensity HomEdge05.graph W = cliqueDensity 2 W*homDensity Hom05.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph05, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph05, homDensity_disjointUnion]
  exact mul_comm _ _

private def core06 : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 1), (0, 3), (1, 2)]
private instance : DecidableRel core06.Adj := by unfold core06; infer_instance
private theorem plain_graph06 : Hom06.graph = core06.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph06 : HomEdge06.graph = disjointUnion core06 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed06 (W : Graphon Ω μ) :
    homDensity HomEdge06.graph W = cliqueDensity 2 W*homDensity Hom06.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph06, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph06, homDensity_disjointUnion]
  exact mul_comm _ _

private def core07 : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 3), (1, 2), (1, 3), (2, 3)]
private instance : DecidableRel core07.Adj := by unfold core07; infer_instance
private theorem plain_graph07 : Hom07.graph = core07.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph07 : HomEdge07.graph = disjointUnion core07 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed07 (W : Graphon Ω μ) :
    homDensity HomEdge07.graph W = cliqueDensity 2 W*homDensity Hom07.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph07, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph07, homDensity_disjointUnion]
  exact mul_comm _ _

private def core08 : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 1), (0, 3), (1, 2), (2, 3)]
private instance : DecidableRel core08.Adj := by unfold core08; infer_instance
private theorem plain_graph08 : Hom08.graph = core08.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph08 : HomEdge08.graph = disjointUnion core08 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed08 (W : Graphon Ω μ) :
    homDensity HomEdge08.graph W = cliqueDensity 2 W*homDensity Hom08.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph08, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph08, homDensity_disjointUnion]
  exact mul_comm _ _

private def core09 : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)]
private instance : DecidableRel core09.Adj := by unfold core09; infer_instance
private theorem plain_graph09 : Hom09.graph = core09.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph09 : HomEdge09.graph = disjointUnion core09 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed09 (W : Graphon Ω μ) :
    homDensity HomEdge09.graph W = cliqueDensity 2 W*homDensity Hom09.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph09, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph09, homDensity_disjointUnion]
  exact mul_comm _ _

private def core10 : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
private instance : DecidableRel core10.Adj := by unfold core10; infer_instance
private theorem plain_graph10 : Hom10.graph = core10.map (Fin.castAdd 2) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
private theorem edge_graph10 : HomEdge10.graph = disjointUnion core10 (⊤ : SimpleGraph (Fin 2)) :=
  (adjacencyCode_eq_iff _ _).mp (by decide +kernel)
theorem fixed10 (W : Graphon Ω μ) :
    homDensity HomEdge10.graph W = cliqueDensity 2 W*homDensity Hom10.graph W := by
  rw [density_eq_of_graph_eq _ _ W plain_graph10, homDensity_map_castAdd]
  rw [density_eq_of_graph_eq _ _ W edge_graph10, homDensity_disjointUnion]
  exact mul_comm _ _

def plainCoefficient : Fin 11 → Fin 156 → Int := ![Hom00.coefficient, Hom01.coefficient, Hom02.coefficient, Hom03.coefficient, Hom04.coefficient, Hom05.coefficient, Hom06.coefficient, Hom07.coefficient, Hom08.coefficient, Hom09.coefficient, Hom10.coefficient]
def edgeCoefficient : Fin 11 → Fin 156 → Int := ![HomEdge00.coefficient, HomEdge01.coefficient, HomEdge02.coefficient, HomEdge03.coefficient, HomEdge04.coefficient, HomEdge05.coefficient, HomEdge06.coefficient, HomEdge07.coefficient, HomEdge08.coefficient, HomEdge09.coefficient, HomEdge10.coefficient]
noncomputable def plainDensity (W : Graphon Ω μ) : Fin 11 → Real := ![homDensity Hom00.graph W, homDensity Hom01.graph W, homDensity Hom02.graph W, homDensity Hom03.graph W, homDensity Hom04.graph W, homDensity Hom05.graph W, homDensity Hom06.graph W, homDensity Hom07.graph W, homDensity Hom08.graph W, homDensity Hom09.graph W, homDensity Hom10.graph W]
noncomputable def edgeDensity (W : Graphon Ω μ) : Fin 11 → Real := ![homDensity HomEdge00.graph W, homDensity HomEdge01.graph W, homDensity HomEdge02.graph W, homDensity HomEdge03.graph W, homDensity HomEdge04.graph W, homDensity HomEdge05.graph W, homDensity HomEdge06.graph W, homDensity HomEdge07.graph W, homDensity HomEdge08.graph W, homDensity HomEdge09.graph W, homDensity HomEdge10.graph W]
theorem plain_expansion (j : Fin 11) (W : Graphon Ω μ) :
    (∑ g : Fin 156, (plainCoefficient j g : Real)*density g W) = plainDensity W j := by
  fin_cases j
  · exact (Hom00.density_expansion W).symm
  · exact (Hom01.density_expansion W).symm
  · exact (Hom02.density_expansion W).symm
  · exact (Hom03.density_expansion W).symm
  · exact (Hom04.density_expansion W).symm
  · exact (Hom05.density_expansion W).symm
  · exact (Hom06.density_expansion W).symm
  · exact (Hom07.density_expansion W).symm
  · exact (Hom08.density_expansion W).symm
  · exact (Hom09.density_expansion W).symm
  · exact (Hom10.density_expansion W).symm
theorem edge_expansion (j : Fin 11) (W : Graphon Ω μ) :
    (∑ g : Fin 156, (edgeCoefficient j g : Real)*density g W) = edgeDensity W j := by
  fin_cases j
  · exact (HomEdge00.density_expansion W).symm
  · exact (HomEdge01.density_expansion W).symm
  · exact (HomEdge02.density_expansion W).symm
  · exact (HomEdge03.density_expansion W).symm
  · exact (HomEdge04.density_expansion W).symm
  · exact (HomEdge05.density_expansion W).symm
  · exact (HomEdge06.density_expansion W).symm
  · exact (HomEdge07.density_expansion W).symm
  · exact (HomEdge08.density_expansion W).symm
  · exact (HomEdge09.density_expansion W).symm
  · exact (HomEdge10.density_expansion W).symm
theorem fixed_density (j : Fin 11) (W : Graphon Ω μ) :
    edgeDensity W j = cliqueDensity 2 W*plainDensity W j := by
  fin_cases j
  · exact fixed00 W
  · exact fixed01 W
  · exact fixed02 W
  · exact fixed03 W
  · exact fixed04 W
  · exact fixed05 W
  · exact fixed06 W
  · exact fixed07 W
  · exact fixed08 W
  · exact fixed09 W
  · exact fixed10 W
theorem empty_density (W : Graphon Ω μ) : plainDensity W 0 = 1 := by
  change homDensity Hom00.graph W = 1
  have he : Hom00.graph.edgeFinset = ∅ := by decide +kernel
  simp [homDensity, graphWeight, he]
#print axioms fixed_density
end Taeyoung.Methods.RootedSOS.Induced.Six.HomIdentities
