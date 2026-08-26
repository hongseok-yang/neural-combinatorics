import Taeyoung.Foundation.HomDensity
import Taeyoung.Methods.RootedSOS.Atlas43PSD
import Taeyoung.Methods.RootedSOS.Bernoulli
import Taeyoung.Methods.RootedSOS.FlagGraph

/-!
# Rooted flags used by the Atlas 43 certificate

The 64 flags are ordered by binary masks on

`01, 02, 03, 12, 13, 23`.

The three label-label edges use shared Bernoulli bits.  The other three
bits record the neighbours of the single integrated branch vertex.  The main
identity in this file proves that averaging a product of two flags takes the
union of their labelled edges, exactly matching simple-graph gluing.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Atlas43Flags

open Taeyoung
open Taeyoung.Methods.RootedSOS
open Taeyoung.Methods.RootedSOS.Atlas43PSD
open Taeyoung.Methods.RootedSOS.Atlas43Gram

private def singletonIf {α : Type*} [DecidableEq α] (b : Bool) (x : α) : Finset α :=
  if b then {x} else ∅

/-- The labelled edges selected by a six-bit flag mask. -/
def flagLabelEdges (a : Fin 64) : Finset (Sym2 (Fin 3)) :=
  singletonIf (a.1.testBit 0) s(0, 1) ∪
    singletonIf (a.1.testBit 1) s(0, 2) ∪
      singletonIf (a.1.testBit 3) s(1, 2)

/-- The labelled neighbours of the branch vertex selected by a flag mask. -/
def flagBranchNeighbors (a : Fin 64) : Finset (Fin 3) :=
  singletonIf (a.1.testBit 2) 0 ∪
    singletonIf (a.1.testBit 4) 1 ∪
      singletonIf (a.1.testBit 5) 2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The branch-edge monomial before integrating the branch vertex. -/
def branchMonomial (W : Graphon Ω μ) (x : Fin 3 → Ω) (y : Ω)
    (N : Finset (Fin 3)) : ℝ :=
  rootedBranchMonomial W x y N

/-- The one-branch conditional density attached to fixed labels `x`. -/
noncomputable def branchDensity (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (N : Finset (Fin 3)) : ℝ :=
  rootedBranchDensity W x N

/-- A rooted flag evaluated at fixed labels and one shared set of successful
Bernoulli label-edge bits. -/
noncomputable def rootedFlagValue (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (A L : Finset (Sym2 (Fin 3))) (N : Finset (Fin 3)) : ℝ :=
  if L ⊆ A then branchDensity W x N else 0

/-- The kernel obtained after gluing two one-branch flags along their labels. -/
noncomputable def gluedFlagKernel (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (L₀ L₁ : Finset (Sym2 (Fin 3))) (N₀ N₁ : Finset (Fin 3)) : ℝ :=
  (∏ e ∈ L₀ ∪ L₁, edgeValue W x e) *
    branchDensity W x N₀ * branchDensity W x N₁

/-- The label graph left after the shared Bernoulli bits of two flags are
averaged. -/
def combinedLabelGraph (a b : Fin 64) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet ↑(flagLabelEdges a ∪ flagLabelEdges b)

instance combinedLabelGraph_decidableAdj (a b : Fin 64) :
    DecidableRel (combinedLabelGraph a b).Adj := by
  unfold combinedLabelGraph
  infer_instance

/-- The five-vertex ordinary graph represented by a product of two Atlas 43
rooted flags. -/
def gluedOrdinaryGraph (a b : Fin 64) : SimpleGraph (Fin 5) :=
  gluedFlagGraph (combinedLabelGraph a b)
    (flagBranchNeighbors a) (flagBranchNeighbors b)

instance gluedOrdinaryGraph_decidableAdj (a b : Fin 64) :
    DecidableRel (gluedOrdinaryGraph a b).Adj := by
  unfold gluedOrdinaryGraph
  infer_instance

private theorem combinedLabelGraph_edgeFinset_all :
    ∀ a b : Fin 64,
      (combinedLabelGraph a b).edgeFinset = flagLabelEdges a ∪ flagLabelEdges b := by
  decide +kernel

theorem combinedLabelGraph_edgeFinset (a b : Fin 64) :
    (combinedLabelGraph a b).edgeFinset = flagLabelEdges a ∪ flagLabelEdges b :=
  combinedLabelGraph_edgeFinset_all a b

theorem gluedFlagKernel_eq_rootedGluedKernel (W : Graphon Ω μ)
    (x : Fin 3 → Ω) (a b : Fin 64) :
    gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
        (flagBranchNeighbors a) (flagBranchNeighbors b) =
      rootedGluedKernel (combinedLabelGraph a b)
        (flagBranchNeighbors a) (flagBranchNeighbors b) W x := by
  simp only [gluedFlagKernel, rootedGluedKernel, branchDensity, graphWeight,
    combinedLabelGraph_edgeFinset]
  ring

/-- Every entry of the averaged Atlas 43 flag-product matrix is exactly the
homomorphism density of its explicitly glued ordinary graph. -/
theorem integral_gluedFlagKernel_eq_homDensity (W : Graphon Ω μ)
    (a b : Fin 64) :
    (∫ x, gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
        (flagBranchNeighbors a) (flagBranchNeighbors b)
      ∂(assignmentMeasure (Fin 3) μ)) =
      homDensity (gluedOrdinaryGraph a b) W := by
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun x ↦
    gluedFlagKernel_eq_rootedGluedKernel W x a b)]
  exact integral_rootedGluedKernel_eq_homDensity
    (combinedLabelGraph a b) (flagBranchNeighbors a) (flagBranchNeighbors b) W

/-- **Shared-Bernoulli rooted products are simple glued products.**  In
particular, a labelled edge present in both flags contributes one graphon
factor, not its square. -/
theorem bernoulli_rootedFlag_product (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (L₀ L₁ : Finset (Sym2 (Fin 3))) (N₀ N₁ : Finset (Fin 3)) :
    (∑ A ∈ (univ : Finset (Sym2 (Fin 3))).powerset,
      bernoulliWeight (fun e ↦ edgeValue W x e) A *
        rootedFlagValue W x A L₀ N₀ * rootedFlagValue W x A L₁ N₁) =
      gluedFlagKernel W x L₀ L₁ N₀ N₁ := by
  simpa [rootedFlagValue, gluedFlagKernel] using
    (bernoulli_indicator_product (fun e : Sym2 (Fin 3) ↦ edgeValue W x e)
      L₀ L₁ (branchDensity W x N₀) (branchDensity W x N₁))

/-- The certificate's 64-entry rooted flag vector. -/
noncomputable def flagVector (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (A : Finset (Sym2 (Fin 3))) (a : Fin 64) : ℝ :=
  rootedFlagValue W x A (flagLabelEdges a) (flagBranchNeighbors a)

/-- The 128-entry vector `(f, u f)` used by the first Gram block. -/
noncomputable def extendedFlagVector (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (A : Finset (Sym2 (Fin 3))) (u : ℝ) (a : Fin 128) : ℝ :=
  if h : a.1 < 64 then
    flagVector W x A ⟨a.1, h⟩
  else
    u * flagVector W x A ⟨a.1 - 64, by omega⟩

/-- The first certificate quadratic is nonnegative for every fixed label
assignment and every outcome of the shared label-edge bits. -/
theorem conditional_gram₀_nonneg (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (A : Finset (Sym2 (Fin 3))) (u : ℝ) :
    0 ≤ factoredRatGramForm F₀ C₀ (extendedFlagVector W x A u) :=
  gram₀_nonneg _

/-- The second certificate quadratic is nonnegative for every fixed label
assignment and every outcome of the shared label-edge bits. -/
theorem conditional_gram₁_nonneg (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (A : Finset (Sym2 (Fin 3))) :
    0 ≤ factoredRatGramForm F₁ C₁ (flagVector W x A) :=
  gram₁_nonneg _

/-- Conditional Bernoulli averaging preserves nonnegativity of the first
certificate block. -/
theorem averaged_gram₀_nonneg (W : Graphon Ω μ) (x : Fin 3 → Ω) (u : ℝ) :
    0 ≤ ∑ A ∈ (univ : Finset (Sym2 (Fin 3))).powerset,
      bernoulliWeight (fun e ↦ edgeValue W x e) A *
        factoredRatGramForm F₀ C₀ (extendedFlagVector W x A u) := by
  exact bernoulli_average_nonneg
    (fun e ↦ edgeValue_nonneg W x e) (fun e ↦ edgeValue_le_one W x e)
    (fun A ↦ factoredRatGramForm F₀ C₀ (extendedFlagVector W x A u))
    (fun A ↦ conditional_gram₀_nonneg W x A u)

/-- Conditional Bernoulli averaging preserves nonnegativity of the second
certificate block. -/
theorem averaged_gram₁_nonneg (W : Graphon Ω μ) (x : Fin 3 → Ω) :
    0 ≤ ∑ A ∈ (univ : Finset (Sym2 (Fin 3))).powerset,
      bernoulliWeight (fun e ↦ edgeValue W x e) A *
        factoredRatGramForm F₁ C₁ (flagVector W x A) := by
  exact bernoulli_average_nonneg
    (fun e ↦ edgeValue_nonneg W x e) (fun e ↦ edgeValue_le_one W x e)
    (fun A ↦ factoredRatGramForm F₁ C₁ (flagVector W x A))
    (fun A ↦ conditional_gram₁_nonneg W x A)

/-- The first conditionally averaged Gram integrand. -/
noncomputable def averagedGram₀ (W : Graphon Ω μ) (u : ℝ) (x : Fin 3 → Ω) : ℝ :=
  ∑ A ∈ (univ : Finset (Sym2 (Fin 3))).powerset,
    bernoulliWeight (fun e ↦ edgeValue W x e) A *
      factoredRatGramForm F₀ C₀ (extendedFlagVector W x A u)

/-- The second conditionally averaged Gram integrand. -/
noncomputable def averagedGram₁ (W : Graphon Ω μ) (x : Fin 3 → Ω) : ℝ :=
  ∑ A ∈ (univ : Finset (Sym2 (Fin 3))).powerset,
    bernoulliWeight (fun e ↦ edgeValue W x e) A *
      factoredRatGramForm F₁ C₁ (flagVector W x A)

theorem averagedGram₀_nonneg (W : Graphon Ω μ) (u : ℝ) (x : Fin 3 → Ω) :
    0 ≤ averagedGram₀ W u x := by
  simpa [averagedGram₀] using averaged_gram₀_nonneg W x u

theorem averagedGram₁_nonneg (W : Graphon Ω μ) (x : Fin 3 → Ω) :
    0 ≤ averagedGram₁ W x := by
  simpa [averagedGram₁] using averaged_gram₁_nonneg W x

/-- The complete right-hand side of the Atlas 43 SOS identity, before the
coefficient identity identifies it with `t(H,W) - Φₕ(p)`. -/
noncomputable def certificateSOS (W : Graphon Ω μ) (u : ℝ) : ℝ :=
  (∫ x, averagedGram₀ W u x ∂(assignmentMeasure (Fin 3) μ)) +
    u * (1 - u) *
      ∫ x, averagedGram₁ W x ∂(assignmentMeasure (Fin 3) μ)

/-- **The exact certificate's complete SOS side is nonnegative on
`0 ≤ u ≤ 1`.** -/
theorem certificateSOS_nonneg (W : Graphon Ω μ) (u : ℝ)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) : 0 ≤ certificateSOS W u := by
  unfold certificateSOS
  apply add_nonneg
  · exact integral_nonneg (averagedGram₀_nonneg W u)
  · exact mul_nonneg (mul_nonneg hu₀ (sub_nonneg.mpr hu₁))
      (integral_nonneg (averagedGram₁_nonneg W))

end Taeyoung.Methods.RootedSOS.Atlas43Flags
