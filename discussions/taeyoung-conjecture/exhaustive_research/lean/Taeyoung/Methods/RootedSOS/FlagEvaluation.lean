import Taeyoung.Methods.RootedSOS.Bernoulli
import Taeyoung.Methods.RootedSOS.FlagGraph

/-!
# Generic shared-Bernoulli evaluation of one-branch rooted flags

This is the certificate-independent semantic layer used by four-root S4
certificates.  A flag consists of a simple graph on the labelled vertices and
a set of labels joined to one integrated branch vertex.  Labelled edges are
sampled once as shared Bernoulli bits, so multiplying two flags takes the
union of their labelled graphs rather than squaring common graphon factors.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

open Taeyoung

variable {k : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Evaluation of one rooted flag at fixed labels and one outcome of the
shared labelled-edge Bernoulli variables. -/
noncomputable def rootedFlagValue (W : Graphon Ω μ) (x : Fin k → Ω)
    (A : Finset (Sym2 (Fin k))) (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N : Finset (Fin k)) : ℝ :=
  if L.edgeFinset ⊆ A then rootedBranchDensity W x N else 0

/-- Conditional kernel obtained by gluing two rooted flags. -/
noncomputable def gluedRootedFlagKernel (W : Graphon Ω μ) (x : Fin k → Ω)
    (L₀ L₁ : SimpleGraph (Fin k)) [DecidableRel L₀.Adj]
    [DecidableRel L₁.Adj] (N₀ N₁ : Finset (Fin k)) : ℝ :=
  graphWeight (L₀ ⊔ L₁) W x *
    rootedBranchDensity W x N₀ * rootedBranchDensity W x N₁

instance sup_decidableAdj (L₀ L₁ : SimpleGraph (Fin k))
    [DecidableRel L₀.Adj] [DecidableRel L₁.Adj] :
    DecidableRel (L₀ ⊔ L₁).Adj := fun i j =>
  inferInstanceAs (Decidable (L₀.Adj i j ∨ L₁.Adj i j))

lemma edgeFinset_sup (L₀ L₁ : SimpleGraph (Fin k))
    [DecidableRel L₀.Adj] [DecidableRel L₁.Adj] :
    (L₀ ⊔ L₁).edgeFinset = L₀.edgeFinset ∪ L₁.edgeFinset := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union,
    SimpleGraph.edgeSet_sup, Set.mem_union]

/-- Shared Bernoulli averaging turns a product of two rooted flags into the
conditional kernel of their simple-graph gluing. -/
theorem bernoulli_rootedFlag_product
    (W : Graphon Ω μ) (x : Fin k → Ω)
    (L₀ L₁ : SimpleGraph (Fin k)) [DecidableRel L₀.Adj]
    [DecidableRel L₁.Adj] (N₀ N₁ : Finset (Fin k)) :
    (∑ A ∈ (univ : Finset (Sym2 (Fin k))).powerset,
      bernoulliWeight (fun e => edgeValue W x e) A *
        rootedFlagValue W x A L₀ N₀ * rootedFlagValue W x A L₁ N₁) =
      gluedRootedFlagKernel W x L₀ L₁ N₀ N₁ := by
  have h := bernoulli_indicator_product
    (fun e : Sym2 (Fin k) => edgeValue W x e)
    L₀.edgeFinset L₁.edgeFinset
    (rootedBranchDensity W x N₀) (rootedBranchDensity W x N₁)
  rw [← edgeFinset_sup L₀ L₁] at h
  have he :
      @SimpleGraph.edgeFinset (Fin k) (L₀ ⊔ L₁) (L₀.fintypeEdgeSetSup L₁) =
        @SimpleGraph.edgeFinset (Fin k) (L₀ ⊔ L₁) (L₀ ⊔ L₁).fintypeEdgeSet := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  rw [he] at h
  simpa only [rootedFlagValue, gluedRootedFlagKernel, graphWeight] using h

/-- The ordinary graph represented by a product of two one-branch flags. -/
def gluedRootedFlagGraph (L₀ L₁ : SimpleGraph (Fin k))
    [DecidableRel L₀.Adj] [DecidableRel L₁.Adj]
    (N₀ N₁ : Finset (Fin k)) : SimpleGraph (Fin (k + 2)) :=
  gluedFlagGraph (L₀ ⊔ L₁) N₀ N₁

instance gluedRootedFlagGraph_decidableAdj
    (L₀ L₁ : SimpleGraph (Fin k)) [DecidableRel L₀.Adj]
    [DecidableRel L₁.Adj] (N₀ N₁ : Finset (Fin k)) :
    DecidableRel (gluedRootedFlagGraph L₀ L₁ N₀ N₁).Adj := by
  unfold gluedRootedFlagGraph
  infer_instance

lemma gluedRootedFlagKernel_eq_rootedGluedKernel
    (W : Graphon Ω μ) (x : Fin k → Ω)
    (L₀ L₁ : SimpleGraph (Fin k)) [DecidableRel L₀.Adj]
    [DecidableRel L₁.Adj] (N₀ N₁ : Finset (Fin k)) :
    gluedRootedFlagKernel W x L₀ L₁ N₀ N₁ =
      rootedGluedKernel (L₀ ⊔ L₁) N₀ N₁ W x := by
  simp only [gluedRootedFlagKernel, rootedGluedKernel]
  exact mul_assoc _ _ _

/-- The conditional glued kernel is integrable in the labelled variables. -/
theorem integrable_rootedGluedKernel
    (L : SimpleGraph (Fin k)) [DecidableRel L.Adj]
    (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ) :
    Integrable (rootedGluedKernel L N₀ N₁ W)
      (assignmentMeasure (Fin k) μ) := by
  have h := (integrable_splitGluedFlagKernel L N₀ N₁ W).integral_prod_left
  rw [show rootedGluedKernel L N₀ N₁ W =
      (fun x => ∫ y, splitGluedFlagKernel L N₀ N₁ W (x, y)
        ∂assignmentMeasure (Fin 2) μ) by
    funext x
    simp only [rootedGluedKernel, splitGluedFlagKernel]
    rw [MeasureTheory.integral_const_mul,
      integral_two_rootedBranchMonomial W x N₀ N₁]]
  exact h

theorem integrable_gluedRootedFlagKernel
    (W : Graphon Ω μ)
    (L₀ L₁ : SimpleGraph (Fin k)) [DecidableRel L₀.Adj]
    [DecidableRel L₁.Adj] (N₀ N₁ : Finset (Fin k)) :
    Integrable (fun x => gluedRootedFlagKernel W x L₀ L₁ N₀ N₁)
      (assignmentMeasure (Fin k) μ) := by
  rw [show (fun x => gluedRootedFlagKernel W x L₀ L₁ N₀ N₁) =
      rootedGluedKernel (L₀ ⊔ L₁) N₀ N₁ W by
    funext x
    exact gluedRootedFlagKernel_eq_rootedGluedKernel W x L₀ L₁ N₀ N₁]
  exact integrable_rootedGluedKernel (L₀ ⊔ L₁) N₀ N₁ W

/-- After integrating the labels, a shared-Bernoulli flag product is exactly
the homomorphism density of its explicitly glued ordinary graph. -/
theorem integral_gluedRootedFlagKernel_eq_homDensity
    (W : Graphon Ω μ)
    (L₀ L₁ : SimpleGraph (Fin k)) [DecidableRel L₀.Adj]
    [DecidableRel L₁.Adj] (N₀ N₁ : Finset (Fin k)) :
    (∫ x, gluedRootedFlagKernel W x L₀ L₁ N₀ N₁
      ∂assignmentMeasure (Fin k) μ) =
      homDensity (gluedRootedFlagGraph L₀ L₁ N₀ N₁) W := by
  rw [MeasureTheory.integral_congr_ae
    (MeasureTheory.ae_of_all _ fun x =>
      gluedRootedFlagKernel_eq_rootedGluedKernel W x L₀ L₁ N₀ N₁)]
  exact integral_rootedGluedKernel_eq_homDensity (L₀ ⊔ L₁) N₀ N₁ W

end Taeyoung.Methods.RootedSOS
