import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-graph homomorphism densities

This file supplies the graphon layer needed by the pure-chordal proof.  A graphon
is an actual measurable symmetric `[0,1]`-valued kernel, not a quotient by weak
isomorphism.  Homomorphism density is an integral over the finite product
probability measure indexed by the vertices of the graph.
-/

open MeasureTheory
open scoped BigOperators

namespace PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual graphon representative on the probability space `(Ω, μ)`. -/
structure Graphon (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  toFun : Ω → Ω → ℝ
  measurable : Measurable (Function.uncurry toFun)
  nonneg : ∀ x y, 0 ≤ toFun x y
  le_one : ∀ x y, toFun x y ≤ 1
  symm : ∀ x y, toFun x y = toFun y x

instance : CoeFun (Graphon Ω μ) fun _ ↦ Ω → Ω → ℝ :=
  ⟨Graphon.toFun⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite product of copies of `μ`, indexed by the vertex type `V`. -/
noncomputable def assignmentMeasure (V : Type*) [Fintype V] [DecidableEq V]
    (μ : Measure Ω) : Measure (V → Ω) :=
  Measure.pi fun _ : V ↦ μ

instance assignmentMeasure_isProbability :
    IsProbabilityMeasure (assignmentMeasure V μ) := by
  unfold assignmentMeasure
  infer_instance

/-- Evaluation of a symmetric kernel on an unordered pair of assigned vertices. -/
def edgeValue (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun u v ↦ W (x u) (x v), fun u v ↦ W.symm (x u) (x v)⟩ e

@[simp] lemma edgeValue_mk (W : Graphon Ω μ) (x : V → Ω) (u v : V) :
    edgeValue W x s(u, v) = W (x u) (x v) := by
  simp [edgeValue, Sym2.lift_mk]

lemma measurable_edgeValue (W : Graphon Ω μ) (e : Sym2 V) :
    Measurable (fun x : V → Ω ↦ edgeValue W x e) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [show (fun x : V → Ω ↦ edgeValue W x s(u, v)) =
          fun x ↦ W (x u) (x v) by funext x; simp]
      have hp : Measurable (fun x : V → Ω ↦ (x u, x v)) :=
        (measurable_pi_apply u).prodMk (measurable_pi_apply v)
      have hc : Measurable
          (Function.uncurry W.toFun ∘ fun x : V → Ω ↦ (x u, x v)) :=
        W.measurable.comp hp
      simpa [Function.comp_def, Function.uncurry] using hc

lemma edgeValue_nonneg (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) :
    0 ≤ edgeValue W x e := by
  induction e using Sym2.inductionOn with
  | _ u v => simpa using W.nonneg (x u) (x v)

lemma edgeValue_le_one (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) :
    edgeValue W x e ≤ 1 := by
  induction e using Sym2.inductionOn with
  | _ u v => simpa using W.le_one (x u) (x v)

/-- The pointwise product of graphon values over all edges of `H`. -/
def graphWeight (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) (x : V → Ω) : ℝ :=
  ∏ e ∈ H.edgeFinset, edgeValue W x e

lemma measurable_graphWeight (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) :
    Measurable (graphWeight H W) := by
  exact H.edgeFinset.measurable_fun_prod fun e _ ↦ measurable_edgeValue W e

lemma graphWeight_nonneg (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) (x : V → Ω) :
    0 ≤ graphWeight H W x := by
  exact Finset.prod_nonneg fun e _ ↦ edgeValue_nonneg W x e

lemma graphWeight_le_one (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) (x : V → Ω) :
    graphWeight H W x ≤ 1 := by
  exact Finset.prod_le_one
    (fun e _ ↦ edgeValue_nonneg W x e)
    (fun e _ ↦ edgeValue_le_one W x e)

lemma graphWeight_lower_bound (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    δ ^ H.edgeFinset.card ≤ graphWeight H W x := by
  unfold graphWeight
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => hδ0)
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v => simpa using hδ (x u) (x v)

lemma integrable_graphWeight (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) :
    Integrable (graphWeight H W) (assignmentMeasure V μ) := by
  refine (integrable_const (μ := assignmentMeasure V μ) (1 : ℝ)).mono'
    (measurable_graphWeight H W).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (graphWeight_nonneg H W x)]
  exact graphWeight_le_one H W x

/-- The homomorphism density of a finite simple graph in an actual graphon. -/
noncomputable def homDensity (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) : ℝ :=
  ∫ x, graphWeight H W x ∂assignmentMeasure V μ

lemma homDensity_nonneg (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) :
    0 ≤ homDensity H W := by
  exact integral_nonneg fun x ↦ graphWeight_nonneg H W x

lemma homDensity_le_one (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) :
    homDensity H W ≤ 1 := by
  simpa [homDensity] using
    integral_mono (integrable_graphWeight H W)
      (integrable_const (μ := assignmentMeasure V μ) (1 : ℝ))
      (fun x ↦ graphWeight_le_one H W x)

lemma homDensity_lower_bound (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    δ ^ H.edgeFinset.card ≤ homDensity H W := by
  calc
    δ ^ H.edgeFinset.card =
        ∫ _ : V → Ω, δ ^ H.edgeFinset.card
          ∂assignmentMeasure V μ := by simp
    _ ≤ ∫ x, graphWeight H W x ∂assignmentMeasure V μ := by
      apply integral_mono
      · exact integrable_const _
      · exact integrable_graphWeight H W
      · exact fun x => graphWeight_lower_bound H W hδ0 hδ x
    _ = homDensity H W := rfl

lemma homDensity_pos_of_lower_bound
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    0 < homDensity H W :=
  lt_of_lt_of_le (pow_pos hδpos _) <|
    homDensity_lower_bound H W hδpos.le hδ

/-- Clique density, with `K_s` represented as the top graph on `Fin s`. -/
noncomputable def cliqueDensity (s : ℕ) (W : Graphon Ω μ) : ℝ :=
  homDensity (⊤ : SimpleGraph (Fin s)) W

lemma cliqueDensity_pos_of_lower_bound
    (s : ℕ) (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    0 < cliqueDensity s W :=
  homDensity_pos_of_lower_bound (⊤ : SimpleGraph (Fin s))
    W hδpos hδ

@[simp] lemma cliqueDensity_zero (W : Graphon Ω μ) :
    cliqueDensity 0 W = 1 := by
  have hedges : (⊤ : SimpleGraph (Fin 0)).edgeFinset = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin 0))
  simp [cliqueDensity, homDensity, graphWeight, assignmentMeasure, hedges]

@[simp] lemma cliqueDensity_one (W : Graphon Ω μ) :
    cliqueDensity 1 W = 1 := by
  have hedges : (⊤ : SimpleGraph (Fin 1)).edgeFinset = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin 1))
  simp [cliqueDensity, homDensity, graphWeight, assignmentMeasure, hedges]

lemma cliqueDensity_nonneg (s : ℕ) (W : Graphon Ω μ) :
    0 ≤ cliqueDensity s W :=
  homDensity_nonneg _ W

lemma cliqueDensity_le_one (s : ℕ) (W : Graphon Ω μ) :
    cliqueDensity s W ≤ 1 :=
  homDensity_le_one _ W

end PureChordal
