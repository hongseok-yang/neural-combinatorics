import ApicesCommonness.Common.Graph.Lipschitz
import ApicesCommonness.Common.Host.Bridge

/-!
# Transfer from step graphons to graphons

An inequality between `L¹`-continuous graphon functionals (`L1ContAt`) that holds on every step
graphon holds on every graphon (`le_of_step_graphons_cont`: step graphons are `L¹`-dense,
`exists_stepGraphon_l1_close`).  Lipschitz functionals are continuous (`L1ContAt.of_lipschitz`), and
continuity survives pairing and composition with a function that is continuous at the value
(`L1ContAt.prod`, `L1ContAt.comp`).  `le_of_hosts_cont` states the transfer for functionals whose
step values are host values.
-/

open MeasureTheory

set_option linter.unusedSectionVars false

namespace ApicesCommonness

open Foundation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `L¹`-continuity of a graphon functional at `W` (tested on graphons). -/
def L1ContAt {α : Type*} [PseudoMetricSpace α] (μ : Measure Ω) (F : (Ω → Ω → ℝ) → α)
    (W : Ω → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ V, IsGraphon V μ → l1norm μ (fun x y => W x y - V x y) < δ →
    dist (F V) (F W) < ε

lemma L1ContAt.of_lipschitz {F : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ V, IsGraphon V μ → |F W - F V| ≤ C * l1norm μ (fun x y => W x y - V x y)) :
    L1ContAt μ F W := by
  intro ε hε
  refine ⟨ε / (C + 1), by positivity, fun V hV hδ => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have hl := l1norm_nonneg (μ := μ) (fun x y => W x y - V x y)
  calc |F W - F V| ≤ C * l1norm μ (fun x y => W x y - V x y) := h V hV
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hδ.le hC
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

lemma L1ContAt.const {α : Type*} [PseudoMetricSpace α] (a : α) (W : Ω → Ω → ℝ) :
    L1ContAt μ (fun _ => a) W :=
  fun ε hε => ⟨1, one_pos, fun _ _ _ => by simpa using hε⟩

lemma L1ContAt.prod {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {F : (Ω → Ω → ℝ) → α} {G : (Ω → Ω → ℝ) → β} {W : Ω → Ω → ℝ} (hF : L1ContAt μ F W)
    (hG : L1ContAt μ G W) : L1ContAt μ (fun V => (F V, G V)) W := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hF ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hG ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun V hV hδ => ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨h₁ V hV (lt_of_lt_of_le hδ (min_le_left _ _)),
    h₂ V hV (lt_of_lt_of_le hδ (min_le_right _ _))⟩

lemma L1ContAt.comp {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {F : (Ω → Ω → ℝ) → α} {W : Ω → Ω → ℝ} (hF : L1ContAt μ F W) {φ : α → β}
    (hφ : ContinuousAt φ (F W)) : L1ContAt μ (fun V => φ (F V)) W := by
  intro ε hε
  obtain ⟨η, hη, hφ'⟩ := Metric.continuousAt_iff.mp hφ ε hε
  obtain ⟨δ, hδ, hF'⟩ := hF η hη
  exact ⟨δ, hδ, fun V hV hδV => hφ' (hF' V hV hδV)⟩

/-- **Transfer of a closed inequality between `L¹`-continuous functionals.** -/
theorem le_of_step_graphons_cont {F G : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ}
    (hW : IsGraphon W μ) (hF : L1ContAt μ F W) (hG : L1ContAt μ G W)
    (hstep : ∀ V, IsGraphon V μ → IsStepKernel V → F V ≤ G V) : F W ≤ G W := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, h₁⟩ := hF (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hG (ε / 2) (by positivity)
  obtain ⟨V, hV, hVs, hclose⟩ := exists_stepGraphon_l1_close hW (lt_min hδ₁ hδ₂)
  have a₁ := h₁ V hV (lt_of_lt_of_le hclose (min_le_left _ _))
  have a₂ := h₂ V hV (lt_of_lt_of_le hclose (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at a₁ a₂
  have := hstep V hV hVs
  linarith

/-- The transfer, specialised to host values: if `F V = f(host)` and `G V = g(host)` on step
graphons and `f ≤ g` on every finite host, then `F W ≤ G W`. -/
theorem le_of_hosts_cont {F G : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hF : L1ContAt μ F W) (hG : L1ContAt μ G W)
    (hstep : ∀ {d : ℕ} {σ : Ω → Fin d} (_hσ : Measurable σ) (M : Fin d → Fin d → ℝ)
      (_hsym : ∀ i j, M i j = M j i) (_h0 : ∀ i j, 0 ≤ M i j) (_h1 : ∀ i j, M i j ≤ 1)
      (V : Ω → Ω → ℝ), (∀ x y, V x y = M (σ x) (σ y)) → F V ≤ G V) : F W ≤ G W :=
  le_of_step_graphons_cont hW hF hG fun V hV hVs => by
    obtain ⟨d, σ, M, hσ, hVM, hsym, h0, h1⟩ := exists_host_of_isStepKernel hV hVs
    exact hstep hσ M hsym h0 h1 V hVM

end ApicesCommonness
