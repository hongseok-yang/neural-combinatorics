-- Provenance (plan T-D7): the `L1ContAt` layer (`L1ContAt`, `L1ContAt.of_lipschitz`,
-- `L1ContAt.const`, `L1ContAt.prod`, `L1ContAt.comp`, `le_of_step_graphons_cont`,
-- `le_of_hosts_cont`) is copied from
--   discussions/even_cycle_apex_commonality/lean/EvenCycleApex/Equality/Functionals.lean
--   at neural-combinatorics commit 12b365e3.
-- Changes: imports (only light even-cycle modules) and the namespace EvenCycleApex -> TreeApex.
-- Everything after "Step graphons are hosts" is new.
import TreeApex.Host.Double
import EvenCycleApex.Graph.Lipschitz
import EvenCycleApex.Host.Bridge

/-!
# Transfer from weighted hosts to graphons

Plan T-D3 and §2.7.  Every statement of the paper is a polynomial inequality between finitely many
homomorphism densities, each `L¹`-Lipschitz on graphons (`homDensity_L1_lipschitz`).  An inequality
between `L¹`-continuous functionals that holds on every step graphon holds on every graphon
(`le_of_step_graphons_cont`: step graphons are `L¹`-dense, `exists_stepGraphon_l1_close`), and a
step graphon `V = M ∘ (σ × σ)` is the weighted host `(cellWeights μ σ, M)`
(`step_homDensity_eq_host`).  This replaces the paper's W-random graphs (`lem:approximation`).

* `L1ContAt` and its closure properties, `le_of_step_graphons_cont`, `le_of_hosts_cont` (copied);
* `homDensity_cont`, `commonalityM_cont`, and `L1ContAt.mul`/`L1ContAt.pow`;
* `stepHost`: the `ProbHost (Fin d)` of a step graphon, with `homDensity_step`, `homDensity_cmpl_step`
  and `commonalityM_step` (`m(F, V) = Mh F`).
-/

open MeasureTheory

set_option linter.unusedSectionVars false

namespace TreeApex

open EvenCycleApex EvenCycleApex.Foundation SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Continuity and the transfer (copied) -/

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

/-! ### Continuity of the densities (new) -/

lemma L1ContAt.mul {F G : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ} (hF : L1ContAt μ F W)
    (hG : L1ContAt μ G W) : L1ContAt μ (fun V => F V * G V) W :=
  (hF.prod hG).comp (φ := fun p : ℝ × ℝ => p.1 * p.2) continuous_mul.continuousAt

lemma L1ContAt.pow {F : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ} (hF : L1ContAt μ F W) (a : ℕ) :
    L1ContAt μ (fun V => F V ^ a) W :=
  hF.comp (φ := fun t : ℝ => t ^ a) (continuous_pow a).continuousAt

/-- `t(F, ·)` is `L¹`-continuous at every graphon. -/
lemma homDensity_cont {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] {W : Ω → Ω → ℝ}
    (hW : IsGraphon W μ) : L1ContAt μ (fun V => homDensity F V μ) W := by
  have hb : ∀ {U : Ω → Ω → ℝ}, IsGraphon U μ → ∀ x y, |U x y| ≤ 1 := fun hU x y => by
    rw [abs_le]; exact ⟨by linarith [hU.nonneg x y], hU.le_one x y⟩
  refine L1ContAt.of_lipschitz (C := (edgePairs F).card) (by positivity) fun V hV => ?_
  have h := homDensity_L1_lipschitz (μ := μ) F hW.meas hV.meas le_rfl (hb hW) (hb hV)
  rwa [one_pow, mul_one] at h

/-- `m(F, ·)` is `L¹`-continuous at every graphon. -/
lemma commonalityM_cont {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : L1ContAt μ (fun V => commonalityM F V μ) W :=
  L1ContAt.of_lipschitz (by positivity) fun V hV => commonalityM_L1_lipschitz F hW hV

/-! ### Step graphons are hosts (new) -/

/-- The host of a step graphon `V = M ∘ (σ × σ)`: cell weights `μ(σ⁻¹{i})` and the matrix `M`. -/
noncomputable def stepHost {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Fin d → Fin d → ℝ) (hsym : ∀ i j, M i j = M j i)
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i j, M i j ≤ 1) : ProbHost (Fin d) where
  w := cellWeights μ σ
  w_nonneg := cellWeights_nonneg σ
  w_sum := cellWeights_sum hσ
  M := M
  M_symm := hsym
  M_nonneg := h0
  M_le_one := h1

variable {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ) (M : Fin d → Fin d → ℝ)
  (hsym : ∀ i j, M i j = M j i) (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i j, M i j ≤ 1)
  {V : Ω → Ω → ℝ} (hV : ∀ x y, V x y = M (σ x) (σ y))
include hV

lemma homDensity_step {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] :
    homDensity F V μ = hostDens (stepHost hσ μ M hsym h0 h1).w F (stepHost hσ μ M hsym h0 h1).M :=
  step_homDensity_eq_host F hσ M hV

lemma homDensity_cmpl_step {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] :
    homDensity F (cmpl V) μ
      = hostDens (stepHost hσ μ M hsym h0 h1).w F (stepHost hσ μ M hsym h0 h1).Mc :=
  step_homDensity_eq_host F hσ (fun i j => 1 - M i j) fun x y => by
    simp only [cmpl, hV x y]

lemma commonalityM_step {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] :
    commonalityM F V μ = (stepHost hσ μ M hsym h0 h1).Mh F := by
  rw [commonalityM, ProbHost.Mh, homDensity_step hσ M hsym h0 h1 hV,
    homDensity_cmpl_step hσ M hsym h0 h1 hV]

end TreeApex
