import ApicesCommonness.Trees.Host.Double
import ApicesCommonness.Common.Transfer

/-!
# Transfer from weighted hosts to graphons

Every statement of the paper is a polynomial inequality between finitely many
homomorphism densities, each `L¹`-Lipschitz on graphons (`homDensity_L1_lipschitz`).  An inequality
between `L¹`-continuous functionals that holds on every step graphon holds on every graphon
(`le_of_step_graphons_cont`: step graphons are `L¹`-dense, `exists_stepGraphon_l1_close`), and a
step graphon `V = M ∘ (σ × σ)` is the weighted host `(cellWeights μ σ, M)`
(`step_homDensity_eq_host`).  The transfer itself is `Common/Transfer.lean`.

* `homDensity_cont`, `commonalityM_cont`, and `L1ContAt.mul`/`L1ContAt.pow`;
* `stepHost`: the `ProbHost (Fin d)` of a step graphon, with `homDensity_step`, `homDensity_cmpl_step`
  and `commonalityM_step` (`m(F, V) = Mh F`).
-/

open MeasureTheory

set_option linter.unusedSectionVars false

namespace ApicesCommonness

open Foundation SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Continuity of the densities -/

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

/-! ### Step graphons are hosts -/

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

end ApicesCommonness
