import EvenCycleApex.Finite.OneApex
import EvenCycleApex.Host.Bridge
import EvenCycleApex.Graph.Lipschitz

/-!
# From finite hosts to every graphon

Plan D3 and §2.7; blueprint `thm:graphon-main` (the inequality part).

A graphon `W` on any probability space is an `L¹` limit of step graphons
(`exists_stepGraphon_l1_close`); a step graphon is a finite host (`exists_host_of_isStepKernel`,
`hostOfStep`), on which every density of `W` is the host density of the matrix
(`normalizedApexDensity_step`, from `step_homDensity_eq_host`).  The normalized apex density is
`L¹`-Lipschitz (`normalizedApexDensity_lipschitz`, from `commonalityM_L1_lipschitz`), so a lower
bound that holds on all finite hosts passes to `W` (`one_le_normalizedApexDensity_of_hosts`).

**First headline:** `commonality_one_apex`, commonality of `C_n^{+1}` for every even `n ≥ 4`.
-/

open MeasureTheory Finset

namespace EvenCycleApex

open Foundation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The finite kernel of a step graphon: cell masses as weights, `U = 2M − 1`. -/
noncomputable def hostOfStep {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ) (M : Fin d → Fin d → ℝ)
    (hsym : ∀ i j, M i j = M j i) (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i j, M i j ≤ 1) :
    FiniteKernel d where
  w := cellWeights μ σ
  w_nonneg := cellWeights_nonneg σ
  w_sum := cellWeights_sum hσ
  U := fun i j => 2 * M i j - 1
  U_symm := fun i j => by rw [hsym]
  U_abs_le := fun i j => by
    rw [abs_le]; constructor <;> linarith [h0 i j, h1 i j]

/-- On a step graphon, the normalized apex density is the host's `A_{n/2,k}`. -/
theorem normalizedApexDensity_step {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ)
    (M : Fin d → Fin d → ℝ) (hsym : ∀ i j, M i j = M j i) (h0 : ∀ i j, 0 ≤ M i j)
    (h1 : ∀ i j, M i j ≤ 1) {V : Ω → Ω → ℝ} (hV : ∀ x y, V x y = M (σ x) (σ y))
    {n k : ℕ} (hn : 3 ≤ n) :
    normalizedApexDensity V μ n k = (hostOfStep (μ := μ) hσ M hsym h0 h1).A n k := by
  rw [normalizedApexDensity_eq_colour_mean V μ hn, FiniteKernel.A]
  have hstep : ∀ c : ℝ, homDensity (apexCycle n k) (colourKernel c (signedKernel V)) μ
      = hostDensity (hostOfStep (μ := μ) hσ M hsym h0 h1).w (apexCycle n k)
          ((hostOfStep (μ := μ) hσ M hsym h0 h1).S c) := fun c =>
    step_homDensity_eq_host (apexCycle n k) hσ _ fun x y => by
      simp only [colourKernel, signedKernel, hV]; rfl
  rw [hstep, hstep]

/-- The normalized apex density is `L¹`-Lipschitz on graphons. -/
theorem normalizedApexDensity_lipschitz {W V : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hV : IsGraphon V μ) {n k : ℕ} (hn : 3 ≤ n) :
    |normalizedApexDensity W μ n k - normalizedApexDensity V μ n k|
      ≤ 2 ^ (n * (k + 1)) * (n * (k + 1)) * l1norm μ (fun x y => W x y - V x y) := by
  have h := commonalityM_L1_lipschitz (μ := μ) (apexCycle n k) hW hV
  rw [apexCycle_edgeCount hn] at h
  rw [normalizedApexDensity, normalizedApexDensity, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity)]
  push_cast at h ⊢
  calc 2 ^ (n * (k + 1)) / 2 * |commonalityM (apexCycle n k) W μ - commonalityM (apexCycle n k) V μ|
      ≤ 2 ^ (n * (k + 1)) / 2 * (2 * (n * (k + 1)) * l1norm μ (fun x y => W x y - V x y)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 ^ (n * (k + 1)) * (n * (k + 1)) * l1norm μ (fun x y => W x y - V x y) := by ring

/-- **Transfer.**  If `A_{n/2,k} ≥ 1` on every finite host, then `A_{n/2,k}(W) ≥ 1` for every
graphon `W` on every probability space. -/
theorem one_le_normalizedApexDensity_of_hosts {n k : ℕ} (hn : 3 ≤ n)
    (hfin : ∀ (d : ℕ) (K : FiniteKernel d), 1 ≤ K.A n k) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    1 ≤ normalizedApexDensity W μ n k := by
  set C : ℝ := 2 ^ (n * (k + 1)) * (n * (k + 1)) with hC
  have hC0 : 0 ≤ C := by positivity
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  -- a step graphon `V` with `C ‖W − V‖₁ < δ`
  obtain ⟨V, hV, hstep, hclose⟩ :=
    exists_stepGraphon_l1_close hW (show 0 < δ / (C + 1) by positivity)
  obtain ⟨d, σ, M, hσ, hVM, hsym, h0, h1⟩ := exists_host_of_isStepKernel hV hstep
  have hVA : 1 ≤ normalizedApexDensity V μ n k := by
    rw [normalizedApexDensity_step hσ M hsym h0 h1 hVM hn]
    exact hfin d _
  have hlip := normalizedApexDensity_lipschitz hW hV (k := k) hn
  rw [← hC] at hlip
  have hsmall : C * l1norm μ (fun x y => W x y - V x y) < δ := by
    calc C * l1norm μ (fun x y => W x y - V x y) ≤ C * (δ / (C + 1)) :=
          mul_le_mul_of_nonneg_left hclose.le hC0
      _ < δ := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
  have := (abs_sub_lt_iff.mp (lt_of_le_of_lt hlip hsmall)).2
  linarith

/-- **Headline, one apex.**  For every graphon `W` on every probability space and every even
`n ≥ 4`, `M(C_n^{+1}, W) ≥ 2^{1 − 2n}`. -/
theorem commonality_one_apex {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {n : ℕ} (hn : Even n)
    (hn4 : 4 ≤ n) :
    2 / 2 ^ (n * (1 + 1)) ≤
      homDensity (apexCycle n 1) W μ + homDensity (apexCycle n 1) (cmpl W) μ := by
  have h := one_le_normalizedApexDensity_of_hosts (by omega)
    (fun d K => K.one_le_A_one hn hn4) hW
  rw [normalizedApexDensity, commonalityM] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

end EvenCycleApex
