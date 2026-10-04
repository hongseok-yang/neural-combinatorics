import ApicesCommonness.Cycles.Finite.AllApices
import ApicesCommonness.Cycles.Transfer

/-!
# The main theorems

Blueprint `thm:main` (parts H1 and H3; the equality part H2 is M10) and `thm:graphon-main`.

A closed inequality between normalized densities passes from finite hosts to every graphon on
every probability space: both sides are `L¹`-Lipschitz and agree with the host quantities on step
graphons (`le_of_step_graphons`, the pattern of `one_le_normalizedApexDensity_of_hosts`).  Hence

* **H1** `commonality_all_even_all_apices`: `M(C_n^{+k}, W) ≥ 2^{1 − n(k+1)}` for every even `n ≥ 4`
  and every `k ≥ 1`;
* **H3** `apex_relative_of_three_le`: `A_{n/2,k}(W) ≥ R_n(W)` for `k ≥ 3`, together with
  `R_n(W) ≥ 1` (`one_le_normalizedCycleDensity`).

The statements are those of plan D5.
-/

open MeasureTheory

namespace ApicesCommonness

open Foundation SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- On a step graphon, the normalized cycle density is the host's `R_n`. -/
theorem normalizedCycleDensity_step {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ)
    (M : Fin d → Fin d → ℝ) (hsym : ∀ i j, M i j = M j i) (h0 : ∀ i j, 0 ≤ M i j)
    (h1 : ∀ i j, M i j ≤ 1) {V : Ω → Ω → ℝ} (hV : ∀ x y, V x y = M (σ x) (σ y))
    {n : ℕ} (hn : 3 ≤ n) :
    normalizedCycleDensity V μ n = (hostOfStep (μ := μ) hσ M hsym h0 h1).R n := by
  rw [normalizedCycleDensity_eq_colour_mean V μ hn, FiniteKernel.R]
  have hstep : ∀ c : ℝ, homDensity (cycleGraph n) (colourKernel c (signedKernel V)) μ
      = hostDensity (hostOfStep (μ := μ) hσ M hsym h0 h1).w (cycleGraph n)
          ((hostOfStep (μ := μ) hσ M hsym h0 h1).S c) := fun c =>
    step_homDensity_eq_host (cycleGraph n) hσ _ fun x y => by
      simp only [colourKernel, signedKernel, hV]; rfl
  rw [hstep, hstep]

/-- The normalized cycle density is `L¹`-Lipschitz on graphons. -/
theorem normalizedCycleDensity_lipschitz {W V : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hV : IsGraphon V μ) {n : ℕ} (hn : 3 ≤ n) :
    |normalizedCycleDensity W μ n - normalizedCycleDensity V μ n|
      ≤ 2 ^ n * n * l1norm μ (fun x y => W x y - V x y) := by
  have h := commonalityM_L1_lipschitz (μ := μ) (cycleGraph n) hW hV
  rw [cycleGraph_card_edgePairs hn] at h
  rw [normalizedCycleDensity, normalizedCycleDensity, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity)]
  calc 2 ^ n / 2 * |commonalityM (cycleGraph n) W μ - commonalityM (cycleGraph n) V μ|
      ≤ 2 ^ n / 2 * (2 * n * l1norm μ (fun x y => W x y - V x y)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 ^ n * n * l1norm μ (fun x y => W x y - V x y) := by ring

/-- **Transfer of a closed inequality.**  If `F ≤ G` on every step graphon, and `F`, `G` are
`L¹`-Lipschitz, then `F(W) ≤ G(W)`. -/
theorem le_of_step_graphons {F G : (Ω → Ω → ℝ) → ℝ} {CF CG : ℝ} (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hF : ∀ V, IsGraphon V μ → |F W - F V| ≤ CF * l1norm μ (fun x y => W x y - V x y))
    (hG : ∀ V, IsGraphon V μ → |G W - G V| ≤ CG * l1norm μ (fun x y => W x y - V x y))
    (hstep : ∀ V, IsGraphon V μ → IsStepKernel V → F V ≤ G V) : F W ≤ G W := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set C := CF + CG with hC
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨V, hV, hVs, hclose⟩ := exists_stepGraphon_l1_close hW (show 0 < δ / (C + 1) by positivity)
  have hFV := hF V hV
  have hGV := hG V hV
  have hle := hstep V hV hVs
  have hl1 : 0 ≤ l1norm μ (fun x y => W x y - V x y) :=
    integral_nonneg fun x => integral_nonneg fun y => abs_nonneg _
  have hsmall : C * l1norm μ (fun x y => W x y - V x y) < δ := by
    calc C * l1norm μ (fun x y => W x y - V x y) ≤ C * (δ / (C + 1)) :=
          mul_le_mul_of_nonneg_left hclose.le hC0
      _ < δ := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
  have h1 : F W - F V ≤ CF * l1norm μ (fun x y => W x y - V x y) := (le_abs_self _).trans hFV
  have h2 : G V - G W ≤ CG * l1norm μ (fun x y => W x y - V x y) := by
    rw [abs_sub_comm] at hGV
    exact (le_abs_self _).trans hGV
  have hsplit : C * l1norm μ (fun x y => W x y - V x y)
      = CF * l1norm μ (fun x y => W x y - V x y) + CG * l1norm μ (fun x y => W x y - V x y) := by
    rw [hC]
    ring
  linarith

/-- **`R_n(W) ≤ A_{n/2,k}(W)`** on every graphon, from the finite hosts. -/
theorem normalizedCycleDensity_le_apex_of_hosts {n k : ℕ} (hn : 3 ≤ n)
    (hfin : ∀ (d : ℕ) (K : FiniteKernel d), K.R n ≤ K.A n k) {W : Ω → Ω → ℝ}
    (hW : IsGraphon W μ) : normalizedCycleDensity W μ n ≤ normalizedApexDensity W μ n k := by
  refine le_of_step_graphons (F := fun V => normalizedCycleDensity V μ n)
    (G := fun V => normalizedApexDensity V μ n k) (by positivity) (by positivity) hW
    (fun V hV => normalizedCycleDensity_lipschitz hW hV hn)
    (fun V hV => normalizedApexDensity_lipschitz hW hV hn) fun V hV hVs => ?_
  obtain ⟨d, σ, M, hσ, hVM, hsym, h0, h1⟩ := exists_host_of_isStepKernel hV hVs
  rw [normalizedCycleDensity_step hσ M hsym h0 h1 hVM hn,
    normalizedApexDensity_step hσ M hsym h0 h1 hVM hn]
  exact hfin d _

/-- `R_n(W) ≥ 1` on every graphon, for even `n ≥ 4`. -/
theorem one_le_normalizedCycleDensity {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) {W : Ω → Ω → ℝ}
    (hW : IsGraphon W μ) : 1 ≤ normalizedCycleDensity W μ n := by
  refine le_of_step_graphons (F := fun _ => (1 : ℝ)) (G := fun V => normalizedCycleDensity V μ n)
    (CF := 0) le_rfl (by positivity) hW (fun V _ => by simp [l1norm])
    (fun V hV => normalizedCycleDensity_lipschitz hW hV (by omega)) fun V hV hVs => ?_
  obtain ⟨d, σ, M, hσ, hVM, hsym, h0, h1⟩ := exists_host_of_isStepKernel hV hVs
  rw [normalizedCycleDensity_step hσ M hsym h0 h1 hVM (by omega)]
  exact (FiniteKernel.even_cycle_lower_bound _ hn hn4).2.2

/-- **Headline H1** (`thm:main`, commonality).  For every graphon `W` on every probability space,
every even `n ≥ 4` and every `k ≥ 1`, `M(C_n^{+k}, W) ≥ 2^{1 − n(k+1)}`. -/
theorem commonality_all_even_all_apices {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    {n k : ℕ} (hn : Even n) (hn4 : 4 ≤ n) (hk : 1 ≤ k) :
    2 / 2 ^ (n * (k + 1)) ≤
      homDensity (apexCycle n k) W μ + homDensity (apexCycle n k) (cmpl W) μ := by
  have h := one_le_normalizedApexDensity_of_hosts (by omega)
    (fun d K => K.one_le_A hn hn4 hk) hW
  rw [normalizedApexDensity, commonalityM] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Headline H3** (`thm:main`, relative bound).  For every graphon, every even `n ≥ 4` and every
`k ≥ 3`, `A_{n/2,k} ≥ R_n`, i.e. `2^{n(k+1)−1} M(C_n^{+k}, W) ≥ 2^{n−1} M(C_n, W)`; and
`R_n ≥ 1` (`one_le_normalizedCycleDensity`). -/
theorem apex_relative_of_three_le {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    {n k : ℕ} (hn : Even n) (hn4 : 4 ≤ n) (hk : 3 ≤ k) :
    2 ^ (n * (k + 1)) / 2 * (homDensity (apexCycle n k) W μ + homDensity (apexCycle n k) (cmpl W) μ)
      ≥ 2 ^ n / 2 * (homDensity (cycleGraph n) W μ + homDensity (cycleGraph n) (cmpl W) μ) :=
  normalizedCycleDensity_le_apex_of_hosts (by omega)
    (fun d K => K.apex_relative_host hn hn4 hk) hW

/-- The companion of H3: `2^{n−1} M(C_n, W) ≥ 1` for even `n ≥ 4`. -/
theorem one_le_cycle_normalized {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {n : ℕ} (hn : Even n)
    (hn4 : 4 ≤ n) :
    1 ≤ 2 ^ n / 2 * (homDensity (cycleGraph n) W μ + homDensity (cycleGraph n) (cmpl W) μ) :=
  one_le_normalizedCycleDensity hn hn4 hW

end ApicesCommonness
