import ApicesCommonness.Cycles.Finite.ThreeApexScalars

/-!
# Three apices on a finite host

Blueprint `thm:weighted-reference` and `thm:finite-three`.

For `m ≥ 0` a density `ω` of the colour and the apex triple with `0 ≤ ω ≤ 2`, `E ω = 1` and
`E ω (Q♯₃)⁴ ≥ max(r_{+,4}, r_{−,4})` is given by the blueprint's three cases
(`weighted_fourth_reference_of_nonneg`):

```
  m + p₃ ≤ 0:            ω = 1                                (𝒥₀ ≥ R₄^{3/2} ≥ R₄ + 4br ≥ r_{−,4})
  m + p₃ > 0, μ ≥ 0:     ω = (3 + 2μ + σ − 𝒫) / (3 + μ)       (d(E ω𝓕 − r_{+,4}) = G + 4m + μ𝒟)
  m + p₃ > 0, μ < 0:     ω = (6 − 2μ + σ + 𝒫) / (6 − μ)       (d(E ω𝓕 − r_{+,4}) = H + 24τ − 8m − μ𝒟)
```

using `(Q♯₃)⁴ ≥ 𝓕` pointwise.  Length lifting then gives `A_{n/2,3} ≥ E(Q♯₃)ⁿ ≥ ½ ∑_σ r_{σ,4}^{n/4} ≥
R_n` (`three_apex_relative_of_nonneg`); the case `m < 0` follows for the complementary kernel `−U`,
which has the same `A_{n/2,3}` and `R_n` (`three_apex_relative`).
-/

open Finset Matrix SimpleGraph

namespace ApicesCommonness

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

/-! ### Expectations of affine densities -/

lemma E_const_one : K.E (fun _ : Sample d 3 => (1 : ℝ)) = 1 := by
  simp [E, K.sum_prob]

lemma E_colour : K.E (fun ω : Sample d 3 => colour ω.1) = 0 := by
  rw [E_eq_colours]
  simp [colour_true, colour_false]

/-- `E (α + βσ + γ𝒫) = α + γμ`. -/
lemma E_affine (α β γ : ℝ) :
    K.E (fun ω : Sample d 3 => α + β * colour ω.1 + γ * K.majority ω.2) = α + γ * K.μ := by
  have h : K.E (fun ω : Sample d 3 => α + β * colour ω.1 + γ * K.majority ω.2)
      = α * K.E (fun _ : Sample d 3 => (1 : ℝ)) + β * K.E (fun ω : Sample d 3 => colour ω.1)
        + γ * K.E (fun ω : Sample d 3 => K.majority ω.2) := by
    simp only [E, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by ring
  rw [h, K.E_const_one, K.E_colour, K.E_majority]
  ring

/-- `E[(α + βσ + γ𝒫) 𝓕] = α𝒥₀ + β𝒥_σ + γ𝒥_𝒫`. -/
lemma E_affine_threeF (α β γ : ℝ) :
    K.E (fun ω : Sample d 3 => (α + β * colour ω.1 + γ * K.majority ω.2) * K.threeF ω)
      = α * K.J0 + β * K.Jσ + γ * K.JP := by
  simp only [J0, Jσ, JP, E, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

/-- A nonnegative density: `E ω (Q♯)⁴ ≥ E ω 𝓕`. -/
lemma E_weight_condQs_ge {ω : Sample d 3 → ℝ} (hω : ∀ x, 0 ≤ ω x) :
    K.E (fun x => ω x * K.threeF x) ≤ K.E (fun x => ω x * K.condQs x ^ 4) :=
  K.E_mono fun x => mul_le_mul_of_nonneg_left (K.condQs_four_ge x) (hω x)

private lemma colour_bounds (b : Bool) : -1 ≤ colour b ∧ colour b ≤ 1 := by
  cases b <;> simp [colour]

/-! ### `thm:weighted-reference` -/

/-- **`thm:weighted-reference`**, for `m ≥ 0`. -/
theorem weighted_fourth_reference_of_nonneg (hm : 0 ≤ K.m) :
    ∃ ω : Sample d 3 → ℝ, (∀ x, 0 ≤ ω x ∧ ω x ≤ 2) ∧ K.E ω = 1 ∧
      max (K.rσ4 1) (K.rσ4 (-1)) ≤ K.E (fun x => ω x * K.condQs x ^ 4) := by
  obtain ⟨-, hrp, hrm⟩ := K.fourth_colour_traces
  obtain ⟨hR1, -, hZ, hZJ, hJQ⟩ := K.reference_mean_bounds
  have hamp := K.fourth_cycle_amplification
  have hp3 := (K.basic_scalar_bounds hm).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hG, hH⟩ := K.weighted_certificate_inequalities
  have hD := K.auxiliary_scalar_nonnegative
  have hP := K.abs_majority_le
  by_cases h1 : K.m + K.p3 ≤ 0
  · -- case 1: the constant density
    refine ⟨fun _ => 1, fun _ => ⟨zero_le_one, one_le_two⟩, K.E_const_one, ?_⟩
    simp only [one_mul]
    have habs := (abs_le.mp hp3).1
    rw [max_le_iff]
    constructor <;> nlinarith [K.b_nonneg, K.r_nonneg]
  have h1 : 0 < K.m + K.p3 := lt_of_not_ge h1
  by_cases hμ : 0 ≤ K.μ
  · -- case 2
    set dd := 3 + K.μ with hdd
    have hd0 : 0 < dd := by linarith
    refine ⟨fun x => (3 + 2 * K.μ) / dd + 1 / dd * colour x.1 + (-1 / dd) * K.majority x.2,
      fun x => ?_, ?_, ?_⟩
    · dsimp only
      have hc := colour_bounds x.1
      have hp := abs_le.mp (hP x.2)
      have hnum : (3 + 2 * K.μ) / dd + 1 / dd * colour x.1 + (-1 / dd) * K.majority x.2
          = (3 + 2 * K.μ + colour x.1 - K.majority x.2) / dd := by field_simp; ring
      rw [hnum, div_nonneg_iff, div_le_iff₀ hd0]
      exact ⟨Or.inl ⟨by linarith, hd0.le⟩, by linarith⟩
    · rw [E_affine]
      field_simp
      ring
    · refine le_trans ?_ (K.E_weight_condQs_ge fun x => ?_)
      · rw [K.E_affine_threeF, max_le_iff]
        have hid : (3 + 2 * K.μ) * K.J0 + K.Jσ - K.JP - (3 + K.μ) * (K.R 4 + 4 * (K.m + K.p3))
            = K.certG + 4 * K.m + K.μ * K.auxD := by
          simp only [certG, auxD, μ, a]
          ring
        have hmain : K.rσ4 1 ≤ (3 + 2 * K.μ) / dd * K.J0 + 1 / dd * K.Jσ + -1 / dd * K.JP := by
          rw [hrp, show (3 + 2 * K.μ) / dd * K.J0 + 1 / dd * K.Jσ + -1 / dd * K.JP
            = ((3 + 2 * K.μ) * K.J0 + K.Jσ - K.JP) / dd by field_simp; ring, le_div_iff₀ hd0]
          nlinarith [mul_nonneg hμ hD]
        exact ⟨hmain, by rw [hrm]; rw [hrp] at hmain; linarith⟩
      · have hc := colour_bounds x.1
        have hp := abs_le.mp (hP x.2)
        have hnum : (3 + 2 * K.μ) / dd + 1 / dd * colour x.1 + (-1 / dd) * K.majority x.2
            = (3 + 2 * K.μ + colour x.1 - K.majority x.2) / dd := by field_simp; ring
        rw [hnum]
        exact div_nonneg (by linarith) hd0.le
  · -- case 3
    have hμ : K.μ < 0 := lt_of_not_ge hμ
    set dd := 6 - K.μ with hdd
    have hd0 : 0 < dd := by linarith
    have hτ : 3 * K.m < K.τ := by rw [μ] at hμ; linarith
    refine ⟨fun x => (6 - 2 * K.μ) / dd + 1 / dd * colour x.1 + (1 / dd) * K.majority x.2,
      fun x => ?_, ?_, ?_⟩
    · dsimp only
      have hc := colour_bounds x.1
      have hp := abs_le.mp (hP x.2)
      have hnum : (6 - 2 * K.μ) / dd + 1 / dd * colour x.1 + (1 / dd) * K.majority x.2
          = (6 - 2 * K.μ + colour x.1 + K.majority x.2) / dd := by field_simp
      rw [hnum, div_nonneg_iff, div_le_iff₀ hd0]
      exact ⟨Or.inl ⟨by linarith, hd0.le⟩, by linarith⟩
    · rw [E_affine]
      field_simp
      ring
    · refine le_trans ?_ (K.E_weight_condQs_ge fun x => ?_)
      · rw [K.E_affine_threeF, max_le_iff]
        have hid : (6 - 2 * K.μ) * K.J0 + K.Jσ + K.JP - (6 - K.μ) * (K.R 4 + 4 * (K.m + K.p3))
            = K.certH + 24 * K.τ - 8 * K.m - K.μ * K.auxD := by
          simp only [certH, auxD, μ, a]
          ring
        have hmain : K.rσ4 1 ≤ (6 - 2 * K.μ) / dd * K.J0 + 1 / dd * K.Jσ + 1 / dd * K.JP := by
          rw [hrp, show (6 - 2 * K.μ) / dd * K.J0 + 1 / dd * K.Jσ + 1 / dd * K.JP
            = ((6 - 2 * K.μ) * K.J0 + K.Jσ + K.JP) / dd by field_simp, le_div_iff₀ hd0]
          nlinarith [mul_nonneg (neg_nonneg.2 hμ.le) hD]
        exact ⟨hmain, by rw [hrm]; rw [hrp] at hmain; linarith⟩
      · have hc := colour_bounds x.1
        have hp := abs_le.mp (hP x.2)
        have hnum : (6 - 2 * K.μ) / dd + 1 / dd * colour x.1 + (1 / dd) * K.majority x.2
            = (6 - 2 * K.μ + colour x.1 + K.majority x.2) / dd := by field_simp
        rw [hnum]
        exact div_nonneg (by linarith) hd0.le

/-! ### The complementary kernel -/

lemma colour_not (b : Bool) : colour (!b) = -colour b := by
  cases b <;> simp [colour]

lemma neg_m : K.neg.m = -K.m := by
  simp only [m, f, neg, mul_neg, sum_neg_distrib]

lemma neg_A (n s : ℕ) : K.neg.A n s = K.A n s := by
  rw [A, A, neg_S, neg_S, neg_neg, add_comm]
  rfl

lemma neg_R (n : ℕ) : K.neg.R n = K.R n := by
  rw [R, R, neg_S, neg_S, neg_neg, add_comm]
  rfl

lemma neg_rσ4 (σ : ℝ) : K.neg.rσ4 σ = K.rσ4 (-σ) := by
  rw [rσ4, rσ4, neg_S]
  rfl

/-- Swapping the colour: a sample of `K` is a sample of `−U` with the other colour. -/
lemma condQs_neg {s : ℕ} (ω : Sample d s) : K.neg.condQs (!ω.1, ω.2) = K.condQs ω := by
  simp only [condQs, condPi, condD, condA, condH, neg_S, colour_not, neg_neg]
  rfl

lemma condQs_neg' {s : ℕ} (y : Sample d s) : K.condQs (!y.1, y.2) = K.neg.condQs y := by
  rw [← K.condQs_neg (!y.1, y.2), Bool.not_not]

lemma E_neg {s : ℕ} (F : Sample d s → ℝ) : K.neg.E (fun ω => F (!ω.1, ω.2)) = K.E F := by
  rw [E, E]
  refine Fintype.sum_equiv (Equiv.prodCongr (Function.Involutive.toPerm _ Bool.not_not)
    (Equiv.refl _)) _ _ fun ω => ?_
  simp only [Equiv.prodCongr_apply, Prod.map, Function.Involutive.coe_toPerm, Equiv.coe_refl, id]
  rfl

/-- **`thm:weighted-reference`.**  On every finite host there is a density `ω` of the colour and
the three apices with `0 ≤ ω ≤ 2`, `E ω = 1` and `E ω (Q♯₃)⁴ ≥ max(r_{+,4}, r_{−,4})`. -/
theorem weighted_fourth_reference :
    ∃ ω : Sample d 3 → ℝ, (∀ x, 0 ≤ ω x ∧ ω x ≤ 2) ∧ K.E ω = 1 ∧
      max (K.rσ4 1) (K.rσ4 (-1)) ≤ K.E (fun x => ω x * K.condQs x ^ 4) := by
  rcases le_or_gt 0 K.m with hm | hm
  · exact K.weighted_fourth_reference_of_nonneg hm
  · obtain ⟨ω, hω, hω1, hwt⟩ := K.neg.weighted_fourth_reference_of_nonneg (by rw [neg_m]; linarith)
    refine ⟨fun x => ω (!x.1, x.2), fun x => hω _, ?_, ?_⟩
    · rw [← K.E_neg]
      simpa only [Bool.not_not] using hω1
    · rw [neg_rσ4, neg_rσ4, neg_neg, max_comm] at hwt
      refine hwt.trans (le_of_eq ?_)
      rw [← K.E_neg]
      congr 1
      funext y
      simp only [Bool.not_not, Prod.mk.eta, K.condQs_neg']

/-! ### `thm:finite-three` -/

lemma rσ4_nonneg (σ : ℝ) : 0 ≤ K.rσ4 σ := by
  rw [rσ4_eq_trace]
  exact trace_pow_nonneg (K.TS_isHermitian σ) (by decide)

/-- `t(C_n, S_σ) ≤ r_{σ,4}^{n/4}` (`lem:finite-spectral`). -/
lemma colour_cycle_le (σ : ℝ) {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    hostDensity K.w (cycleGraph n) (K.S σ) ≤ K.rσ4 σ ^ ((n : ℝ) / 4) := by
  rw [hostDensity_cycle_eq_trace K.w_nonneg (K.S_symm σ) (by omega), rσ4_eq_trace]
  exact trace_pow_le_trace_four_rpow (K.TS_isHermitian σ) hn h4

/-- **`thm:finite-three`.**  `A_{n/2,3} ≥ R_n` on every finite host, for every even `n ≥ 4`. -/
theorem three_apex_relative {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) : K.R n ≤ K.A n 3 := by
  obtain ⟨ω, hω, hω1, hwt⟩ := K.weighted_fourth_reference
  obtain ⟨hR1, hR32, hZ, hZJ, hJQ⟩ := K.reference_mean_bounds
  have h4r : ∀ x : Sample d 3, K.condQs x ^ (4 : ℝ) = K.condQs x ^ 4 := fun x => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hmean : (K.rσ4 1 + K.rσ4 (-1)) / 2 ≤ ∑ x : Sample d 3, K.prob x * K.condQs x ^ (4 : ℝ) := by
    simp only [h4r]
    change K.R 4 ≤ K.E (fun x : Sample d 3 => K.condQs x ^ 4)
    linarith
  have hweight : max (K.rσ4 1) (K.rσ4 (-1)) ≤ ∑ x : Sample d 3, K.prob x * ω x * K.condQs x ^ (4 : ℝ) := by
    simp only [h4r, mul_assoc]
    exact hwt
  have hlift := length_lifting_two_fourth_moments (univ : Finset (Sample d 3)) K.prob K.condQs ω
    (fun x _ => K.prob_nonneg x) (K.sum_prob (s := 3)) (fun x _ => K.condQs_nonneg x) (fun x _ => (hω x).1)
    (fun x _ => (hω x).2) hω1 (K.rσ4_nonneg 1) (K.rσ4_nonneg (-1)) hmean hweight
    (q := (n : ℝ)) (by exact_mod_cast h4)
  have hn' : ∑ x : Sample d 3, K.prob x * K.condQs x ^ (n : ℝ) = K.E (fun x : Sample d 3 => K.condQs x ^ n) := by
    simp only [Real.rpow_natCast]
    rfl
  rw [hn'] at hlift
  have htrace := (K.conditional_trace_bound (s := 3) hn h4).2
  have hc1 := K.colour_cycle_le 1 hn h4
  have hc2 := K.colour_cycle_le (-1) hn h4
  rw [R]
  linarith

/-- `A_{n/2,3} ≥ 1`. -/
theorem one_le_A_three {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) : 1 ≤ K.A n 3 :=
  (K.even_cycle_lower_bound hn h4).2.2.trans (K.three_apex_relative hn h4)

end FiniteKernel

end ApicesCommonness
