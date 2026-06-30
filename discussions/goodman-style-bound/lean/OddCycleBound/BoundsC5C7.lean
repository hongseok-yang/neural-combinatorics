import OddCycleBound.Necklace

/-!
# Complement-form `C₅` and `C₇` bounds

This is the *assembly* step for the two complement-path cases: it combines the necklace
identity (`Necklace.lean`) with the positivity certificate (`Certificate.lean`) and the
edge-deletion bound (`Cycle.lean`) into the integral-grounded inequalities

* `C5_integral`     : `t(C₅, 1−U) ≥ (1−q)⁵ − (1−q)q⁴`   (all densities),
* `C7_integral`     : `t(C₇, 1−U) ≥ (1−q)⁷ − (1−q)q⁶`   (nontrivial regime `q ≤ ½`),
* `C7_integral_all` : the same `C₇` bound for all densities (`q > ½` is `g₇ ≤ 0 ≤ t`),

where `q = edgeDensity U μ = ∫∫U`.  Each necklace expands — by a pure `ring` identity in the
spectral moments — to `gₘ + Φₘ + (xₘ₋₁ − cₘ)`, after which `Φₘ ≥ 0` (the certificate) and
`xₘ₋₁ − cₘ ≥ 0` (edge deletion) finish by linear arithmetic.  The `W`-facing restatements are
in `Main.lean`; the `C₉` analogue is in `C9.lean`.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- **`C₅` for all edge densities, fully integral-grounded.**  `t(C₅, 1−U) ≥ p⁵ − p(1−p)⁴`
(`p = 1 − q`, `q = ∫∫U`), with *only the integral definition of homomorphism density trusted*. -/
theorem C5_integral (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 4) ≥ (1 - edgeDensity U μ) ^ 5 - (1 - edgeDensity U μ) * edgeDensity U μ ^ 4 := by
  -- shorthand
  have hx1 : pathDensity U μ 1 = edgeDensity U μ := pathDensity_one hU
  have hx2 : pathDensity U μ 2 = edgeDensity U μ ^ 2 + specMoment U μ 0 := pathDensity_two hU
  have hx3 : pathDensity U μ 3 = edgeDensity U μ ^ 3 + 2 * edgeDensity U μ * specMoment U μ 0 + specMoment U μ 1 := pathDensity_three hU
  have hx4 : pathDensity U μ 4 = edgeDensity U μ ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 0
      + 2 * edgeDensity U μ * specMoment U μ 1 + specMoment U μ 0 ^ 2 + specMoment U μ 2 := pathDensity_four hU
  have hed : trace μ (compPow μ U 4) ≤ pathDensity U μ 4 := edge_deletion_general hU 3
  have hcert := cert5_specMoment hU (edgeDensity U μ)
  rw [complTrace_necklace hU 3]
  simp only [pairing_pathIter_complIter_closed hU, complMean_succ hU, complMean_zero, pathDensity_zero, pairing_pathIter_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ, Nat.reduceSub, Nat.reduceAdd,
    mul_one, one_mul, mul_neg, neg_neg, zero_add, add_zero]
  rw [hx1, hx2, hx3, hx4]
  rw [hx4] at hed
  nlinarith [hcert, hed]

/-- **`C₇`, nontrivial regime `q ≤ ½`, fully integral-grounded.** -/
theorem C7_integral (hU : IsGraphon U μ) (hq : edgeDensity U μ ≤ 1 / 2) :
    trace μ (compPow μ (compl U) 6) ≥ (1 - edgeDensity U μ) ^ 7 - (1 - edgeDensity U μ) * edgeDensity U μ ^ 6 := by
  have hx1 : pathDensity U μ 1 = edgeDensity U μ := pathDensity_one hU
  have hx2 := pathDensity_two hU; have hx3 := pathDensity_three hU; have hx4 := pathDensity_four hU
  have hx5 := pathDensity_five hU; have hx6 := pathDensity_six hU
  have hed : trace μ (compPow μ U 6) ≤ pathDensity U μ 6 := edge_deletion_general hU 5
  have hcert := cert7_specMoment hU (edgeDensity U μ) (edgeDensity_nonneg hU) hq
  -- The necklace expands to `g₇ + Φ₇ + (x₆ − c₆)` as a pure polynomial identity (`ring`);
  -- `Φ₇ ≥ 0` (`hcert`) and `x₆ − c₆ ≥ 0` (`hed`) then finish by linear arithmetic.
  have key : trace μ (compPow μ (compl U) 6)
      = ((1 - edgeDensity U μ) ^ 7 - (1 - edgeDensity U μ) * edgeDensity U μ ^ 6)
        + (6 * specMoment U μ 4 + (12 * edgeDensity U μ - 7) * specMoment U μ 3
            + (18 * edgeDensity U μ ^ 2 - 21 * edgeDensity U μ + 7) * specMoment U μ 2
            + (24 * edgeDensity U μ ^ 3 - 42 * edgeDensity U μ ^ 2 + 28 * edgeDensity U μ - 7) * specMoment U μ 1
            + (30 * edgeDensity U μ ^ 4 - 70 * edgeDensity U μ ^ 3 + 70 * edgeDensity U μ ^ 2 - 35 * edgeDensity U μ + 7) * specMoment U μ 0
            + 12 * specMoment U μ 0 * specMoment U μ 2 + (36 * edgeDensity U μ - 21) * specMoment U μ 0 * specMoment U μ 1
            + (36 * edgeDensity U μ ^ 2 - 42 * edgeDensity U μ + 14) * (specMoment U μ 0) ^ 2 + 6 * (specMoment U μ 0) ^ 3
            + 6 * (specMoment U μ 1) ^ 2)
        + (pathDensity U μ 6 - trace μ (compPow μ U 6)) := by
    rw [complTrace_necklace hU 5]
    simp only [pairing_pathIter_complIter_closed hU, complMean_succ hU, complMean_zero, pathDensity_zero, pairing_pathIter_zero,
      Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ, Nat.reduceSub, Nat.reduceAdd,
      mul_one, one_mul, mul_neg, neg_neg, zero_add, add_zero]
    rw [hx1, hx2, hx3, hx4, hx5, hx6]
    ring
  rw [key]
  linarith [hcert, hed]

/-- **`C₇` for all edge densities, fully integral-grounded.**  In the regime `q > ½` the bound
is trivial: `g₇ = (1−q)((1−q)⁶ − q⁶) ≤ 0 ≤ t(C₇, 1−U)`. -/
theorem C7_integral_all (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 6) ≥ (1 - edgeDensity U μ) ^ 7 - (1 - edgeDensity U μ) * edgeDensity U μ ^ 6 := by
  rcases le_total (edgeDensity U μ) (1 / 2) with hq | hq
  · exact C7_integral hU hq
  · have hcc : 0 ≤ trace μ (compPow μ (compl U) 6) := by
      rw [trace]; exact integral_nonneg fun x => compPow_nonneg (isGraphon_compl hU) 6 x x
    have h1 : 0 ≤ 1 - edgeDensity U μ := by linarith [edgeDensity_le_one hU]
    have hpow : (1 - edgeDensity U μ) ^ 6 ≤ edgeDensity U μ ^ 6 :=
      pow_le_pow_left₀ h1 (by linarith) 6
    have hg7 : (1 - edgeDensity U μ) ^ 7 - (1 - edgeDensity U μ) * edgeDensity U μ ^ 6 ≤ 0 := by
      nlinarith [mul_nonneg h1 (sub_nonneg.mpr hpow)]
    linarith [hcc, hg7]

end OddCycleBound
