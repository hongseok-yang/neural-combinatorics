import OddCycleBound.Necklace

/-!
# Basic graphon bound helpers

This file contains small graphon-facing lemmas shared by the headline theorem
file and conditional assemblies.  They are kept out of `Main.lean` so that
`Main.lean` remains a list of headline results rather than proof plumbing.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The complement of the complement is the original kernel. -/
theorem compl_compl (W : Ω → Ω → ℝ) : compl (compl W) = W := by
  funext x y
  simp only [compl]
  ring

/-- Edge density of the complement: `∫∫(1−W) = 1 − ∫∫W`. -/
theorem edgeDensity_compl (hW : IsGraphon W μ) :
    edgeDensity (compl W) μ = 1 - edgeDensity W μ := by
  have hGW : GoodK W := goodK_of_isGraphon hW
  have hdegint : Integrable (degree W μ) μ :=
    hGW.colsum_integrable.congr (ae_of_all _ fun x => by
      rw [degree]
      exact integral_congr_ae (ae_of_all _ fun y => hW.symm y x))
  have hone : (∫ _x : Ω, (1 : ℝ) ∂μ) = 1 := by simp
  have hdeg : ∀ x, degree (compl W) μ x = 1 - degree W μ x := fun x => by
    show (∫ y, compl W x y ∂μ) = 1 - degree W μ x
    have hwk : (fun y => compl W x y) = fun y => (1 : ℝ) - W x y := rfl
    rw [hwk, integral_sub (integrable_const 1) (hGW.integrable_row x), hone, degree]
  show (∫ x, degree (compl W) μ x ∂μ) = 1 - edgeDensity W μ
  rw [integral_congr_ae (ae_of_all _ hdeg), integral_sub (integrable_const 1) hdegint, hone]
  rfl

/-- Nonnegativity of odd/even graphon cycle traces, from pointwise
nonnegativity of graphon kernel powers. -/
theorem trace_compPow_nonneg (hW : IsGraphon W μ) (n : Nat) :
    0 <= trace μ (compPow μ W n) := by
  rw [trace]
  exact integral_nonneg fun x => compPow_nonneg hW n x x

theorem rhs9_nonpos_of_le_half (hW : IsGraphon W μ)
    (hp : edgeDensity W μ <= 1 / 2) :
    edgeDensity W μ ^ 9 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 8 <= 0 := by
  have hp0 : 0 <= edgeDensity W μ := edgeDensity_nonneg hW
  have hple : edgeDensity W μ <= 1 - edgeDensity W μ := by linarith
  have hpow : edgeDensity W μ ^ 8 <= (1 - edgeDensity W μ) ^ 8 :=
    pow_le_pow_left₀ hp0 hple 8
  have hmul := mul_le_mul_of_nonneg_left hpow hp0
  have hsplit : edgeDensity W μ ^ 9 = edgeDensity W μ * edgeDensity W μ ^ 8 := by ring
  nlinarith

theorem rhs11_nonpos_of_le_half (hW : IsGraphon W μ)
    (hp : edgeDensity W μ <= 1 / 2) :
    edgeDensity W μ ^ 11 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 10 <= 0 := by
  have hp0 : 0 <= edgeDensity W μ := edgeDensity_nonneg hW
  have hple : edgeDensity W μ <= 1 - edgeDensity W μ := by linarith
  have hpow : edgeDensity W μ ^ 10 <= (1 - edgeDensity W μ) ^ 10 :=
    pow_le_pow_left₀ hp0 hple 10
  have hmul := mul_le_mul_of_nonneg_left hpow hp0
  have hsplit : edgeDensity W μ ^ 11 = edgeDensity W μ * edgeDensity W μ ^ 10 := by ring
  nlinarith

theorem rhs13_nonpos_of_le_half (hW : IsGraphon W μ)
    (hp : edgeDensity W μ <= 1 / 2) :
    edgeDensity W μ ^ 13 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 12 <= 0 := by
  have hp0 : 0 <= edgeDensity W μ := edgeDensity_nonneg hW
  have hple : edgeDensity W μ <= 1 - edgeDensity W μ := by linarith
  have hpow : edgeDensity W μ ^ 12 <= (1 - edgeDensity W μ) ^ 12 :=
    pow_le_pow_left₀ hp0 hple 12
  have hmul := mul_le_mul_of_nonneg_left hpow hp0
  have hsplit : edgeDensity W μ ^ 13 = edgeDensity W μ * edgeDensity W μ ^ 12 := by ring
  nlinarith

end OddCycleBound
