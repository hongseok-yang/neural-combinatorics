import OddCycleBound.RegionII.Certificate.C13Generated
import OddCycleBound.HighDensity.MixtureIntegral

/-!
# Semantic verification of the C13 Bernstein payloads

The generated files contain data and Boolean sign checks only.  The lemmas in
this file identify each Bernstein form with the existing formal C13 kernels.
-/

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.HighDensity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13LinearSafeCertificate_identity (z : Fin 2 → ℝ) :
    diagKernel 13 1
        (481 / 1000 + (9 / 1000) * z 0)
        (-(1 / 2) + (16 / 25) * z 1) =
      c13LinearSafeCertificate.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13LinearSafeCertificate, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13LinearFrontierCertificate_identity (z : Fin 2 → ℝ) :
    diagKernel 13 1
        (481 / 1000 + (9 / 1000) * z 0)
        ((481 / 1000 + (9 / 1000) * z 0) +
          (1 / 2 - (481 / 1000 + (9 / 1000) * z 0)) * z 1) =
      c13LinearFrontierCertificate.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13LinearFrontierCertificate, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

private lemma cast_ratBernstein_transform
    {source target : Fin 9 → Fin 9 → Fin 9 → ℚ}
    (h : ∀ i j index, target i j index =
      ∑ power : Fin 9, source i j power * ratBernsteinRatio 8 power index) :
    ∀ i j index,
      (target i j index : ℝ) =
        ∑ power : Fin 9, (source i j power : ℝ) * bernsteinRatio 8 power index := by
  intro i j index
  simpa [ratBernsteinRatio, bernsteinRatio] using
    congrArg (fun value : ℚ => (value : ℝ)) (h i j index)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
lemma c13QuadraticSafeSafeCube_power_identity (z : Fin 3 → ℝ) :
    multiKernel 13 2
        (481 / 1000 + (9 / 1000) * z 0)
        [-(1 / 2) + (16 / 25) * z 1,
          -(1 / 2) + (16 / 25) * z 2] =
      cubeEval
        (fun i j k => (cubeCoefficient c13QuadraticSafeSafeCube.power i j k : ℝ))
        (powerFamily (z 0)) (powerFamily (z 1)) (powerFamily (z 2)) := by
  rw [multiKernel_expand (by norm_num) (by norm_num)]
  norm_num (config := { maxSteps := 10000000 })
    [cubeEval, cubeCoefficient, cubeIndex, c13QuadraticSafeSafeCube,
      c13QuadraticSafeSafeCubePower, RationalDatum.value, powerFamily,
      kerB, hsym, Finset.sum_range_succ, Fin.sum_univ_succ, Nat.choose]
  ring

lemma c13QuadraticSafeSafeCube_nonneg
    {z : Fin 3 → ℝ} (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) :
    0 ≤ cubeEval
      (fun i j k => (cubeCoefficient c13QuadraticSafeSafeCube.power i j k : ℝ))
      (powerFamily (z 0)) (powerFamily (z 1)) (powerFamily (z 2)) := by
  have checked := c13QuadraticSafeSafeCube_checked
  have hTwo := cast_ratBernstein_transform checked.1
  have hOneAux := cast_ratBernstein_transform
    (fun i k index => checked.2.1 i index k)
  have hOne : ∀ i index k,
      (cubeCoefficient c13QuadraticSafeSafeCube.stageOne i index k : ℝ) =
        ∑ powerIndex : Fin 9,
          (cubeCoefficient c13QuadraticSafeSafeCube.stageTwo i powerIndex k : ℝ) *
            bernsteinRatio 8 powerIndex index :=
    fun i index k => hOneAux i k index
  have hZeroAux := cast_ratBernstein_transform
    (fun j k index => checked.2.2.1 index j k)
  have hZero : ∀ index j k,
      (cubeCoefficient c13QuadraticSafeSafeCube.bernstein index j k : ℝ) =
        ∑ powerIndex : Fin 9,
          (cubeCoefficient c13QuadraticSafeSafeCube.stageOne powerIndex j k : ℝ) *
            bernsteinRatio 8 powerIndex index :=
    fun index j k => hZeroAux j k index
  have hnonneg : ∀ i j k,
      0 ≤ (cubeCoefficient c13QuadraticSafeSafeCube.bernstein i j k : ℝ) := by
    intro i j k
    exact_mod_cast checked.2.2.2 i j k
  rw [bernsteinCube8_staged_sound
    (fun i j k => (cubeCoefficient c13QuadraticSafeSafeCube.power i j k : ℝ))
    (fun i j k => (cubeCoefficient c13QuadraticSafeSafeCube.stageTwo i j k : ℝ))
    (fun i j k => (cubeCoefficient c13QuadraticSafeSafeCube.stageOne i j k : ℝ))
    (fun i j k => (cubeCoefficient c13QuadraticSafeSafeCube.bernstein i j k : ℝ))
    hTwo hOne hZero z]
  exact cubeEval_bernstein_nonneg hnonneg hz

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
lemma c13QuadraticFrontierSafeCube_power_identity (z : Fin 3 → ℝ) :
    multiKernel 13 2
        (481 / 1000 + (9 / 1000) * z 0)
        [((481 / 1000 + (9 / 1000) * z 0) +
            (1 / 2 - (481 / 1000 + (9 / 1000) * z 0)) * z 1),
          -(1 / 2) + (16 / 25) * z 2] =
      cubeEval
        (fun i j k => (cubeCoefficient c13QuadraticFrontierSafeCube.power i j k : ℝ))
        (powerFamily (z 0)) (powerFamily (z 1)) (powerFamily (z 2)) := by
  rw [multiKernel_expand (by norm_num) (by norm_num)]
  norm_num (config := { maxSteps := 10000000 })
    [cubeEval, cubeCoefficient, cubeIndex, c13QuadraticFrontierSafeCube,
      c13QuadraticFrontierSafeCubePower, RationalDatum.value, powerFamily,
      kerB, hsym, Finset.sum_range_succ, Fin.sum_univ_succ, Nat.choose]
  ring

lemma c13QuadraticFrontierSafeCube_nonneg
    {z : Fin 3 → ℝ} (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) :
    0 ≤ cubeEval
      (fun i j k => (cubeCoefficient c13QuadraticFrontierSafeCube.power i j k : ℝ))
      (powerFamily (z 0)) (powerFamily (z 1)) (powerFamily (z 2)) := by
  have checked := c13QuadraticFrontierSafeCube_checked
  have hTwo := cast_ratBernstein_transform checked.1
  have hOneAux := cast_ratBernstein_transform
    (fun i k index => checked.2.1 i index k)
  have hOne : ∀ i index k,
      (cubeCoefficient c13QuadraticFrontierSafeCube.stageOne i index k : ℝ) =
        ∑ powerIndex : Fin 9,
          (cubeCoefficient c13QuadraticFrontierSafeCube.stageTwo i powerIndex k : ℝ) *
            bernsteinRatio 8 powerIndex index :=
    fun i index k => hOneAux i k index
  have hZeroAux := cast_ratBernstein_transform
    (fun j k index => checked.2.2.1 index j k)
  have hZero : ∀ index j k,
      (cubeCoefficient c13QuadraticFrontierSafeCube.bernstein index j k : ℝ) =
        ∑ powerIndex : Fin 9,
          (cubeCoefficient c13QuadraticFrontierSafeCube.stageOne powerIndex j k : ℝ) *
            bernsteinRatio 8 powerIndex index :=
    fun index j k => hZeroAux j k index
  have hnonneg : ∀ i j k,
      0 ≤ (cubeCoefficient c13QuadraticFrontierSafeCube.bernstein i j k : ℝ) := by
    intro i j k
    exact_mod_cast checked.2.2.2 i j k
  rw [bernsteinCube8_staged_sound
    (fun i j k => (cubeCoefficient c13QuadraticFrontierSafeCube.power i j k : ℝ))
    (fun i j k => (cubeCoefficient c13QuadraticFrontierSafeCube.stageTwo i j k : ℝ))
    (fun i j k => (cubeCoefficient c13QuadraticFrontierSafeCube.stageOne i j k : ℝ))
    (fun i j k => (cubeCoefficient c13QuadraticFrontierSafeCube.bernstein i j k : ℝ))
    hTwo hOne hZero z]
  exact cubeEval_bernstein_nonneg hnonneg hz

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13QuadraticFrontierFrontierCertificate_identity (z : Fin 2 → ℝ) :
    multiKernel 13 2
        (481 / 1000 + (9 / 1000) * z 0)
        [((481 / 1000 + (9 / 1000) * z 0) +
            (1 / 2 - (481 / 1000 + (9 / 1000) * z 0)) * z 1),
          ((481 / 1000 + (9 / 1000) * z 0) +
            (1 / 2 - (481 / 1000 + (9 / 1000) * z 0)) * z 1)] =
      c13QuadraticFrontierFrontierCertificate.eval z := by
  rw [multiKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13QuadraticFrontierFrontierCertificate, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, hsym,
    Finset.sum_range_succ, Fin.sum_univ_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13Diagonal3Certificate0_identity (z : Fin 2 → ℝ) :
    diagKernel 13 3 ((1 / 2) * z 0) ((1 / 2) * z 1) =
      c13Diagonal3Certificate0.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13Diagonal3Certificate0, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13Diagonal3Certificate1_identity (z : Fin 2 → ℝ) :
    diagKernel 13 3 ((1 / 2) * z 0) (-(1 / 2) + (1 / 2) * z 1) =
      c13Diagonal3Certificate1.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13Diagonal3Certificate1, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13Diagonal4Certificate0_identity (z : Fin 2 → ℝ) :
    diagKernel 13 4 ((1 / 2) * z 0) ((1 / 2) * z 1) =
      c13Diagonal4Certificate0.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13Diagonal4Certificate0, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13Diagonal4Certificate1_identity (z : Fin 2 → ℝ) :
    diagKernel 13 4 ((1 / 2) * z 0) (-(1 / 2) + (1 / 2) * z 1) =
      c13Diagonal4Certificate1.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13Diagonal4Certificate1, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13Diagonal5Certificate0_identity (z : Fin 2 → ℝ) :
    diagKernel 13 5 (1 / 4 + (1 / 4) * z 0) ((1 / 2) * z 1) =
      c13Diagonal5Certificate0.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13Diagonal5Certificate0, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13Diagonal5Certificate1_identity (z : Fin 2 → ℝ) :
    diagKernel 13 5 ((1 / 4) * z 0) ((1 / 2) * z 1) =
      c13Diagonal5Certificate1.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13Diagonal5Certificate1, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma c13Diagonal5Certificate2_identity (z : Fin 2 → ℝ) :
    diagKernel 13 5 ((1 / 2) * z 0) (-(1 / 2) + (1 / 2) * z 1) =
      c13Diagonal5Certificate2.eval z := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [c13Diagonal5Certificate2, BernsteinCertificate.eval,
    BernsteinTerm.eval, bernsteinBasis, kerB, Finset.sum_range_succ, Nat.choose]
  ring

/-! ## Range-facing consequences -/

private lemma unit_div_interval {a b : ℝ} (hb : 0 < b)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ a / b ∧ a / b ≤ 1 :=
  ⟨div_nonneg ha hb.le, (div_le_one hb).2 hab⟩

theorem c13_linear_safe_nonneg {q ell : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (hello : -(1 / 2) ≤ ell) (helhi : ell ≤ 7 / 50) :
    0 ≤ diagKernel 13 1 q ell := by
  let z : Fin 2 → ℝ := ![
    (q - 481 / 1000) / (9 / 1000),
    (ell + 1 / 2) / (16 / 25)]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> norm_num at * <;> linarith
  have hs := BernsteinCertificate.sound c13LinearSafeCertificate_checked hz
  rw [← c13LinearSafeCertificate_identity z] at hs
  change 0 ≤ diagKernel 13 1
    (481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000)))
    (-(1 / 2) + (16 / 25) * ((ell + 1 / 2) / (16 / 25))) at hs
  have hq : 481 / 1000 + (9 / 1000) *
      ((q - 481 / 1000) / (9 / 1000)) = q := by norm_num; ring
  have hell : -(1 / 2) + (16 / 25) *
      ((ell + 1 / 2) / (16 / 25)) = ell := by norm_num; ring
  simpa only [hq, hell] using hs

theorem c13_linear_frontier_nonneg {q alpha : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (halphaLo : q ≤ alpha) (halphaHi : alpha ≤ 1 / 2) :
    0 ≤ diagKernel 13 1 q alpha := by
  let den : ℝ := 1 / 2 - q
  have hden : 0 < den := by dsimp [den]; norm_num at *; linarith
  let z : Fin 2 → ℝ := ![
    (q - 481 / 1000) / (9 / 1000),
    (alpha - q) / den]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i
    · simp [z]
      constructor <;> norm_num at * <;> linarith
    · simp [z]
      exact unit_div_interval hden (sub_nonneg.mpr halphaLo) (by
        dsimp [den]
        linarith)
  have hs := BernsteinCertificate.sound c13LinearFrontierCertificate_checked hz
  rw [← c13LinearFrontierCertificate_identity z] at hs
  change 0 ≤ diagKernel 13 1
    (481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000)))
    ((481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000))) +
      (1 / 2 - (481 / 1000 + (9 / 1000) *
        ((q - 481 / 1000) / (9 / 1000)))) * ((alpha - q) / den)) at hs
  have hq : 481 / 1000 + (9 / 1000) *
      ((q - 481 / 1000) / (9 / 1000)) = q := by norm_num; ring
  have halpha : q + (1 / 2 - q) * ((alpha - q) / den) = alpha := by
    change q + den * ((alpha - q) / den) = alpha
    calc
      q + den * ((alpha - q) / den) =
          q + (alpha - q) * den / den := by ring
      _ = q + (alpha - q) := by rw [mul_div_cancel_right₀ _ (ne_of_gt hden)]
      _ = alpha := by ring
  simpa only [hq, halpha] using hs

theorem c13_quadratic_safe_safe_nonneg {q x y : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (hxlo : -(1 / 2) ≤ x) (hxhi : x ≤ 7 / 50)
    (hylo : -(1 / 2) ≤ y) (hyhi : y ≤ 7 / 50) :
    0 ≤ multiKernel 13 2 q [x, y] := by
  let z : Fin 3 → ℝ := ![
    (q - 481 / 1000) / (9 / 1000),
    (x + 1 / 2) / (16 / 25),
    (y + 1 / 2) / (16 / 25)]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> norm_num at * <;> linarith
  have hs := c13QuadraticSafeSafeCube_nonneg hz
  rw [← c13QuadraticSafeSafeCube_power_identity z] at hs
  change 0 ≤ multiKernel 13 2
    (481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000)))
    [-(1 / 2) + (16 / 25) * ((x + 1 / 2) / (16 / 25)),
      -(1 / 2) + (16 / 25) * ((y + 1 / 2) / (16 / 25))] at hs
  have hq : 481 / 1000 + (9 / 1000) *
      ((q - 481 / 1000) / (9 / 1000)) = q := by norm_num; ring
  have hx : -(1 / 2) + (16 / 25) *
      ((x + 1 / 2) / (16 / 25)) = x := by norm_num; ring
  have hy : -(1 / 2) + (16 / 25) *
      ((y + 1 / 2) / (16 / 25)) = y := by norm_num; ring
  simpa only [hq, hx, hy] using hs

theorem c13_quadratic_frontier_safe_nonneg {q alpha y : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (halphaLo : q ≤ alpha) (halphaHi : alpha ≤ 1 / 2)
    (hylo : -(1 / 2) ≤ y) (hyhi : y ≤ 7 / 50) :
    0 ≤ multiKernel 13 2 q [alpha, y] := by
  let den : ℝ := 1 / 2 - q
  have hden : 0 < den := by dsimp [den]; norm_num at *; linarith
  let z : Fin 3 → ℝ := ![
    (q - 481 / 1000) / (9 / 1000),
    (alpha - q) / den,
    (y + 1 / 2) / (16 / 25)]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i
    · simp [z]
      constructor <;> norm_num at * <;> linarith
    · simp [z]
      exact unit_div_interval hden (sub_nonneg.mpr halphaLo) (by
        dsimp [den]
        linarith)
    · simp [z]
      constructor <;> norm_num at * <;> linarith
  have hs := c13QuadraticFrontierSafeCube_nonneg hz
  rw [← c13QuadraticFrontierSafeCube_power_identity z] at hs
  change 0 ≤ multiKernel 13 2
    (481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000)))
    [((481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000))) +
        (1 / 2 - (481 / 1000 + (9 / 1000) *
          ((q - 481 / 1000) / (9 / 1000)))) * ((alpha - q) / den)),
      -(1 / 2) + (16 / 25) * ((y + 1 / 2) / (16 / 25))] at hs
  have hq : 481 / 1000 + (9 / 1000) *
      ((q - 481 / 1000) / (9 / 1000)) = q := by norm_num; ring
  have halpha : q + (1 / 2 - q) * ((alpha - q) / den) = alpha := by
    change q + den * ((alpha - q) / den) = alpha
    calc
      q + den * ((alpha - q) / den) =
          q + (alpha - q) * den / den := by ring
      _ = q + (alpha - q) := by rw [mul_div_cancel_right₀ _ (ne_of_gt hden)]
      _ = alpha := by ring
  have hy : -(1 / 2) + (16 / 25) *
      ((y + 1 / 2) / (16 / 25)) = y := by norm_num; ring
  simpa only [hq, halpha, hy] using hs

theorem c13_quadratic_frontier_frontier_nonneg {q alpha : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (halphaLo : q ≤ alpha) (halphaHi : alpha ≤ 1 / 2) :
    0 ≤ multiKernel 13 2 q [alpha, alpha] := by
  let den : ℝ := 1 / 2 - q
  have hden : 0 < den := by dsimp [den]; norm_num at *; linarith
  let z : Fin 2 → ℝ := ![
    (q - 481 / 1000) / (9 / 1000),
    (alpha - q) / den]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i
    · simp [z]
      constructor <;> norm_num at * <;> linarith
    · simp [z]
      exact unit_div_interval hden (sub_nonneg.mpr halphaLo) (by
        dsimp [den]
        linarith)
  have hs := BernsteinCertificate.sound
    c13QuadraticFrontierFrontierCertificate_checked hz
  rw [← c13QuadraticFrontierFrontierCertificate_identity z] at hs
  change 0 ≤ multiKernel 13 2
    (481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000)))
    [((481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000))) +
        (1 / 2 - (481 / 1000 + (9 / 1000) *
          ((q - 481 / 1000) / (9 / 1000)))) * ((alpha - q) / den)),
      ((481 / 1000 + (9 / 1000) * ((q - 481 / 1000) / (9 / 1000))) +
        (1 / 2 - (481 / 1000 + (9 / 1000) *
          ((q - 481 / 1000) / (9 / 1000)))) * ((alpha - q) / den))] at hs
  have hq : 481 / 1000 + (9 / 1000) *
      ((q - 481 / 1000) / (9 / 1000)) = q := by norm_num; ring
  have halpha : q + (1 / 2 - q) * ((alpha - q) / den) = alpha := by
    change q + den * ((alpha - q) / den) = alpha
    calc
      q + den * ((alpha - q) / den) =
          q + (alpha - q) * den / den := by ring
      _ = q + (alpha - q) := by rw [mul_div_cancel_right₀ _ (ne_of_gt hden)]
      _ = alpha := by ring
  simpa only [hq, halpha] using hs

private theorem c13_diagonal_three_nonneg_of_nonneg {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1 / 2) :
    0 ≤ diagKernel 13 3 q ell := by
  let z : Fin 2 → ℝ := ![2 * q, 2 * ell]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> linarith
  have hs := BernsteinCertificate.sound c13Diagonal3Certificate0_checked hz
  rw [← c13Diagonal3Certificate0_identity z] at hs
  change 0 ≤ diagKernel 13 3 ((1 / 2) * (2 * q)) ((1 / 2) * (2 * ell)) at hs
  have hq : ((1 : ℝ) / 2) * (2 * q) = q := by ring
  have hell : ((1 : ℝ) / 2) * (2 * ell) = ell := by ring
  simpa only [hq, hell] using hs

private theorem c13_diagonal_three_nonneg_of_nonpos {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : -(1 / 2) ≤ ell) (hell1 : ell ≤ 0) :
    0 ≤ diagKernel 13 3 q ell := by
  let z : Fin 2 → ℝ := ![2 * q, 2 * ell + 1]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> linarith
  have hs := BernsteinCertificate.sound c13Diagonal3Certificate1_checked hz
  rw [← c13Diagonal3Certificate1_identity z] at hs
  change 0 ≤ diagKernel 13 3 ((1 / 2) * (2 * q))
    (-(1 / 2) + (1 / 2) * (2 * ell + 1)) at hs
  have hq : ((1 : ℝ) / 2) * (2 * q) = q := by ring
  have hell : -((1 : ℝ) / 2) + ((1 : ℝ) / 2) * (2 * ell + 1) = ell := by ring
  simpa only [hq, hell] using hs

theorem c13_diagonal_three_nonneg {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : -(1 / 2) ≤ ell) (hell1 : ell ≤ 1 / 2) :
    0 ≤ diagKernel 13 3 q ell := by
  by_cases hell : 0 ≤ ell
  · exact c13_diagonal_three_nonneg_of_nonneg hq0 hq1 hell hell1
  · exact c13_diagonal_three_nonneg_of_nonpos hq0 hq1 hell0 (le_of_not_ge hell)

private theorem c13_diagonal_four_nonneg_of_nonneg {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1 / 2) :
    0 ≤ diagKernel 13 4 q ell := by
  let z : Fin 2 → ℝ := ![2 * q, 2 * ell]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> linarith
  have hs := BernsteinCertificate.sound c13Diagonal4Certificate0_checked hz
  rw [← c13Diagonal4Certificate0_identity z] at hs
  change 0 ≤ diagKernel 13 4 ((1 / 2) * (2 * q)) ((1 / 2) * (2 * ell)) at hs
  have hq : ((1 : ℝ) / 2) * (2 * q) = q := by ring
  have hell : ((1 : ℝ) / 2) * (2 * ell) = ell := by ring
  simpa only [hq, hell] using hs

private theorem c13_diagonal_four_nonneg_of_nonpos {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : -(1 / 2) ≤ ell) (hell1 : ell ≤ 0) :
    0 ≤ diagKernel 13 4 q ell := by
  let z : Fin 2 → ℝ := ![2 * q, 2 * ell + 1]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> linarith
  have hs := BernsteinCertificate.sound c13Diagonal4Certificate1_checked hz
  rw [← c13Diagonal4Certificate1_identity z] at hs
  change 0 ≤ diagKernel 13 4 ((1 / 2) * (2 * q))
    (-(1 / 2) + (1 / 2) * (2 * ell + 1)) at hs
  have hq : ((1 : ℝ) / 2) * (2 * q) = q := by ring
  have hell : -((1 : ℝ) / 2) + ((1 : ℝ) / 2) * (2 * ell + 1) = ell := by ring
  simpa only [hq, hell] using hs

theorem c13_diagonal_four_nonneg {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : -(1 / 2) ≤ ell) (hell1 : ell ≤ 1 / 2) :
    0 ≤ diagKernel 13 4 q ell := by
  by_cases hell : 0 ≤ ell
  · exact c13_diagonal_four_nonneg_of_nonneg hq0 hq1 hell hell1
  · exact c13_diagonal_four_nonneg_of_nonpos hq0 hq1 hell0 (le_of_not_ge hell)

private theorem c13_diagonal_five_nonneg_upper {q ell : ℝ}
    (hq0 : 1 / 4 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1 / 2) :
    0 ≤ diagKernel 13 5 q ell := by
  let z : Fin 2 → ℝ := ![4 * q - 1, 2 * ell]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> linarith
  have hs := BernsteinCertificate.sound c13Diagonal5Certificate0_checked hz
  rw [← c13Diagonal5Certificate0_identity z] at hs
  change 0 ≤ diagKernel 13 5
    (1 / 4 + (1 / 4) * (4 * q - 1)) ((1 / 2) * (2 * ell)) at hs
  have hq : ((1 : ℝ) / 4) + ((1 : ℝ) / 4) * (4 * q - 1) = q := by ring
  have hell : ((1 : ℝ) / 2) * (2 * ell) = ell := by ring
  simpa only [hq, hell] using hs

private theorem c13_diagonal_five_nonneg_lower {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 4)
    (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1 / 2) :
    0 ≤ diagKernel 13 5 q ell := by
  let z : Fin 2 → ℝ := ![4 * q, 2 * ell]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> linarith
  have hs := BernsteinCertificate.sound c13Diagonal5Certificate1_checked hz
  rw [← c13Diagonal5Certificate1_identity z] at hs
  change 0 ≤ diagKernel 13 5 ((1 / 4) * (4 * q)) ((1 / 2) * (2 * ell)) at hs
  have hq : ((1 : ℝ) / 4) * (4 * q) = q := by ring
  have hell : ((1 : ℝ) / 2) * (2 * ell) = ell := by ring
  simpa only [hq, hell] using hs

private theorem c13_diagonal_five_nonneg_of_nonpos {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : -(1 / 2) ≤ ell) (hell1 : ell ≤ 0) :
    0 ≤ diagKernel 13 5 q ell := by
  let z : Fin 2 → ℝ := ![2 * q, 2 * ell + 1]
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    fin_cases i <;> simp [z] <;> constructor <;> linarith
  have hs := BernsteinCertificate.sound c13Diagonal5Certificate2_checked hz
  rw [← c13Diagonal5Certificate2_identity z] at hs
  change 0 ≤ diagKernel 13 5 ((1 / 2) * (2 * q))
    (-(1 / 2) + (1 / 2) * (2 * ell + 1)) at hs
  have hq : ((1 : ℝ) / 2) * (2 * q) = q := by ring
  have hell : -((1 : ℝ) / 2) + ((1 : ℝ) / 2) * (2 * ell + 1) = ell := by ring
  simpa only [hq, hell] using hs

theorem c13_diagonal_five_nonneg {q ell : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hell0 : -(1 / 2) ≤ ell) (hell1 : ell ≤ 1 / 2) :
    0 ≤ diagKernel 13 5 q ell := by
  by_cases hell : 0 ≤ ell
  · by_cases hq : 1 / 4 ≤ q
    · exact c13_diagonal_five_nonneg_upper hq hq1 hell hell1
    · exact c13_diagonal_five_nonneg_lower hq0 (le_of_not_ge hq) hell hell1
  · exact c13_diagonal_five_nonneg_of_nonpos hq0 hq1 hell0 (le_of_not_ge hell)

lemma c13_diagonal_six (q ell : ℝ) : diagKernel 13 6 q ell = 12 := by
  rw [diagKernel_expand (by norm_num) (by norm_num)]
  norm_num [kerB, hsym, Finset.sum_range_succ, Nat.choose]
  ring

theorem c13_multiKernel_three_nonneg {q : ℝ} {L : List ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (hLlen : L.length = 3)
    (hL : ∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ multiKernel 13 3 q L := by
  exact multiKernel_nonneg (by norm_num) (by norm_num) q L hLlen
    (fun ell hell => c13_diagonal_three_nonneg hq0 hq1 (by linarith [hell.1])
      (by linarith [hell.2])) hL

theorem c13_multiKernel_four_nonneg {q : ℝ} {L : List ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (hLlen : L.length = 4)
    (hL : ∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ multiKernel 13 4 q L := by
  exact multiKernel_nonneg (by norm_num) (by norm_num) q L hLlen
    (fun ell hell => c13_diagonal_four_nonneg hq0 hq1 (by linarith [hell.1])
      (by linarith [hell.2])) hL

theorem c13_multiKernel_five_nonneg {q : ℝ} {L : List ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (hLlen : L.length = 5)
    (hL : ∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ multiKernel 13 5 q L := by
  exact multiKernel_nonneg (by norm_num) (by norm_num) q L hLlen
    (fun ell hell => c13_diagonal_five_nonneg hq0 hq1 (by linarith [hell.1])
      (by linarith [hell.2])) hL

theorem c13_multiKernel_six_nonneg {q : ℝ} {L : List ℝ}
    (hLlen : L.length = 6)
    (hL : ∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ multiKernel 13 6 q L := by
  apply multiKernel_nonneg (by norm_num) (by norm_num) q L hLlen
  · intro ell hell
    rw [c13_diagonal_six]
    norm_num
  · exact hL

end OddCycleBound.RegionII.Certificate
