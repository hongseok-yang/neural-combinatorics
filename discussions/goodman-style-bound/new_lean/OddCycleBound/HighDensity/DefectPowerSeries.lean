/-
# Formal-power-series core of the universal E5b identity

This file packages the path recurrence as the inverse of its scalar denominator.  It is the
operator-free formal-series bridge needed to identify the necklace expression with the two-sided
spectral shift.
-/

import OddCycleBound.HighDensity.DefectIdentity
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown

open scoped BigOperators

namespace OddCycleBound.HighDensity

open PowerSeries

/-- The ordinary generating series of a moment sequence. -/
noncomputable def momentSeries (s : ℕ → ℝ) : ℝ⟦X⟧ := PowerSeries.mk s

/-- The ordinary generating series of the universal path recurrence. -/
noncomputable def pathSeries (q : ℝ) (s : ℕ → ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk (pathMoment q s)

/-- The scalar Schur-complement denominator of the path resolvent. -/
noncomputable def pathDenominator (q : ℝ) (s : ℕ → ℝ) : ℝ⟦X⟧ :=
  1 - C q * X - X ^ 2 * momentSeries s

@[simp] lemma coeff_momentSeries (s : ℕ → ℝ) (j : ℕ) :
    coeff j (momentSeries s) = s j := by simp [momentSeries]

@[simp] lemma coeff_pathSeries (q : ℝ) (s : ℕ → ℝ) (j : ℕ) :
    coeff j (pathSeries q s) = pathMoment q s j := by simp [pathSeries]

/-- Powers of the moment series have exactly the convolution coefficients used by `momentPhi`. -/
lemma coeff_momentSeries_pow (s : ℕ → ℝ) : ∀ r j,
    coeff j (momentSeries s ^ r) = momentConv s r j
  | 0, j => by cases j <;> simp
  | r + 1, j => by
      rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        momentConv_succ]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_momentSeries, coeff_momentSeries_pow]

/-! ## Scalar resolvents and finite geometric expansion -/

/-- The scalar series `(1-aX)⁻ʳ`, packaged using mathlib's negative-binomial unit. -/
noncomputable def scalarInvPow (a : ℝ) (r : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.rescale a (PowerSeries.invOneSubPow ℝ r : ℝ⟦X⟧)

@[simp] lemma coeff_scalarInvPow_succ (a : ℝ) (r n : ℕ) :
    coeff n (scalarInvPow a (r + 1)) =
      (Nat.choose (r + n) r : ℝ) * a ^ n := by
  rw [scalarInvPow, coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp only [coeff_mk]
  ring

@[simp] lemma scalarInvPow_zero (a : ℝ) : scalarInvPow a 0 = 1 := by
  simp [scalarInvPow, PowerSeries.invOneSubPow_zero]

lemma scalarInvPow_add (a : ℝ) (r e : ℕ) :
    scalarInvPow a (r + e) = scalarInvPow a r * scalarInvPow a e := by
  unfold scalarInvPow
  rw [PowerSeries.invOneSubPow_add]
  exact map_mul (PowerSeries.rescale a) _ _

lemma one_sub_C_mul_X_pow_mul_scalarInvPow (a : ℝ) (r : ℕ) :
    (1 - C a * X) ^ r * scalarInvPow a r = 1 := by
  have h := (PowerSeries.invOneSubPow ℝ r).inv_val
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at h
  have ha := congrArg (PowerSeries.rescale a) h
  simpa only [map_mul, map_pow, map_sub, map_one, PowerSeries.rescale_X,
    scalarInvPow] using ha

@[simp] lemma scalarInvPow_one_mul (a : ℝ) :
    (1 - C a * X) * scalarInvPow a 1 = 1 := by
  simpa using one_sub_C_mul_X_pow_mul_scalarInvPow a 1

/-- The excursion variable after removing the scalar part of the path denominator. -/
noncomputable def excursionVariable (a : ℝ) (s : ℕ → ℝ) : ℝ⟦X⟧ :=
  X ^ 2 * momentSeries s * scalarInvPow a 1

/-- The recursive path series satisfies `P = 1 + qXP + X²SP`. -/
lemma pathSeries_fixed_point (q : ℝ) (s : ℕ → ℝ) :
    pathSeries q s = 1 + C q * X * pathSeries q s +
      X ^ 2 * momentSeries s * pathSeries q s := by
  ext (_ | n)
  · simp [pathSeries]
  · cases n with
    | zero =>
        simp only [map_add, coeff_pathSeries]
        rw [coeff_one, if_neg (by omega), zero_add]
        simp only [pathMoment]
        simp only [mul_one, Finset.sum_range_zero, add_zero, zero_add]
        have hq : coeff 1 (C q * X * pathSeries q s) = q := by
          rw [mul_assoc, coeff_C_mul]
          simpa using coeff_X_pow_mul (pathSeries q s) 1 0
        have hs : coeff 1 (X ^ 2 * momentSeries s * pathSeries q s) = 0 := by
          rw [mul_assoc, coeff_X_pow_mul']
          simp
        rw [hq, hs, add_zero]
    | succ n =>
        simp only [map_add, coeff_pathSeries]
        rw [coeff_one, if_neg (by omega), zero_add]
        rw [show n + 1 + 1 = (n + 1) + 1 by omega,
          pathMoment_succ]
        have hq : coeff (n + 2) (C q * X * pathSeries q s) =
            q * pathMoment q s (n + 1) := by
          rw [mul_assoc, coeff_C_mul]
          simpa [show n + 2 = (n + 1) + 1 by omega] using
            (coeff_X_pow_mul (pathSeries q s) 1 (n + 1))
        have hs : coeff (n + 2) (X ^ 2 * momentSeries s * pathSeries q s) =
            ∑ i ∈ Finset.range (n + 1),
              s i * pathMoment q s (n - i) := by
          rw [mul_assoc]
          have hx := coeff_X_pow_mul (momentSeries s * pathSeries q s) 2 n
          rw [show n + 2 = n + 2 by rfl] at hx
          rw [hx, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          simp only [coeff_momentSeries, coeff_pathSeries]
        rw [hq, hs]
        congr 1

/-- The path denominator and path series are mutual inverses. -/
theorem pathDenominator_mul_pathSeries (q : ℝ) (s : ℕ → ℝ) :
    pathDenominator q s * pathSeries q s = 1 := by
  have h := pathSeries_fixed_point q s
  unfold pathDenominator
  linear_combination h

/-- Multiplying the path series by its scalar denominator leaves a geometric inverse in the
excursion variable. -/
lemma one_sub_excursionVariable_mul_scalar_pathSeries (a : ℝ) (s : ℕ → ℝ) :
    (1 - excursionVariable a s) *
        ((1 - C a * X) * pathSeries a s) = 1 := by
  have hD := pathDenominator_mul_pathSeries a s
  have hscalar := scalarInvPow_one_mul a
  have hfactor :
      pathDenominator a s =
        (1 - C a * X) * (1 - excursionVariable a s) := by
    unfold pathDenominator excursionVariable
    calc
      1 - C a * X - X ^ 2 * momentSeries s =
          (1 - C a * X) - X ^ 2 * momentSeries s *
            ((1 - C a * X) * scalarInvPow a 1) := by rw [hscalar]; ring
      _ = _ := by ring
  rw [hfactor] at hD
  linear_combination hD

/-- A finite geometric expansion with an exact remainder. -/
lemma scalar_pathSeries_geometric (a : ℝ) (s : ℕ → ℝ) (R : ℕ) :
    (1 - C a * X) * pathSeries a s =
      (∑ r ∈ Finset.range R, excursionVariable a s ^ r) +
        excursionVariable a s ^ R *
          ((1 - C a * X) * pathSeries a s) := by
  let H := (1 - C a * X) * pathSeries a s
  let Z := excursionVariable a s
  have hZH : (1 - Z) * H = 1 :=
    one_sub_excursionVariable_mul_scalar_pathSeries a s
  have hrec : H = 1 + Z * H := by
    linear_combination hZH
  induction R with
  | zero => simp
  | succ R ih =>
      have hstep : excursionVariable a s ^ R * H =
          excursionVariable a s ^ R + excursionVariable a s ^ (R + 1) * H := by
        calc
          excursionVariable a s ^ R * H =
              excursionVariable a s ^ R * (1 + Z * H) :=
                congrArg (fun F => excursionVariable a s ^ R * F) hrec
          _ = _ := by
            change excursionVariable a s ^ R *
                (1 + excursionVariable a s * H) = _
            rw [pow_succ']
            ring
      calc
        (1 - C a * X) * pathSeries a s =
            (∑ r ∈ Finset.range R, excursionVariable a s ^ r) +
              excursionVariable a s ^ R * H := ih
        _ = (∑ r ∈ Finset.range (R + 1), excursionVariable a s ^ r) +
              excursionVariable a s ^ (R + 1) * H := by
            rw [hstep, Finset.sum_range_succ]
            abel

/-- The full path resolvent is the scalar inverse times its finite excursion expansion. -/
lemma pathSeries_geometric (a : ℝ) (s : ℕ → ℝ) (R : ℕ) :
    pathSeries a s =
      scalarInvPow a 1 *
        (∑ r ∈ Finset.range R, excursionVariable a s ^ r) +
      scalarInvPow a 1 * excursionVariable a s ^ R *
        ((1 - C a * X) * pathSeries a s) := by
  have h := congrArg (fun F => scalarInvPow a 1 * F)
    (scalar_pathSeries_geometric a s R)
  have hscalar := scalarInvPow_one_mul a
  calc
    pathSeries a s = scalarInvPow a 1 *
        ((1 - C a * X) * pathSeries a s) := by
          calc
            pathSeries a s = 1 * pathSeries a s := by rw [one_mul]
            _ = (scalarInvPow a 1 * (1 - C a * X)) * pathSeries a s := by
              rw [mul_comm (scalarInvPow a 1), hscalar]
            _ = _ := by rw [mul_assoc]
    _ = _ := by simpa only [mul_add, Finset.mul_sum, mul_assoc] using h

lemma scalarInvPow_eq_pow (a : ℝ) : ∀ r : ℕ,
    scalarInvPow a r = scalarInvPow a 1 ^ r
  | 0 => by simp
  | r + 1 => by
      rw [scalarInvPow_add a r 1, scalarInvPow_eq_pow, pow_succ]

/-- Normal form of the `r`-excursion summand. -/
lemma scalarInvPow_mul_excursionVariable_pow (a : ℝ) (s : ℕ → ℝ) (r : ℕ) :
    scalarInvPow a 1 * excursionVariable a s ^ r =
      X ^ (2 * r) * momentSeries s ^ r * scalarInvPow a (r + 1) := by
  unfold excursionVariable
  rw [mul_pow]
  rw [mul_pow]
  rw [← pow_mul]
  have hG : scalarInvPow a 1 * scalarInvPow a 1 ^ r =
      scalarInvPow a (r + 1) := by
    calc
      scalarInvPow a 1 * scalarInvPow a 1 ^ r =
          scalarInvPow a 1 ^ (r + 1) := by rw [pow_succ']
      _ = scalarInvPow a (r + 1) := (scalarInvPow_eq_pow a (r + 1)).symm
  calc
    scalarInvPow a 1 *
        (X ^ (2 * r) * momentSeries s ^ r * scalarInvPow a 1 ^ r) =
      X ^ (2 * r) * momentSeries s ^ r *
        (scalarInvPow a 1 * scalarInvPow a 1 ^ r) := by ring
    _ = _ := by rw [hG]

/-- Coefficient of a fixed excursion summand. -/
lemma coeff_scalarInvPow_mul_excursionVariable_pow (a : ℝ) (s : ℕ → ℝ)
    {r n : ℕ} (hrn : 2 * r ≤ n) :
    coeff n (scalarInvPow a 1 * excursionVariable a s ^ r) =
      ∑ j ∈ Finset.range (n - 2 * r + 1),
        (Nat.choose (n - 2 * r - j + r) r : ℝ) *
          a ^ (n - 2 * r - j) * momentConv s r j := by
  rw [scalarInvPow_mul_excursionVariable_pow]
  rw [mul_assoc, coeff_X_pow_mul']
  rw [if_pos hrn, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_momentSeries_pow, coeff_scalarInvPow_succ]
  ring

/-- Coefficients below the leading excursion degree vanish. -/
lemma coeff_scalarInvPow_mul_excursionVariable_pow_eq_zero (a : ℝ) (s : ℕ → ℝ)
    {r n : ℕ} (hnr : n < 2 * r) :
    coeff n (scalarInvPow a 1 * excursionVariable a s ^ r) = 0 := by
  rw [scalarInvPow_mul_excursionVariable_pow]
  rw [mul_assoc, coeff_X_pow_mul']
  simp [hnr.not_ge]

/-- Finite coefficient expansion of the path resolvent. -/
lemma coeff_pathSeries_eq_sum_excursions (a : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    coeff n (pathSeries a s) =
      ∑ r ∈ Finset.range (n / 2 + 1),
        coeff n (scalarInvPow a 1 * excursionVariable a s ^ r) := by
  have hgeo := congrArg (coeff n) (pathSeries_geometric a s (n / 2 + 1))
  simp only [map_add] at hgeo
  have hrem : coeff n
      (scalarInvPow a 1 * excursionVariable a s ^ (n / 2 + 1) *
        ((1 - C a * X) * pathSeries a s)) = 0 := by
    rw [← mul_assoc, scalarInvPow_mul_excursionVariable_pow]
    rw [show
      X ^ (2 * (n / 2 + 1)) * momentSeries s ^ (n / 2 + 1) *
          scalarInvPow a (n / 2 + 1 + 1) * (1 - C a * X) * pathSeries a s =
        X ^ (2 * (n / 2 + 1)) *
          (momentSeries s ^ (n / 2 + 1) *
            scalarInvPow a (n / 2 + 1 + 1) *
            (1 - C a * X) * pathSeries a s) by ring]
    rw [coeff_X_pow_mul']
    rw [if_neg]
    omega
  rw [hrem, add_zero] at hgeo
  rw [Finset.mul_sum] at hgeo
  simpa only [map_sum] using hgeo

/-- The path coefficient is its scalar term plus exactly the `momentPathTerm` tail used by
`momentPhi`. -/
theorem pathMoment_eq_pow_add_sum_momentPathTerm (q : ℝ) (s : ℕ → ℝ)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    pathMoment q s (m - 1) = q ^ (m - 1) +
      ∑ k ∈ Finset.range ((m - 1) / 2), momentPathTerm m (k + 1) q s := by
  rw [← coeff_pathSeries]
  rw [coeff_pathSeries_eq_sum_excursions]
  have hhalf : (m - 1) / 2 + 1 = ((m - 1) / 2) + 1 := rfl
  rw [hhalf, Finset.sum_range_succ']
  have hzero : coeff (m - 1)
      (scalarInvPow q 1 * excursionVariable q s ^ 0) = q ^ (m - 1) := by
    simp
  rw [hzero]
  suffices htail :
      (∑ k ∈ Finset.range ((m - 1) / 2),
          coeff (m - 1)
            (scalarInvPow q 1 * excursionVariable q s ^ (k + 1))) =
        ∑ k ∈ Finset.range ((m - 1) / 2), momentPathTerm m (k + 1) q s by
    rw [htail]
    ring
  refine Finset.sum_congr rfl fun k hk => ?_
  have hklt : k < (m - 1) / 2 := Finset.mem_range.mp hk
  have hrle : 2 * (k + 1) ≤ m - 1 := by
    rcases hm with ⟨t, ht⟩
    omega
  rw [coeff_scalarInvPow_mul_excursionVariable_pow q s hrle]
  unfold momentPathTerm
  have hbound : m - 1 - 2 * (k + 1) + 1 = m - 2 * (k + 1) := by omega
  rw [hbound, Finset.sum_range_succ]
  simp only [if_neg (lt_irrefl (m - 2 * (k + 1))), zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < m - 2 * (k + 1) := Finset.mem_range.mp hj
  rw [if_pos hjlt]
  have hchoose :
      m - 1 - 2 * (k + 1) - j + (k + 1) =
        m - 2 * (k + 1) - 1 - j + (k + 1) := by omega
  have hpow :
      m - 1 - 2 * (k + 1) - j =
        m - 2 * (k + 1) - 1 - j := by omega
  rw [hchoose, hpow]

/-! ## Coefficient extraction: logarithmic derivatives -/

/-- Normal form for a positive power of the excursion variable. -/
lemma excursionVariable_pow (a : ℝ) (s : ℕ → ℝ) (r : ℕ) :
    excursionVariable a s ^ r =
      X ^ (2 * r) * momentSeries s ^ r * scalarInvPow a r := by
  unfold excursionVariable
  rw [mul_pow, mul_pow, ← pow_mul]
  have hG := scalarInvPow_eq_pow a r
  rw [hG]

/-- Coefficient of a positive excursion power. -/
lemma coeff_excursionVariable_pow (a : ℝ) (s : ℕ → ℝ)
    {r m : ℕ} (hr : r ≠ 0) (hrm : 2 * r ≤ m) :
    coeff m (excursionVariable a s ^ r) =
      ∑ j ∈ Finset.range (m - 2 * r + 1),
        (Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          a ^ (m - 2 * r - j) * momentConv s r j := by
  rw [excursionVariable_pow, mul_assoc, coeff_X_pow_mul']
  rw [if_pos hrm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_momentSeries_pow, coeff_scalarInvPow_succ]
  simp only [Nat.succ_sub_one, Nat.add_comm]
  ring

/-- Differentiating one excursion power produces the factor `m/r` at coefficient `m-1`. -/
lemma coeff_derivative_excursion_mul_pow (a : ℝ) (s : ℕ → ℝ)
    {r m : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
    coeff (m - 1) (((PowerSeries.derivative ℝ) (excursionVariable a s)) *
        excursionVariable a s ^ (r - 1)) =
      (m / r : ℝ) * coeff m (excursionVariable a s ^ r) := by
  have hpow := PowerSeries.derivative_pow ℝ (excursionVariable a s) r
  have hc := congrArg (coeff (m - 1)) hpow
  rw [coeff_derivative] at hc
  have hmcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)
  have hrcast : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hrc : (r : ℝ⟦X⟧) = C (r : ℝ) := by simp
  rw [hrc, mul_assoc, coeff_C_mul] at hc
  rw [show m - 1 + 1 = m by omega] at hc
  rw [hmcast] at hc
  calc
    coeff (m - 1) (((PowerSeries.derivative ℝ) (excursionVariable a s)) *
        excursionVariable a s ^ (r - 1)) =
      coeff (m - 1) (excursionVariable a s ^ (r - 1) *
        ((PowerSeries.derivative ℝ) (excursionVariable a s))) := by rw [mul_comm]
    _ = (m / r : ℝ) * coeff m (excursionVariable a s ^ r) := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hrcast).2
      calc
        coeff (m - 1) (excursionVariable a s ^ (r - 1) *
            ((PowerSeries.derivative ℝ) (excursionVariable a s))) * (r : ℝ) =
          (r : ℝ) * coeff (m - 1) (excursionVariable a s ^ (r - 1) *
            ((PowerSeries.derivative ℝ) (excursionVariable a s))) := by ring
        _ = coeff m (excursionVariable a s ^ r) * (m : ℝ) := hc.symm
        _ = _ := by ring

/-- Factorized logarithmic derivative of the path denominator. -/
lemma derivative_pathDenominator_mul_pathSeries (a : ℝ) (s : ℕ → ℝ) :
    ((PowerSeries.derivative ℝ) (pathDenominator a s)) * pathSeries a s =
      -C a * scalarInvPow a 1 -
        ((PowerSeries.derivative ℝ) (excursionVariable a s)) *
          ((1 - C a * X) * pathSeries a s) := by
  let A : ℝ⟦X⟧ := 1 - C a * X
  let Z : ℝ⟦X⟧ := excursionVariable a s
  let P : ℝ⟦X⟧ := pathSeries a s
  have hscalar : A * scalarInvPow a 1 = 1 := scalarInvPow_one_mul a
  have hDP : pathDenominator a s * P = 1 := pathDenominator_mul_pathSeries a s
  have hfactor : pathDenominator a s = A * (1 - Z) := by
    change pathDenominator a s =
      (1 - C a * X) * (1 - excursionVariable a s)
    unfold pathDenominator excursionVariable
    calc
      1 - C a * X - X ^ 2 * momentSeries s =
          (1 - C a * X) - X ^ 2 * momentSeries s *
            ((1 - C a * X) * scalarInvPow a 1) := by
              rw [scalarInvPow_one_mul]
              ring
      _ = _ := by ring
  have hZP : (1 - Z) * P = scalarInvPow a 1 := by
    calc
      (1 - Z) * P =
          (scalarInvPow a 1 * A) * ((1 - Z) * P) := by
            rw [mul_comm (scalarInvPow a 1), hscalar, one_mul]
      _ = scalarInvPow a 1 * (A * ((1 - Z) * P)) := by ring
      _ = scalarInvPow a 1 * (pathDenominator a s * P) := by rw [hfactor]; ring
      _ = _ := by rw [hDP, mul_one]
  have hAder : (PowerSeries.derivative ℝ) A = -C a := by
    dsimp [A]
    simp
  change A.derivativeFun = -C a at hAder
  rw [hfactor]
  change (PowerSeries.derivativeFun (A * (1 - Z))) * P = _
  rw [PowerSeries.derivativeFun_mul]
  simp only [smul_eq_mul]
  rw [hAder]
  have hZder : PowerSeries.derivativeFun (1 - Z) =
      -PowerSeries.derivativeFun Z := by
    change (PowerSeries.derivative ℝ) (1 - Z) =
      -(PowerSeries.derivative ℝ) Z
    rw [map_sub]
    simp
  rw [hZder]
  calc
    (A * -PowerSeries.derivativeFun Z + (1 - Z) * -C a) * P =
        -C a * ((1 - Z) * P) - PowerSeries.derivativeFun Z * (A * P) := by ring
    _ = _ := by rw [hZP]; rfl

/-- The excursion derivative has a visible factor `X`; this makes the finite geometric remainder
vanish at the coefficient being extracted. -/
lemma derivative_excursionVariable_eq_X_mul (a : ℝ) (s : ℕ → ℝ) :
    (PowerSeries.derivative ℝ) (excursionVariable a s) =
      X * ((2 : ℝ⟦X⟧) * (momentSeries s * scalarInvPow a 1) +
        X * (PowerSeries.derivative ℝ) (momentSeries s * scalarInvPow a 1)) := by
  unfold excursionVariable
  rw [show X ^ 2 * momentSeries s * scalarInvPow a 1 =
      X ^ 2 * (momentSeries s * scalarInvPow a 1) by ring]
  change PowerSeries.derivativeFun
      (X ^ 2 * (momentSeries s * scalarInvPow a 1)) = _
  rw [PowerSeries.derivativeFun_mul]
  simp only [smul_eq_mul]
  have hxpow := PowerSeries.derivative_pow ℝ (X : ℝ⟦X⟧) 2
  change PowerSeries.derivativeFun (X ^ 2) = _ at hxpow
  rw [hxpow]
  change X ^ 2 * (PowerSeries.derivative ℝ) (momentSeries s * scalarInvPow a 1) +
      momentSeries s * scalarInvPow a 1 *
        ((2 : ℝ⟦X⟧) * X ^ (2 - 1) * (PowerSeries.derivative ℝ) X) = _
  rw [PowerSeries.derivative_X (R := ℝ)]
  norm_num
  ring

/-- Exact finite coefficient formula for one logarithmic derivative. -/
theorem coeff_derivative_pathDenominator_mul_pathSeries (a : ℝ) (s : ℕ → ℝ)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    coeff (m - 1)
        (((PowerSeries.derivative ℝ) (pathDenominator a s)) * pathSeries a s) =
      -a ^ m -
        ∑ k ∈ Finset.range ((m - 1) / 2),
          (m / (k + 1) : ℝ) *
            coeff m (excursionVariable a s ^ (k + 1)) := by
  rw [derivative_pathDenominator_mul_pathSeries]
  have hgeo := scalar_pathSeries_geometric a s ((m - 1) / 2)
  have hmul := congrArg
    (fun F => ((PowerSeries.derivative ℝ) (excursionVariable a s)) * F) hgeo
  have hrem : coeff (m - 1)
      (((PowerSeries.derivative ℝ) (excursionVariable a s)) *
        (excursionVariable a s ^ ((m - 1) / 2) *
          ((1 - C a * X) * pathSeries a s))) = 0 := by
    rw [derivative_excursionVariable_eq_X_mul, excursionVariable_pow]
    have hdeg : 2 * ((m - 1) / 2) + 1 = m := by
      rcases hm with ⟨t, ht⟩
      omega
    rw [show
      X * ((2 : ℝ⟦X⟧) * (momentSeries s * scalarInvPow a 1) +
          X * (PowerSeries.derivative ℝ) (momentSeries s * scalarInvPow a 1)) *
          (X ^ (2 * ((m - 1) / 2)) * momentSeries s ^ ((m - 1) / 2) *
            scalarInvPow a ((m - 1) / 2) *
            ((1 - C a * X) * pathSeries a s)) =
        X ^ (2 * ((m - 1) / 2) + 1) *
          (((2 : ℝ⟦X⟧) * (momentSeries s * scalarInvPow a 1) +
              X * (PowerSeries.derivative ℝ) (momentSeries s * scalarInvPow a 1)) *
            momentSeries s ^ ((m - 1) / 2) *
            scalarInvPow a ((m - 1) / 2) *
            ((1 - C a * X) * pathSeries a s)) by
              rw [pow_succ']; ring]
    rw [hdeg, coeff_X_pow_mul']
    rw [if_neg (by omega)]
  rw [mul_add, Finset.mul_sum] at hmul
  have hcoeff := congrArg (coeff (m - 1)) hmul
  simp only [map_add, map_sum] at hcoeff
  rw [hrem, add_zero] at hcoeff
  rw [map_sub]
  rw [hcoeff]
  have hscalar : coeff (m - 1) (-C a * scalarInvPow a 1) = -a ^ m := by
    rw [show -C a * scalarInvPow a 1 =
        -(C a * scalarInvPow a 1) by ring]
    rw [map_neg, coeff_C_mul, coeff_scalarInvPow_succ]
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have hmpos : 0 < m := by omega
    rw [← pow_succ']
    congr 2
    omega
  rw [hscalar]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
    (coeff_derivative_excursion_mul_pow a s
      (r := k + 1) (m := m) (by omega) (by omega))

/-- Alternating the input moment series alternates every convolution coefficient. -/
lemma momentConv_signed (s : ℕ → ℝ) : ∀ r j : ℕ,
    momentConv (signedMoment s) r j = (-1 : ℝ) ^ j * momentConv s r j
  | 0, 0 => by simp
  | 0, j + 1 => by simp
  | r + 1, j => by
      rw [momentConv_succ, momentConv_succ]
      simp only [signedMoment]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [momentConv_signed s r (j - k)]
      have hkle : k ≤ j := by
        rw [Finset.mem_range] at hk
        omega
      have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (j - k) = (-1 : ℝ) ^ j := by
        rw [← pow_add]
        congr 1
        omega
      calc
        (-1 : ℝ) ^ k * s k *
            ((-1 : ℝ) ^ (j - k) * momentConv s r (j - k)) =
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (j - k)) *
            (s k * momentConv s r (j - k)) := by ring
        _ = _ := by rw [hsign]

/-- Pairing the two signed logarithmic derivatives gives one `momentShiftTerm`. -/
lemma coeff_excursion_signed_pair_eq_momentShiftTerm (q : ℝ) (s : ℕ → ℝ)
    {m r : ℕ} (hm : Odd m) (hr : r ≠ 0) (hrm : 2 * r < m) :
    (m / r : ℝ) *
        coeff m (excursionVariable (1 - q) (signedMoment s) ^ r) -
      (m / r : ℝ) *
        coeff m (excursionVariable (-q) (signedMoment s) ^ r) =
      momentShiftTerm m r q s := by
  rw [coeff_excursionVariable_pow (1 - q) (signedMoment s) hr (by omega),
    coeff_excursionVariable_pow (-q) (signedMoment s) hr (by omega)]
  unfold momentShiftTerm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [momentConv_signed]
  have hjlt : j < m - 2 * r + 1 := Finset.mem_range.mp hj
  have hdj : m - 2 * r - j + j = m - 2 * r := by omega
  have hodd : Odd (m - 2 * r) := by
    rcases hm with ⟨t, ht⟩
    have hrt : r ≤ t := by omega
    exact ⟨t - r, by omega⟩
  have hsign :
      (-q) ^ (m - 2 * r - j) * (-1 : ℝ) ^ j =
        -q ^ (m - 2 * r - j) := by
    rw [neg_pow]
    calc
      ((-1 : ℝ) ^ (m - 2 * r - j) * q ^ (m - 2 * r - j)) *
          (-1 : ℝ) ^ j =
        ((-1 : ℝ) ^ (m - 2 * r - j) * (-1 : ℝ) ^ j) *
          q ^ (m - 2 * r - j) := by ring
      _ = (-1 : ℝ) ^ (m - 2 * r) * q ^ (m - 2 * r - j) := by
        rw [← pow_add, hdj]
      _ = _ := by rw [hodd.neg_one_pow]; ring
  have hterm :
      (Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          (-q) ^ (m - 2 * r - j) *
          ((-1 : ℝ) ^ j * momentConv s r j) =
        -((Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          q ^ (m - 2 * r - j) * momentConv s r j) := by
    calc
      (Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          (-q) ^ (m - 2 * r - j) *
          ((-1 : ℝ) ^ j * momentConv s r j) =
        (Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          ((-q) ^ (m - 2 * r - j) * (-1 : ℝ) ^ j) *
          momentConv s r j := by ring
      _ = _ := by rw [hsign]; ring
  rw [hterm]
  ring

/-- Coefficient form of the complete two-sided spectral shift. -/
theorem coeff_derivative_resolvent_right_eq_shift (q : ℝ) (s : ℕ → ℝ)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    coeff (m - 1)
        (((PowerSeries.derivative ℝ)
            (pathDenominator (-q) (signedMoment s))) *
            pathSeries (-q) (signedMoment s) -
          ((PowerSeries.derivative ℝ)
            (pathDenominator (1 - q) (signedMoment s))) *
            pathSeries (1 - q) (signedMoment s)) =
      q ^ m + (1 - q) ^ m +
        ∑ k ∈ Finset.range ((m - 1) / 2),
          momentShiftTerm m (k + 1) q s := by
  rw [map_sub,
    coeff_derivative_pathDenominator_mul_pathSeries (-q) (signedMoment s) hm hm3,
    coeff_derivative_pathDenominator_mul_pathSeries (1 - q) (signedMoment s) hm hm3]
  have hmq : -(-q) ^ m = q ^ m := by rw [hm.neg_pow]; ring
  rw [hmq]
  have hpairs :
      (∑ k ∈ Finset.range ((m - 1) / 2),
          ((m / (k + 1) : ℝ) *
            coeff m (excursionVariable (1 - q) (signedMoment s) ^ (k + 1)) -
          (m / (k + 1) : ℝ) *
            coeff m (excursionVariable (-q) (signedMoment s) ^ (k + 1)))) =
        ∑ k ∈ Finset.range ((m - 1) / 2),
          momentShiftTerm m (k + 1) q s := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : k < (m - 1) / 2 := Finset.mem_range.mp hk
    have hrm : 2 * (k + 1) < m := by
      rcases hm with ⟨t, ht⟩
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      (coeff_excursion_signed_pair_eq_momentShiftTerm q s
        (m := m) (r := k + 1) hm (by omega) hrm)
  have hsum :
      (∑ k ∈ Finset.range ((m - 1) / 2),
          (m / (k + 1) : ℝ) *
            coeff m (excursionVariable (1 - q) (signedMoment s) ^ (k + 1))) -
        (∑ k ∈ Finset.range ((m - 1) / 2),
          (m / (k + 1) : ℝ) *
            coeff m (excursionVariable (-q) (signedMoment s) ^ (k + 1))) =
        ∑ k ∈ Finset.range ((m - 1) / 2),
          momentShiftTerm m (k + 1) q s := by
    rw [← Finset.sum_sub_distrib]
    exact hpairs
  rw [← hsum]
  ring

/-- Alternating both the moment sequence and the path coefficient is the same as negating `q`. -/
lemma pathMoment_neg_signed (q : ℝ) (s : ℕ → ℝ) (N : ℕ) :
    pathMoment (-q) (signedMoment s) N = (-1 : ℝ) ^ N * pathMoment q s N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero => simp
    | succ n =>
      rw [pathMoment_succ, pathMoment_succ, ih n (by omega)]
      simp only [signedMoment]
      have hreplace :
          (∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i * s i) *
              pathMoment (-q) (signedMoment s) (n - 1 - i)) =
            ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i * s i) *
              ((-1 : ℝ) ^ (n - 1 - i) * pathMoment q s (n - 1 - i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ih (n - 1 - i) (by
          rw [Finset.mem_range] at hi
          omega)]
      have hsum :
          (∑ i ∈ Finset.range n,
              ((-1 : ℝ) ^ i * s i) *
                ((-1 : ℝ) ^ (n - 1 - i) * pathMoment q s (n - 1 - i))) =
            (-1 : ℝ) ^ (n + 1) *
              ∑ i ∈ Finset.range n, s i * pathMoment q s (n - 1 - i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        have hsign : (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - 1 - i) =
            (-1 : ℝ) ^ (n + 1) := by
          calc
            (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - 1 - i) =
                (-1 : ℝ) ^ (n - 1) := by
                  rw [← pow_add]
                  congr 1
                  omega
            _ = (-1 : ℝ) ^ ((n - 1) + 2) := by
                  rw [pow_add, pow_two]
                  norm_num
            _ = _ := by congr 1 <;> omega
        calc
          (-1 : ℝ) ^ i * s i *
              ((-1 : ℝ) ^ (n - 1 - i) * pathMoment q s (n - 1 - i)) =
              ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - 1 - i)) *
                (s i * pathMoment q s (n - 1 - i)) := by ring
          _ = _ := by rw [hsign]
      rw [hreplace, hsum]
      have hqsign : -q * ((-1 : ℝ) ^ n * pathMoment q s n) =
          (-1 : ℝ) ^ (n + 1) * (q * pathMoment q s n) := by
        rw [pow_succ]
        ring
      rw [hqsign]
      ring

/-- The two alternating path denominators differ by the single hub variable `X`. -/
lemma pathDenominator_neg_eq_add_X (q : ℝ) (s : ℕ → ℝ) :
    pathDenominator (-q) (signedMoment s) =
      pathDenominator (1 - q) (signedMoment s) + X := by
  unfold pathDenominator
  simp only [map_neg, map_sub, map_one]
  ring

/-- Resolvent identity behind the necklace convolution.  If `Q` is the complement path series and
`R` is the sign-alternated original path series, then `Q - R = X Q R`. -/
theorem pathSeries_resolvent_difference (q : ℝ) (s : ℕ → ℝ) :
    pathSeries (1 - q) (signedMoment s) - pathSeries (-q) (signedMoment s) =
      X * pathSeries (1 - q) (signedMoment s) * pathSeries (-q) (signedMoment s) := by
  let DQ := pathDenominator (1 - q) (signedMoment s)
  let DR := pathDenominator (-q) (signedMoment s)
  let Q := pathSeries (1 - q) (signedMoment s)
  let R := pathSeries (-q) (signedMoment s)
  have hQ : DQ * Q = 1 := pathDenominator_mul_pathSeries _ _
  have hR : DR * R = 1 := pathDenominator_mul_pathSeries _ _
  have hD : DR = DQ + X := pathDenominator_neg_eq_add_X q s
  change Q - R = X * Q * R
  calc
    Q - R = Q * (DR * R) - (DQ * Q) * R := by rw [hQ, hR]; ring
    _ = X * Q * R := by rw [hD]; ring

/-- Differentiated form of the resolvent identity.  Its coefficient of degree `m-1` is precisely
the necklace expression plus the terminal path coefficient; the right side is the difference of
the two logarithmic derivatives whose coefficient expansion is `momentShiftTerm`. -/
theorem pathSeries_derivative_resolvent_identity (q : ℝ) (s : ℕ → ℝ) :
    (PowerSeries.derivative ℝ)
        (X * pathSeries (-q) (signedMoment s)) *
        (1 + X * pathSeries (1 - q) (signedMoment s)) =
      (PowerSeries.derivative ℝ) (pathDenominator (-q) (signedMoment s)) *
          pathSeries (-q) (signedMoment s) -
        (PowerSeries.derivative ℝ) (pathDenominator (1 - q) (signedMoment s)) *
          pathSeries (1 - q) (signedMoment s) := by
  let DQ := pathDenominator (1 - q) (signedMoment s)
  let DR := pathDenominator (-q) (signedMoment s)
  let Q := pathSeries (1 - q) (signedMoment s)
  let R := pathSeries (-q) (signedMoment s)
  have hQ : DQ * Q = 1 := pathDenominator_mul_pathSeries _ _
  have hR : DR * R = 1 := pathDenominator_mul_pathSeries _ _
  have hD : DR = DQ + X := pathDenominator_neg_eq_add_X q s
  have hres : Q - R = X * Q * R := pathSeries_resolvent_difference q s
  have hdR : DR * (PowerSeries.derivative ℝ) R +
      R * (PowerSeries.derivative ℝ) DR = 0 := by
    have h := congrArg (PowerSeries.derivative ℝ) hR
    simpa using h
  have hdD : (PowerSeries.derivative ℝ) DR =
      (PowerSeries.derivative ℝ) DQ + 1 := by
    rw [hD]
    simp
  have hone : 1 + X * Q = DR * Q := by
    rw [hD]
    rw [add_mul, hQ]
  change (PowerSeries.derivative ℝ) (X * R) * (1 + X * Q) =
    (PowerSeries.derivative ℝ) DR * R - (PowerSeries.derivative ℝ) DQ * Q
  rw [hone]
  have hprod : (PowerSeries.derivative ℝ) (X * R) =
      R + X * (PowerSeries.derivative ℝ) R := by
    change PowerSeries.derivativeFun (X * R) =
      R + X * PowerSeries.derivativeFun R
    rw [PowerSeries.derivativeFun_mul]
    have hx : PowerSeries.derivativeFun (X : ℝ⟦X⟧) = 1 :=
      PowerSeries.derivative_X (R := ℝ)
    rw [hx]
    simp only [smul_eq_mul, mul_one]
    abel
  have hdR' : DR * (PowerSeries.derivative ℝ) R =
      -(R * (PowerSeries.derivative ℝ) DR) := by
    linear_combination hdR
  have hsimplify :
      (R + X * (PowerSeries.derivative ℝ) R) * (DR * Q) =
        Q - X * Q * (PowerSeries.derivative ℝ) DR * R := by
    calc
      (R + X * (PowerSeries.derivative ℝ) R) * (DR * Q) =
          Q * (DR * R + X * (DR * (PowerSeries.derivative ℝ) R)) := by ring
      _ = Q * (1 - X * (R * (PowerSeries.derivative ℝ) DR)) := by
        rw [hR, hdR']
        ring
      _ = _ := by ring
  rw [hprod, hsimplify, hdD]
  linear_combination (1 + (PowerSeries.derivative ℝ) DQ) * hres

/-! ## Coefficient extraction: the necklace side -/

/-- The derivative of the sign-alternated path resolvent has the weighted path coefficients
appearing in the necklace convolution. -/
lemma coeff_derivative_X_mul_pathSeries_neg (q : ℝ) (s : ℕ → ℝ) (b : ℕ) :
    coeff b ((PowerSeries.derivative ℝ)
        (X * pathSeries (-q) (signedMoment s))) =
      (b + 1 : ℝ) * ((-1 : ℝ) ^ b * pathMoment q s b) := by
  rw [coeff_derivative]
  have hx := coeff_X_pow_mul (pathSeries (-q) (signedMoment s)) 1 b
  have hx' : coeff (1 + b) (X * pathSeries (-q) (signedMoment s)) =
      coeff b (pathSeries (-q) (signedMoment s)) := by
    simpa only [pow_one, add_comm] using hx
  rw [show b + 1 = 1 + b by omega, hx', coeff_pathSeries,
    pathMoment_neg_signed]
  push_cast
  ring

/-- Positive coefficients of `1 + X P` are the preceding path coefficients. -/
lemma coeff_one_add_X_mul_pathSeries (q : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    coeff n (1 + X * pathSeries q s) =
      if n = 0 then 1 else pathMoment q s (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [map_add, coeff_one, Nat.add_eq_zero, one_ne_zero, and_false,
        ↓reduceIte, zero_add]
      simpa using coeff_X_pow_mul (pathSeries q s) 1 n

/-- The degree `m-1` coefficient on the left of the differentiated resolvent identity is the
universal necklace expression plus its terminal path coefficient. -/
theorem coeff_derivative_resolvent_left_eq_neckMoment (q : ℝ) (s : ℕ → ℝ)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    coeff (m - 1)
        (((PowerSeries.derivative ℝ)
            (X * pathSeries (-q) (signedMoment s))) *
          (1 + X * pathSeries (1 - q) (signedMoment s))) =
      neckMoment m q s + pathMoment q s (m - 1) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.fst, Prod.snd]
  rw [show (m - 1).succ = (m - 1) + 1 by omega, Finset.sum_range_succ]
  have hbody :
      (∑ b ∈ Finset.range (m - 1),
          coeff b ((PowerSeries.derivative ℝ)
              (X * pathSeries (-q) (signedMoment s))) *
            coeff (m - 1 - b)
              (1 + X * pathSeries (1 - q) (signedMoment s))) =
        ∑ b ∈ Finset.range (m - 1),
          (b + 1 : ℝ) * ((-1 : ℝ) ^ b *
            (pathMoment (1 - q) (signedMoment s) (m - 2 - b) *
              pathMoment q s b)) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [coeff_derivative_X_mul_pathSeries_neg,
      coeff_one_add_X_mul_pathSeries]
    rw [if_neg (by
      rw [Finset.mem_range] at hb
      omega)]
    have hind : m - 1 - b - 1 = m - 2 - b := by
      rw [Finset.mem_range] at hb
      omega
    rw [hind]
    ring
  rw [hbody, coeff_derivative_X_mul_pathSeries_neg,
    coeff_one_add_X_mul_pathSeries]
  simp only [Nat.sub_self, if_pos, mul_one]
  have hsign : (-1 : ℝ) ^ (m - 1) = 1 := by
    obtain ⟨k, hk⟩ := hm
    subst m
    rw [show 2 * k + 1 - 1 = 2 * k by omega, pow_mul]
    norm_num
  rw [hsign]
  unfold neckMoment
  push_cast
  ring

/-! ## Universal and graphon E5b identities -/

/-- **Universal E5b identity.**  The finite necklace expression is the sharp scalar baseline plus
the already-defined moment defect `momentPhi`. -/
theorem neckMoment_eq_baseline_add_momentPhi (q : ℝ) (s : ℕ → ℝ)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    neckMoment m q s =
      (1 - q) ^ m - (1 - q) * q ^ (m - 1) + momentPhi m q s := by
  have hseries := congrArg (coeff (m - 1))
    (pathSeries_derivative_resolvent_identity q s)
  rw [coeff_derivative_resolvent_left_eq_neckMoment q s hm hm3,
    coeff_derivative_resolvent_right_eq_shift q s hm hm3] at hseries
  have hpath := pathMoment_eq_pow_add_sum_momentPathTerm q s hm hm3
  rw [hpath] at hseries
  unfold momentPhi momentPhiTerm
  rw [Finset.sum_sub_distrib]
  have hqm : q ^ m = q ^ (m - 1) * q := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  rw [hqm] at hseries
  linear_combination hseries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-- **E5b.**  The actual graphon necklace defect is exactly the sharp baseline plus `momentPhi`
of the complement compression moments. -/
theorem neckSum_eq_baseline_add_momentPhi (hW : IsGraphon W μ) {m : ℕ}
    (hm : Odd m) (hm3 : 3 ≤ m) :
    neckSum W μ m =
      edgeDensity W μ ^ m -
        edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) +
      momentPhi m (1 - edgeDensity W μ) (specMoment (compl W) μ) := by
  rw [neckSum_eq_neckMoment hW hm hm3,
    neckMoment_eq_baseline_add_momentPhi (1 - edgeDensity W μ)
      (specMoment (compl W) μ) hm hm3]
  ring

end OddCycleBound.HighDensity
