import OddCycleBound.RegionII.Certificate.Intervals
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Soundness of the Region-II rational interval primitives

These lemmas are the trusted bridge from executable rational comparisons to
the real square roots, exponentials, and powers occurring in the scalar proof.
-/

namespace OddCycleBound.RegionII.Certificate

lemma roundDown_le (x : ℚ) {den : Nat} (hden : 0 < den) :
    roundDown x den ≤ x := by
  have hdq : (0 : ℚ) < den := by exact_mod_cast hden
  rw [roundDown, div_le_iff₀ hdq]
  simpa using (Int.floor_le (x * den))

lemma le_roundUp (x : ℚ) {den : Nat} (hden : 0 < den) :
    x ≤ roundUp x den := by
  have hdq : (0 : ℚ) < den := by exact_mod_cast hden
  rw [roundUp, le_div_iff₀ hdq]
  simpa using (Int.le_ceil (x * den))

lemma roundDown_nonneg {x : ℚ} (hx : 0 ≤ x) {den : Nat} (hden : 0 < den) :
    0 ≤ roundDown x den := by
  have hdq : (0 : ℚ) < den := by exact_mod_cast hden
  rw [roundDown]
  exact div_nonneg (by exact_mod_cast (Int.floor_nonneg.2 (mul_nonneg hx hdq.le))) hdq.le

lemma roundUp_nonneg {x : ℚ} (hx : 0 ≤ x) {den : Nat} (hden : 0 < den) :
    0 ≤ roundUp x den :=
  hx.trans (le_roundUp x hden)

lemma sqrtBracketOK_sound {x lo hi : ℚ} (h : sqrtBracketOK x lo hi = true) :
    (lo : ℝ) ≤ Real.sqrt x ∧ Real.sqrt x ≤ (hi : ℝ) := by
  have hq : 0 ≤ lo ∧ lo * lo ≤ x ∧ x ≤ hi * hi ∧ 0 ≤ hi := by
    simpa [sqrtBracketOK] using h
  have hlo : (0 : ℝ) ≤ lo := by exact_mod_cast hq.1
  have hlosq : (lo : ℝ) ^ 2 ≤ x := by
    simpa [pow_two] using (show ((lo * lo : ℚ) : ℝ) ≤ x by exact_mod_cast hq.2.1)
  have hhi : (0 : ℝ) ≤ hi := by exact_mod_cast hq.2.2.2
  have hhisq : (x : ℝ) ≤ hi ^ 2 := by
    simpa [pow_two] using (show (x : ℝ) ≤ ((hi * hi : ℚ) : ℝ) by exact_mod_cast hq.2.2.1)
  have hx : (0 : ℝ) ≤ x := (sq_nonneg (lo : ℝ)).trans hlosq
  exact ⟨(Real.le_sqrt hlo hx).2 hlosq,
    Real.sqrt_le_iff.mpr ⟨hhi, hhisq⟩⟩

lemma partialExp_fst (x : ℚ) (n : Nat) :
    (partialExp x n).1 = x ^ n / n.factorial := by
  rfl

lemma partialExp_snd (x : ℚ) (n : Nat) :
    (partialExp x n).2 =
      ∑ i ∈ Finset.range (n + 1), x ^ i / i.factorial := by
  rfl

lemma partialExp_pos {x : ℚ} (hx : 0 ≤ x) (n : Nat) :
    0 < (partialExp x n).2 := by
  rw [partialExp_snd]
  have hzero : (0 : ℚ) < x ^ 0 / Nat.factorial 0 := by norm_num
  exact hzero.trans_le (Finset.single_le_sum
    (fun i hi => div_nonneg (pow_nonneg hx i) (by positivity)) (by simp))

lemma cast_partialExp_snd (x : ℚ) (n : Nat) :
    ((partialExp x n).2 : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (x : ℝ) ^ i / i.factorial := by
  rw [partialExp_snd]
  push_cast
  rfl

lemma exp_neg_le_inv_partialExp {t t' : ℚ} (ht' : 0 ≤ t') (hle : t' ≤ t) (n : Nat) :
    Real.exp (-(t : ℝ)) ≤ ((1 / (partialExp t' n).2 : ℚ) : ℝ) := by
  have ht'R : (0 : ℝ) ≤ t' := by exact_mod_cast ht'
  have hsum := Real.sum_le_exp_of_nonneg ht'R (n + 1)
  rw [← cast_partialExp_snd] at hsum
  have hposQ := partialExp_pos ht' n
  have hposR : (0 : ℝ) < (partialExp t' n).2 := by exact_mod_cast hposQ
  have hinv : 1 / Real.exp (t' : ℝ) ≤ 1 / ((partialExp t' n).2 : ℝ) :=
    one_div_le_one_div_of_le hposR hsum
  calc
    Real.exp (-(t : ℝ)) ≤ Real.exp (-(t' : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (by exact_mod_cast hle)
    _ = 1 / Real.exp (t' : ℝ) := by rw [Real.exp_neg]; simp [one_div]
    _ ≤ 1 / ((partialExp t' n).2 : ℝ) := hinv
    _ = ((1 / (partialExp t' n).2 : ℚ) : ℝ) := by norm_cast

lemma expNegUpB_sound {t : ℚ} (ht : 0 ≤ t) :
    Real.exp (-(t : ℝ)) ≤ (expNegUpB t : ℝ) := by
  apply exp_neg_le_inv_partialExp
  · exact roundDown_nonneg ht (by norm_num : 0 < 10 ^ 12)
  · exact roundDown_le t (by norm_num : 0 < 10 ^ 12)

lemma expNegUpB_le_one {t : ℚ} (ht : 0 ≤ t) :
    (expNegUpB t : Real) ≤ 1 := by
  let t' := roundDown t (10 ^ 12)
  have ht' : 0 ≤ t' := roundDown_nonneg ht (by norm_num)
  have hsum : 1 ≤ (partialExp t' 40).2 := by
    rw [partialExp_snd]
    have hzero : (1 : ℚ) = t' ^ 0 / Nat.factorial 0 := by norm_num
    rw [hzero]
    exact Finset.single_le_sum
      (fun i _ => div_nonneg (pow_nonneg ht' i) (by positivity)) (by simp)
  have hsumR : (1 : Real) ≤ ((partialExp t' 40).2 : Real) := by
    exact_mod_cast hsum
  rw [expNegUpB]
  push_cast
  simpa [t'] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hsumR

lemma expNegUpC_sound {t : ℚ} (ht : 0 ≤ t) :
    Real.exp (-(t : ℝ)) ≤ (expNegUpC t : ℝ) := by
  let t' := min (roundDown t (10 ^ 9)) 400
  have ht' : 0 ≤ t' := le_min (roundDown_nonneg ht (by norm_num)) (by norm_num)
  have hle : t' ≤ t :=
    (min_le_left _ _).trans (roundDown_le t (by norm_num : 0 < 10 ^ 9))
  exact exp_neg_le_inv_partialExp ht' hle (expCutoffC t' (1 / 10 ^ 50) 499 1 1)

lemma directedPowUpGo_sound {den : Nat} (hden : 0 < den)
    {r b : ℚ} (hr : 0 ≤ r) (hb : 0 ≤ b) (n : Nat) :
    r * b ^ n ≤ directedPowUpGo den r b n := by
  induction n using Nat.strong_induction_on generalizing r b with
  | h n ih =>
      rw [directedPowUpGo]
      split_ifs with hn hodd
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hdiv : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        let r' := roundUp (r * b) den
        let b' := roundUp (b * b) den
        have hr' : 0 ≤ r' := roundUp_nonneg (mul_nonneg hr hb) hden
        have hb' : 0 ≤ b' := roundUp_nonneg (mul_nonneg hb hb) hden
        have hrec := ih (n / 2) hdiv hr' hb'
        have hpow : b ^ n = b * (b * b) ^ (n / 2) := by
          conv_lhs => rw [← Nat.mod_add_div n 2]
          rw [pow_add, pow_mul, hodd]
          simp [pow_two]
        rw [hpow, ← mul_assoc]
        exact (mul_le_mul (le_roundUp (r * b) hden)
          (pow_le_pow_left₀ (mul_nonneg hb hb) (le_roundUp (b * b) hden) _)
          (pow_nonneg (mul_nonneg hb hb) _) hr').trans hrec
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hdiv : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        have hzero : n % 2 = 0 := (Nat.mod_two_eq_zero_or_one n).resolve_right hodd
        let b' := roundUp (b * b) den
        have hb' : 0 ≤ b' := roundUp_nonneg (mul_nonneg hb hb) hden
        have hrec := ih (n / 2) hdiv hr hb'
        have hpow : b ^ n = (b * b) ^ (n / 2) := by
          conv_lhs => rw [← Nat.mod_add_div n 2]
          rw [pow_add, pow_mul, hzero]
          simp [pow_two]
        rw [hpow]
        exact (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg hb hb) (le_roundUp (b * b) hden) _) hr).trans hrec

lemma directedPowUp_sound {base : ℚ} (hbase : 0 ≤ base) (n : Nat) :
    base ^ n ≤ directedPowUp base n := by
  have hden : 0 < (10 ^ 12 : Nat) := by norm_num
  have hround : 0 ≤ roundUp base (10 ^ 12) := roundUp_nonneg hbase hden
  calc
    base ^ n ≤ roundUp base (10 ^ 12) ^ n :=
      pow_le_pow_left₀ hbase (le_roundUp base hden) n
    _ = 1 * roundUp base (10 ^ 12) ^ n := by simp
    _ ≤ directedPowUpGo (10 ^ 12) 1 (roundUp base (10 ^ 12)) n :=
      directedPowUpGo_sound hden zero_le_one hround n
    _ = directedPowUp base n := rfl

lemma directedPowDownGo_sound {den : Nat} (hden : 0 < den)
    {r b : ℚ} (hr : 0 ≤ r) (hb : 0 ≤ b) (n : Nat) :
    directedPowDownGo den r b n ≤ r * b ^ n := by
  induction n using Nat.strong_induction_on generalizing r b with
  | h n ih =>
      rw [directedPowDownGo]
      split_ifs with hn hodd
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hdiv : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        let r' := roundDown (r * b) den
        let b' := roundDown (b * b) den
        have hr' : 0 ≤ r' := roundDown_nonneg (mul_nonneg hr hb) hden
        have hb' : 0 ≤ b' := roundDown_nonneg (mul_nonneg hb hb) hden
        have hrec := ih (n / 2) hdiv hr' hb'
        have hpow : b ^ n = b * (b * b) ^ (n / 2) := by
          conv_lhs => rw [← Nat.mod_add_div n 2]
          rw [pow_add, pow_mul, hodd]
          simp [pow_two]
        rw [hpow, ← mul_assoc]
        exact hrec.trans (mul_le_mul (roundDown_le (r * b) hden)
          (pow_le_pow_left₀ hb' (roundDown_le (b * b) hden) _)
          (pow_nonneg hb' _) (mul_nonneg hr hb))
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hdiv : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        have hzero : n % 2 = 0 := (Nat.mod_two_eq_zero_or_one n).resolve_right hodd
        let b' := roundDown (b * b) den
        have hb' : 0 ≤ b' := roundDown_nonneg (mul_nonneg hb hb) hden
        have hrec := ih (n / 2) hdiv hr hb'
        have hpow : b ^ n = (b * b) ^ (n / 2) := by
          conv_lhs => rw [← Nat.mod_add_div n 2]
          rw [pow_add, pow_mul, hzero]
          simp [pow_two]
        rw [hpow]
        exact hrec.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hb' (roundDown_le (b * b) hden) _) hr)

lemma directedPowDownGo_nonneg {den : Nat} (hden : 0 < den)
    {r b : ℚ} (hr : 0 ≤ r) (hb : 0 ≤ b) (n : Nat) :
    0 ≤ directedPowDownGo den r b n := by
  induction n using Nat.strong_induction_on generalizing r b with
  | h n ih =>
      rw [directedPowDownGo]
      split_ifs with hn hodd
      · simpa [hn] using hr
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hdiv : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        exact ih (n / 2) hdiv
          (roundDown_nonneg (mul_nonneg hr hb) hden)
          (roundDown_nonneg (mul_nonneg hb hb) hden)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hdiv : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        exact ih (n / 2) hdiv hr
          (roundDown_nonneg (mul_nonneg hb hb) hden)

lemma directedPowDown_sound {base : ℚ} (hbase : 0 ≤ base) (n : Nat) :
    directedPowDown base n ≤ base ^ n := by
  have hden : 0 < (10 ^ 12 : Nat) := by norm_num
  have hround : 0 ≤ roundDown base (10 ^ 12) := roundDown_nonneg hbase hden
  calc
    directedPowDown base n =
        directedPowDownGo (10 ^ 12) 1 (roundDown base (10 ^ 12)) n := rfl
    _ ≤ 1 * roundDown base (10 ^ 12) ^ n :=
      directedPowDownGo_sound hden zero_le_one hround n
    _ = roundDown base (10 ^ 12) ^ n := by simp
    _ ≤ base ^ n := pow_le_pow_left₀ hround (roundDown_le base hden) n

lemma directedPowDown_nonneg {base : ℚ} (hbase : 0 ≤ base) (n : Nat) :
    0 ≤ directedPowDown base n := by
  exact directedPowDownGo_nonneg (by norm_num : 0 < (10 ^ 12 : Nat))
    zero_le_one
    (roundDown_nonneg hbase (by norm_num : 0 < (10 ^ 12 : Nat))) n

end OddCycleBound.RegionII.Certificate
