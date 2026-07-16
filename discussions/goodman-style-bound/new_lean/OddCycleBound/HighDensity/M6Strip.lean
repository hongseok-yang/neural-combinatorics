/-
# High-density theorem — the residual strip (M6), analytic tail `m ≥ 63`

The residual range (`eq:remaining-range`) is `q ≤ 1/3`, `r ≥ 2`, `n > 2r`, `0 < ℓ < q+r/m`.  For
`m ≥ 63` the paper splits on `θ = r/m` and uses a reflection/threshold argument (`lem:threshold`,
`lem:right-reflection`, `lem:left-estimate`).

This file begins with **`lem:threshold`** (`threshold_bound`): the calculus maximum bound
`H(b) = m/((r-1)/b + (n-1)/(n/m)) − b ≤ 2/5` for `0 < b`, `m ≥ 63` odd, `r/m ≥ 1/6`, `n = m−2r`,
`n > 2r`.  It feeds `lem:right-reflection`.  Proved algebraically (no `√`) by completing the square:
`H(b) ≤ 2/5 ⟺ mb ≤ (b+2/5)(A₀ + B₀b)` with `A₀ = r-1`, `B₀ = (n-1)m/n`, which holds because the
discriminant `(A₀ + (2/5)B₀ − m)² ≤ (8/5)A₀B₀` (a cleared quartic in `n,r`, closed by `nlinarith`).
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace OddCycleBound.HighDensity

/-- **`lem:threshold`.**  For odd `m ≥ 63`, `r/m ≥ 1/6` (`m ≤ 6r`), `n = m−2r`, `n > 2r`, and `b > 0`:
`H(b) = m/((r-1)/b + (n-1)/(n/m)) − b ≤ 2/5`.  The maximum of `H` over `b > 0` is `(√m−√(r-1))²/B₀`
(`B₀ = (n-1)m/n`); the bound `< 2/5` is proved here without `√` via the discriminant of the quadratic
`B₀b² + (A₀ + (2/5)B₀ − m)b + (2/5)A₀ ≥ 0`. -/
theorem threshold_bound {m r n : ℕ} (hm63 : 63 ≤ m) (hmodd : m % 2 = 1) (h6r : m ≤ 6 * r)
    (hmn : m = n + 2 * r) (hn2r : 2 * r < n) {b : ℝ} (hb0 : 0 < b) :
    (m : ℝ) / (((r : ℝ) - 1) / b + ((n : ℝ) - 1) / ((n : ℝ) / (m : ℝ))) - b ≤ 2 / 5 := by
  -- real forms of the (integer) constraints
  have hr11 : (11 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 11 ≤ r by omega)
  have h9 : 2 * (n : ℝ) + 13 ≤ 9 * (r : ℝ) := by exact_mod_cast (show 2 * n + 13 ≤ 9 * r by omega)
  have h2 : 2 * (r : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show 2 * r + 1 ≤ n by omega)
  have hn33 : (33 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 33 ≤ n by omega)
  have hmR : (m : ℝ) = (n : ℝ) + 2 * (r : ℝ) := by exact_mod_cast hmn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hm0 : (0 : ℝ) < (m : ℝ) := by rw [hmR]; linarith
  set A0 := (r : ℝ) - 1 with hA0def
  set B0 := ((n : ℝ) - 1) * (m : ℝ) / (n : ℝ) with hB0def
  have hA0pos : 0 < A0 := by rw [hA0def]; linarith
  have hB0pos : 0 < B0 := by
    rw [hB0def]; exact div_pos (mul_pos (by linarith) hm0) hn0
  -- rewrite the nested denominator `(n-1)/(n/m) = B₀`
  have hDrw : ((n : ℝ) - 1) / ((n : ℝ) / (m : ℝ)) = B0 := by
    rw [hB0def, div_div_eq_mul_div]
  rw [hDrw]
  -- discriminant inequality
  have hdisc : (A0 + (2 / 5) * B0 - (m : ℝ)) ^ 2 ≤ (8 / 5) * A0 * B0 := by
    have hcl : (5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
        ≤ 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ) := by
      rw [hA0def, hmR]
      nlinarith [sq_nonneg ((n : ℝ) - 2 * (r : ℝ)), sq_nonneg ((n : ℝ) * (r : ℝ)),
        mul_pos hn0 (by linarith : (0 : ℝ) < (r : ℝ)), sq_nonneg ((n : ℝ) - (r : ℝ)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2 * (r : ℝ) - 1) hn0.le, h9, h2]
    have hkey : (A0 + (2 / 5) * B0 - (m : ℝ)) ^ 2 - (8 / 5) * A0 * B0
        = ((5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
            - 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ)) / (25 * (n : ℝ) ^ 2) := by
      rw [hB0def]; field_simp; ring
    have hnum : (5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
        - 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ) ≤ 0 := by linarith [hcl]
    have hratio : ((5 * A0 * (n : ℝ) + 2 * ((n : ℝ) - 1) * (m : ℝ) - 5 * (m : ℝ) * (n : ℝ)) ^ 2
        - 40 * A0 * ((n : ℝ) - 1) * (m : ℝ) * (n : ℝ)) / (25 * (n : ℝ) ^ 2) ≤ 0 :=
      div_nonpos_iff.mpr (Or.inr ⟨hnum, by positivity⟩)
    linarith [hkey, hratio]
  -- `mb ≤ (b + 2/5)(A₀ + B₀b)`  by completing the square
  have hcore : (m : ℝ) * b ≤ (b + 2 / 5) * (A0 + B0 * b) := by
    have hsq : 4 * B0 * ((b + 2 / 5) * (A0 + B0 * b) - (m : ℝ) * b)
        = (2 * B0 * b + (A0 + (2 / 5) * B0 - (m : ℝ))) ^ 2
          + ((8 / 5) * A0 * B0 - (A0 + (2 / 5) * B0 - (m : ℝ)) ^ 2) := by ring
    nlinarith [hsq, sq_nonneg (2 * B0 * b + (A0 + (2 / 5) * B0 - (m : ℝ))), hdisc, hB0pos, hb0]
  -- conclude `H(b) ≤ 2/5`
  have hABpos : 0 < A0 + B0 * b := add_pos hA0pos (mul_pos hB0pos hb0)
  have hcomb : A0 / b + B0 = (A0 + B0 * b) / b := by field_simp
  rw [hcomb, div_div_eq_mul_div, sub_le_iff_le_add, div_le_iff₀ hABpos]
  nlinarith [hcore]

/-! ### `lem:right-reflection` — the pointwise condition `eq:right-condition` -/

/-- Derivative of `t ↦ log(X+t) − log(X−t)` is `1/(X+t) + 1/(X−t)` (for `X±t > 0`). -/
lemma glog_hasDerivAt {X t : ℝ} (h1 : 0 < X + t) (h2 : 0 < X - t) :
    HasDerivAt (fun s => Real.log (X + s) - Real.log (X - s)) (1 / (X + t) + 1 / (X - t)) t := by
  have h := (((hasDerivAt_id t).const_add X).log (ne_of_gt h1)).sub
    (((hasDerivAt_id t).const_sub X).log (ne_of_gt h2))
  rw [show 1 / (X + t) + 1 / (X - t) = 1 / (X + t) - (-1) / (X - t) from by ring]
  exact h

/-- `X ≤ C` ⇒ `(1/X)·2C²/(C²−t²) ≤ 1/(X+t)+1/(X−t)`  (the pointwise lower bound driving `G' ≥ 0`).
Reduces to `t²(C²−X²) ≥ 0` after clearing the positive denominators. -/
lemma recip_sum_lower {X C t : ℝ} (hX : 0 < X) (hXC : X ≤ C)
    (hXt1 : 0 < X + t) (hXt2 : 0 < X - t) (hCt : 0 < C ^ 2 - t ^ 2) :
    1 / X * (2 * C ^ 2 / (C ^ 2 - t ^ 2)) ≤ 1 / (X + t) + 1 / (X - t) := by
  have hX2t2 : 0 < X ^ 2 - t ^ 2 := by nlinarith [hXt1, hXt2]
  have heq : 1 / (X + t) + 1 / (X - t) = 2 * X / (X ^ 2 - t ^ 2) := by field_simp; ring
  rw [heq, div_mul_div_comm, div_le_div_iff₀ (mul_pos hX hCt) hX2t2]
  nlinarith [mul_nonneg (sq_nonneg t) (by nlinarith [hXC, hX] : (0 : ℝ) ≤ C ^ 2 - X ^ 2)]

/-- **`eq:right-condition` (the core of `lem:right-reflection`).**  For `0 ≤ e < b ≤ ν ≤ C` and the
coefficient bound `m/C ≤ (r-1)/b + (n-1)/ν`, the reflected positive part dominates the negative one:
`((C+e)/(C-e))^m ≤ ((b+e)/(b-e))^{r-1} · ((ν+e)/(ν-e))^{n-1}`.
Proof: with `G(t) = (r-1)(log(b+t)-log(b-t)) + (n-1)(...) - m(...)`, `G(0)=0` and `G'(t) ≥ 0`
(pointwise, `recip_sum_lower` + the coefficient bound), so `G(e) ≥ 0` by the FTC; exponentiate. -/
theorem right_condition {m r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) {b ν C e : ℝ}
    (hb : 0 < b) (hbν : b ≤ ν) (hνC : ν ≤ C) (he0 : 0 ≤ e) (heb : e < b)
    (hcoef : (m : ℝ) / C ≤ ((r : ℝ) - 1) / b + ((n : ℝ) - 1) / ν) :
    ((C + e) / (C - e)) ^ m ≤ ((b + e) / (b - e)) ^ (r - 1) * ((ν + e) / (ν - e)) ^ (n - 1) := by
  have hbe : 0 < b - e := by linarith
  have hν : 0 < ν := by linarith
  have hC : 0 < C := by linarith
  set G : ℝ → ℝ := fun t => ((r : ℝ) - 1) * (Real.log (b + t) - Real.log (b - t))
      + ((n : ℝ) - 1) * (Real.log (ν + t) - Real.log (ν - t))
      - (m : ℝ) * (Real.log (C + t) - Real.log (C - t)) with hGdef
  set G' : ℝ → ℝ := fun t => ((r : ℝ) - 1) * (1 / (b + t) + 1 / (b - t))
      + ((n : ℝ) - 1) * (1 / (ν + t) + 1 / (ν - t))
      - (m : ℝ) * (1 / (C + t) + 1 / (C - t)) with hG'def
  -- positivity facts on `[0,e]`
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) e, 0 < b + t ∧ 0 < b - t ∧ 0 < ν + t ∧ 0 < ν - t
      ∧ 0 < C + t ∧ 0 < C - t ∧ 0 < C ^ 2 - t ^ 2 := by
    intro t ht
    obtain ⟨ht0, hte⟩ := ht
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
    nlinarith [hte, heb, hbν, hνC, ht0]
  -- derivative of G
  have hGderiv : ∀ t ∈ Set.uIcc (0 : ℝ) e, HasDerivAt G (G' t) t := by
    intro t ht
    rw [Set.uIcc_of_le he0] at ht
    obtain ⟨hb1, hb2, hν1, hν2, hC1, hC2, _⟩ := hpos t ht
    have hgb := (glog_hasDerivAt hb1 hb2).const_mul ((r : ℝ) - 1)
    have hgν := (glog_hasDerivAt hν1 hν2).const_mul ((n : ℝ) - 1)
    have hgC := (glog_hasDerivAt hC1 hC2).const_mul ((m : ℝ))
    exact (hgb.add hgν).sub hgC
  -- continuity of each `1/(X+t)+1/(X-t)` on `[0,e]`
  have hcontinv : ∀ X : ℝ, 0 < X - e →
      ContinuousOn (fun t => 1 / (X + t) + 1 / (X - t)) (Set.Icc (0 : ℝ) e) := by
    intro X hXe
    refine ContinuousOn.add (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
      (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    · intro t ht; exact ne_of_gt (by obtain ⟨h0, hte⟩ := ht; linarith)
    · intro t ht; exact ne_of_gt (by obtain ⟨h0, hte⟩ := ht; linarith)
  -- integrability of G'
  have hint : IntervalIntegrable G' volume 0 e := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le he0, hG'def]
    exact (((continuousOn_const.mul (hcontinv b hbe)).add
      (continuousOn_const.mul (hcontinv ν (by linarith)))).sub
      (continuousOn_const.mul (hcontinv C (by linarith))))
  -- G' ≥ 0 on [0,e]
  have hG'nonneg : ∀ t ∈ Set.Icc (0 : ℝ) e, 0 ≤ G' t := by
    intro t ht
    obtain ⟨hb1, hb2, hν1, hν2, hC1, hC2, hCt⟩ := hpos t ht
    have hbB := recip_sum_lower hb (le_trans hbν hνC) hb1 hb2 hCt
    have hνB := recip_sum_lower hν hνC hν1 hν2 hCt
    have heqC : 1 / (C + t) + 1 / (C - t) = 2 * C / (C ^ 2 - t ^ 2) := by field_simp; ring
    have hfac : 0 < 2 * C ^ 2 / (C ^ 2 - t ^ 2) := by positivity
    have hr1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
      have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hstep_b := mul_le_mul_of_nonneg_left hbB hr1
    have hstep_ν := mul_le_mul_of_nonneg_left hνB hn1
    have hstep_coef := mul_le_mul_of_nonneg_right hcoef hfac.le
    have eq1 : (((r : ℝ) - 1) / b + ((n : ℝ) - 1) / ν) * (2 * C ^ 2 / (C ^ 2 - t ^ 2))
        = ((r : ℝ) - 1) * (1 / b * (2 * C ^ 2 / (C ^ 2 - t ^ 2)))
          + ((n : ℝ) - 1) * (1 / ν * (2 * C ^ 2 / (C ^ 2 - t ^ 2))) := by ring
    have eq2 : (m : ℝ) / C * (2 * C ^ 2 / (C ^ 2 - t ^ 2)) = (m : ℝ) * (2 * C / (C ^ 2 - t ^ 2)) := by
      field_simp
    simp only [hG'def, heqC]
    linarith [hstep_b, hstep_ν, hstep_coef, eq1, eq2]
  -- assemble: G e ≥ 0 via FTC
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hint
  have hInonneg : 0 ≤ ∫ t in (0 : ℝ)..e, G' t :=
    intervalIntegral.integral_nonneg he0 hG'nonneg
  have hG0 : G 0 = 0 := by rw [hGdef]; simp
  have hGe : 0 ≤ G e := by rw [hftc] at hInonneg; rw [hG0] at hInonneg; linarith
  -- unfold and convert to the product inequality
  have hbe' : 0 < b + e := by linarith
  have hνe : 0 < ν - e := by linarith
  have hνe' : 0 < ν + e := by linarith
  have hCe : 0 < C - e := by linarith
  have hCe' : 0 < C + e := by linarith
  have hrc : (↑(r - 1) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr, Nat.cast_one]
  have hnc : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  have hPf1 : 0 < ((b + e) / (b - e)) ^ (r - 1) := pow_pos (div_pos hbe' hbe) _
  have hPf2 : 0 < ((ν + e) / (ν - e)) ^ (n - 1) := pow_pos (div_pos hνe' hνe) _
  have hQpos : 0 < ((C + e) / (C - e)) ^ m := pow_pos (div_pos hCe' hCe) _
  have hPpos : 0 < ((b + e) / (b - e)) ^ (r - 1) * ((ν + e) / (ν - e)) ^ (n - 1) := mul_pos hPf1 hPf2
  rw [← Real.exp_log hQpos, ← Real.exp_log hPpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (ne_of_gt hPf1) (ne_of_gt hPf2), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_div (ne_of_gt hCe') (ne_of_gt hCe), Real.log_div (ne_of_gt hbe') (ne_of_gt hbe),
    Real.log_div (ne_of_gt hνe') (ne_of_gt hνe), hrc, hnc]
  have hGe' := hGe
  simp only [hGdef] at hGe'
  linarith [hGe']

end OddCycleBound.HighDensity
