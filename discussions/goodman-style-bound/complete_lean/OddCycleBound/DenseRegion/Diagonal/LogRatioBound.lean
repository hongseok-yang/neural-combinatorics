/-
# Dense region (Phase D) — the log-ratio inequality `L(t) < 0` (D6.6d)

This file proves the paper's final calculus lemma (`eq:gamma-Lnegative`, lines 1691–1766): for
`t > 0`,
```
L(t) := 2t·log A(t) + log B(t) − C(t) < 0,
```
where (with `t = j/r`, from the max-ratio `G(c)/G(−d) = A^{2j}·B^r·e^{−rC}`)
```
A(t) = 3t(5+8t) / (2(1+t)(1+4t)),
B(t) = (1+4t)(5+8t) / (3(1+t)),
C(t) = (32t²+25t+2) / (3(1+4t)).
```
`GammaMomentProof.lean` consumes this (via `Gg_cc_le_neg_dd`) to finish `H(b_*) > 0`.

The argument: the two local maxima of `G` are compared through `L`.  `L''` has one sign change
(a quartic), so `L'` is unimodal; `L'(1) > 0 > L'(3/2)` localizes the interior maximum of `L` to
`[1, 3/2]`; concavity tangent bounds (`log 2 < 7/10`, `log 13 < 13/5`) there give a cubic `< 0`;
the tails `t ↓ 0` and `t → ∞` are handled directly.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

open Real
open scoped Topology

namespace OddCycleBound.DenseRegion

/-- `A(t) = 3t(5+8t)/(2(1+t)(1+4t))` (`= c/d`). -/
noncomputable def Aexpr (t : ℝ) : ℝ := 3 * t * (5 + 8 * t) / (2 * (1 + t) * (1 + 4 * t))

/-- `B(t) = (1+4t)(5+8t)/(3(1+t))` (`= (b+c)/(b−d)`). -/
noncomputable def Bexpr (t : ℝ) : ℝ := (1 + 4 * t) * (5 + 8 * t) / (3 * (1 + t))

/-- `C(t) = (32t²+25t+2)/(3(1+4t))` (`= (c+d)/r`). -/
noncomputable def Cexpr (t : ℝ) : ℝ := (32 * t ^ 2 + 25 * t + 2) / (3 * (1 + 4 * t))

/-- `L(t) = 2t·log A(t) + log B(t) − C(t)`. -/
noncomputable def Lexpr (t : ℝ) : ℝ := 2 * t * Real.log (Aexpr t) + Real.log (Bexpr t) - Cexpr t

lemma Aexpr_pos {t : ℝ} (ht : 0 < t) : 0 < Aexpr t := by unfold Aexpr; positivity

lemma Bexpr_pos {t : ℝ} (ht : 0 < t) : 0 < Bexpr t := by unfold Bexpr; positivity

/-- `C'(t) = (128t²+64t+17)/(3(1+4t)²)`. -/
lemma Cexpr_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt Cexpr ((128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) t := by
  have hden0 : (3 : ℝ) * (1 + 4 * t) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun s : ℝ => 32 * s ^ 2 + 25 * s + 2) (32 * (2 * t) + 25) t := by
    simpa using (((hasDerivAt_pow 2 t).const_mul (32 : ℝ)).add
      ((hasDerivAt_id t).const_mul (25 : ℝ))).add_const (2 : ℝ)
  have hden : HasDerivAt (fun s : ℝ => 3 * (1 + 4 * s)) (3 * 4) t := by
    simpa using (((hasDerivAt_id t).const_mul (4 : ℝ)).const_add (1 : ℝ)).const_mul (3 : ℝ)
  have hquot := hnum.div hden hden0
  have hkey : (32 * (2 * t) + 25) * (3 * (1 + 4 * t)) - (32 * t ^ 2 + 25 * t + 2) * (3 * 4)
      = 3 * (128 * t ^ 2 + 64 * t + 17) := by ring
  have hkey2 : (3 * (1 + 4 * t)) ^ 2 = 3 * (3 * (1 + 4 * t) ^ 2) := by ring
  rw [hkey, hkey2, mul_div_mul_left _ _ (by norm_num : (3 : ℝ) ≠ 0)] at hquot
  exact hquot

/-- `log A(t)` split into elementary logs. -/
lemma Aexpr_log {t : ℝ} (ht : 0 < t) :
    Real.log (Aexpr t) = Real.log 3 + Real.log t + Real.log (5 + 8 * t)
      - Real.log 2 - Real.log (1 + t) - Real.log (1 + 4 * t) := by
  unfold Aexpr
  rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  ring

/-- `log B(t)` split into elementary logs. -/
lemma Bexpr_log {t : ℝ} (ht : 0 < t) :
    Real.log (Bexpr t) = Real.log (1 + 4 * t) + Real.log (5 + 8 * t)
      - Real.log 3 - Real.log (1 + t) := by
  unfold Bexpr
  rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  ring

/-- **`L'(t)`** in split-log form (`eq:gamma-Lprime`, before rational simplification of the
non-log part). -/
lemma Lexpr_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt Lexpr
      (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (1 / t + 8 / (5 + 8 * t) - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) t := by
  have h58 : (5 : ℝ) + 8 * t ≠ 0 := by positivity
  have h1t : (1 : ℝ) + t ≠ 0 := by positivity
  have h14 : (1 : ℝ) + 4 * t ≠ 0 := by positivity
  have dlogt : HasDerivAt Real.log (1 / t) t := by
    rw [one_div]; exact Real.hasDerivAt_log (ne_of_gt ht)
  have dlog58 : HasDerivAt (fun s => Real.log (5 + 8 * s)) (8 / (5 + 8 * t)) t :=
    (show HasDerivAt (fun s : ℝ => 5 + 8 * s) 8 t by
      simpa using ((hasDerivAt_id t).const_mul 8).const_add 5).log h58
  have dlog1t : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t := by
    simpa using (show HasDerivAt (fun s : ℝ => 1 + s) 1 t by
      simpa using (hasDerivAt_id t).const_add 1).log h1t
  have dlog14 : HasDerivAt (fun s => Real.log (1 + 4 * s)) (4 / (1 + 4 * t)) t :=
    (show HasDerivAt (fun s : ℝ => 1 + 4 * s) 4 t by
      simpa using ((hasDerivAt_id t).const_mul 4).const_add 1).log h14
  have dsumA : HasDerivAt (fun s => Real.log 3 + Real.log s + Real.log (5 + 8 * s) - Real.log 2
        - Real.log (1 + s) - Real.log (1 + 4 * s))
      (0 + 1 / t + 8 / (5 + 8 * t) - 0 - 1 / (1 + t) - 4 / (1 + 4 * t)) t :=
    ((((((hasDerivAt_const t (Real.log 3)).add dlogt).add dlog58).sub
      (hasDerivAt_const t (Real.log 2))).sub dlog1t).sub dlog14)
  have d2t : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
  have dsumB : HasDerivAt (fun s => Real.log (1 + 4 * s) + Real.log (5 + 8 * s) - Real.log 3
        - Real.log (1 + s))
      (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 0 - 1 / (1 + t)) t :=
    (((dlog14.add dlog58).sub (hasDerivAt_const t (Real.log 3))).sub dlog1t)
  have hcomb := ((d2t.mul dsumA).add dsumB).sub (Cexpr_hasDerivAt ht)
  have hLraw : HasDerivAt Lexpr
      (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (0 + 1 / t + 8 / (5 + 8 * t) - 0 - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 0 - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) t := by
    apply hcomb.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [Set.mem_Ioi] at hs
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    unfold Lexpr; rw [Aexpr_log hs, Bexpr_log hs]
  have key : (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (0 + 1 / t + 8 / (5 + 8 * t) - 0 - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 0 - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2))
      = (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (1 / t + 8 / (5 + 8 * t) - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) := by ring
  rw [← key]; exact hLraw

/-- The non-log part of `L'` in compact rational form (`eq:gamma-Lprime`):
`R(t) = −(32t²+16t−7)(32t²+25t+2)/(3(1+t)(1+4t)²(5+8t))`. -/
lemma Lexpr_deriv_ratpart {t : ℝ} (ht : 0 < t) :
    2 * t * (1 / t + 8 / (5 + 8 * t) - 1 / (1 + t) - 4 / (1 + 4 * t))
      + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 1 / (1 + t))
      - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)
    = -((32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2))
        / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t)) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h58 : (5 : ℝ) + 8 * t ≠ 0 := by positivity
  have h1t : (1 : ℝ) + t ≠ 0 := by positivity
  have h14 : (1 : ℝ) + 4 * t ≠ 0 := by positivity
  field_simp
  ring

/-- **`L'(t) = 2·log A(t) + R(t)`** (`eq:gamma-Lprime`, compact form). -/
lemma Lexpr_hasDerivAt' {t : ℝ} (ht : 0 < t) :
    HasDerivAt Lexpr (2 * Real.log (Aexpr t)
      - ((32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2))
          / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t))) t := by
  have heq : 2 * Real.log (Aexpr t)
        - ((32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2))
            / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t))
      = 2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (1 / t + 8 / (5 + 8 * t) - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2) := by
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h58 : (5 : ℝ) + 8 * t ≠ 0 := by positivity
    have h1t : (1 : ℝ) + t ≠ 0 := by positivity
    have h14 : (1 : ℝ) + 4 * t ≠ 0 := by positivity
    rw [Aexpr_log ht]; field_simp; ring
  rw [heq]; exact Lexpr_hasDerivAt ht

/-- **Padé lower bound**: `log x ≥ 2(x−1)/(x+1)` for `x ≥ 1` (`eq:gamma-Lprime`'s `L'(1)` step).
`f(x) = log x − 2(x−1)/(x+1)` has `f(1)=0` and `f'(x) = (x−1)²/(x(x+1)²) ≥ 0`. -/
lemma log_ge_padé {x : ℝ} (hx : 1 ≤ x) : 2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have hderiv : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun y => Real.log y - 2 * (y - 1) / (y + 1)) (1 / s - 4 / (s + 1) ^ 2) s := by
    intro s hs
    have hs1 : s + 1 ≠ 0 := by positivity
    have hl : HasDerivAt Real.log (1 / s) s := by rw [one_div]; exact Real.hasDerivAt_log (ne_of_gt hs)
    have hr : HasDerivAt (fun y => 2 * (y - 1) / (y + 1)) (4 / (s + 1) ^ 2) s := by
      have hn : HasDerivAt (fun y : ℝ => 2 * (y - 1)) 2 s := by
        simpa using ((hasDerivAt_id s).sub_const 1).const_mul 2
      have hd : HasDerivAt (fun y : ℝ => y + 1) 1 s := by simpa using (hasDerivAt_id s).add_const 1
      have hq := hn.div hd hs1
      have hkey : (2 * (s + 1) - 2 * (s - 1) * 1) / (s + 1) ^ 2 = 4 / (s + 1) ^ 2 := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; ring
      rw [hkey] at hq; exact hq
    exact hl.sub hr
  have hmono : MonotoneOn (fun y => Real.log y - 2 * (y - 1) / (y + 1)) (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun y hy => (hderiv y (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hy))).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hderiv y (lt_trans one_pos (Set.mem_Ioi.mp hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici, Set.mem_Ioi] at hy
      have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
      rw [(hderiv y hy0).deriv]
      have heq : 1 / y - 4 / (y + 1) ^ 2 = (y - 1) ^ 2 / (y * (y + 1) ^ 2) := by
        have : y ≠ 0 := ne_of_gt hy0
        have : y + 1 ≠ 0 := by positivity
        field_simp; ring
      rw [heq]; positivity
  have h1 := hmono Set.left_mem_Ici (Set.mem_Ici.mpr hx) hx
  simp only [Real.log_one] at h1
  norm_num at h1
  linarith

/-- `L'(1) > 0` (`eq:gamma-Lprime`): `2 log(39/20) ≥ 76/59 > 2419/1950 = −R(1)`. -/
lemma Lprime_one_pos : 0 < deriv Lexpr 1 := by
  rw [(Lexpr_hasDerivAt' (by norm_num : (0 : ℝ) < 1)).deriv]
  have hA : Aexpr 1 = 39 / 20 := by unfold Aexpr; norm_num
  have hlog : (76 : ℝ) / 59 ≤ 2 * Real.log (39 / 20) := by
    have h := log_ge_padé (show (1 : ℝ) ≤ 39 / 20 by norm_num)
    have he : (2 : ℝ) * (39 / 20 - 1) / (39 / 20 + 1) = 38 / 59 := by norm_num
    rw [he] at h; linarith
  rw [hA]; norm_num; linarith [hlog]

/-- `L'(3/2) < 0` (`eq:gamma-Lprime`): `2 log(153/70) ≤ 111/70 < 19847/12495 = −R(3/2)`. -/
lemma Lprime_threehalf_neg : deriv Lexpr (3 / 2) < 0 := by
  rw [(Lexpr_hasDerivAt' (by norm_num : (0 : ℝ) < 3 / 2)).deriv]
  have hA : Aexpr (3 / 2) = 153 / 70 := by unfold Aexpr; norm_num
  have hlog : 2 * Real.log (153 / 70) ≤ 111 / 70 := by
    have hsplit : Real.log (153 / 70) = Real.log 2 + Real.log (153 / 140) := by
      rw [← Real.log_mul (by norm_num) (by norm_num), show (2 : ℝ) * (153 / 140) = 153 / 70 by norm_num]
    have hle : Real.log (153 / 140) ≤ 13 / 140 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 153 / 140 by norm_num); linarith
    have h2 := Real.log_two_lt_d9
    rw [hsplit]; nlinarith [hle, h2]
  rw [hA]; norm_num; linarith [hlog]

/-- `L'(t) < 0` for `t ≥ 3/2`: via `2 log A ≤ 7/5 + (A−2)` and a polynomial inequality
`−1024t⁴−736t³+2244t²+1601t+50 < 0` (root ≈ 1.48). -/
lemma Lprime_neg_of_ge_threehalf {t : ℝ} (ht : 3 / 2 ≤ t) : deriv Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  rw [(Lexpr_hasDerivAt' ht0).deriv]
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have htan : 2 * Real.log (Aexpr t) ≤ 7 / 5 + (Aexpr t - 2) := by
    have hsplit : Real.log (Aexpr t) = Real.log 2 + Real.log (Aexpr t / 2) := by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hA0 (by norm_num))),
          show (2 : ℝ) * (Aexpr t / 2) = Aexpr t from by ring]
    have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Aexpr t / 2 from div_pos hA0 (by norm_num))
    have h2 := Real.log_two_lt_d9
    rw [hsplit]; nlinarith [hle, h2]
  have hrat : 7 / 5 + (Aexpr t - 2)
      - (32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2)
          / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t)) < 0 := by
    have heq : 7 / 5 + (Aexpr t - 2)
        - (32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2)
            / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t))
        = (-1024 * t ^ 4 - 736 * t ^ 3 + 2244 * t ^ 2 + 1601 * t + 50)
            / (30 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t)) := by
      unfold Aexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
    rw [heq]
    apply div_neg_of_neg_of_pos _
      (mul_pos (mul_pos (mul_pos (by norm_num) h1t) (pow_pos h14 2)) h58)
    nlinarith [ht, mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg ht0.le ht0.le),
      mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg t), sq_nonneg (t - 3 / 2), mul_pos ht0 ht0,
      mul_pos (mul_pos ht0 ht0) ht0]
  linarith [htan, hrat]

/-- `log 13 < 13/5`: `log 13 = 4·log 2 + log(13/16) ≤ 4·log 2 − 3/16 < 13/5`. -/
lemma log_thirteen_lt : Real.log 13 < 13 / 5 := by
  have h13 : Real.log 13 = 4 * Real.log 2 + Real.log (13 / 16) := by
    rw [show (13 : ℝ) = 2 ^ 4 * (13 / 16) from by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hle : Real.log (13 / 16) ≤ 13 / 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 := Real.log_two_lt_d9
  rw [h13]; nlinarith [hle, h2]

/-- **`L(t) < 0` on `[1, 3/2]`** (`eq:gamma-L-rational`): tangent bounds `log A ≤ log2+(A−2)/2`,
`log B ≤ log13+(B−13)/13` with `log2<7/10`, `log13<13/5` give `L < 3(96t³−191t²−16t+46)/(130(1+t)(1+4t))`,
and the cubic is `< 0` there. -/
lemma Lexpr_neg_on_Icc {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 3 / 2) : Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Real.log 2 + (Aexpr t - 2) / 2 := by
    rw [show Real.log (Aexpr t) = Real.log 2 + Real.log (Aexpr t / 2) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hA0 (by norm_num))),
          show (2 : ℝ) * (Aexpr t / 2) = Aexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Aexpr t / 2 from div_pos hA0 (by norm_num))]
  have htanB : Real.log (Bexpr t) ≤ Real.log 13 + (Bexpr t - 13) / 13 := by
    rw [show Real.log (Bexpr t) = Real.log 13 + Real.log (Bexpr t / 13) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
          show (13 : ℝ) * (Bexpr t / 13) = Bexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 13 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have h13 := log_thirteen_lt
  have hLbound : Lexpr t
      < 7 * t / 5 + t * (Aexpr t - 2) + (13 / 5 + (Bexpr t - 13) / 13) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Real.log 2 + (Aexpr t - 2) / 2 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB, h13,
      mul_pos ht0 (show (0 : ℝ) < 7 / 10 - Real.log 2 by linarith)]
  have hcubic : 7 * t / 5 + t * (Aexpr t - 2) + (13 / 5 + (Bexpr t - 13) / 13) - Cexpr t
      = 3 * (96 * t ^ 3 - 191 * t ^ 2 - 16 * t + 46) / (130 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : 3 * (96 * t ^ 3 - 191 * t ^ 2 - 16 * t + 46) / (130 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht1, ht2, mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2), sq_nonneg (t - 1),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2)) ht0.le]
  linarith [hLbound, hcneg]

/-- `L(t) < 0` for `t ≥ 3/2`: `L` is antitone there (`L' < 0`) and `L(3/2) < 0`. -/
lemma Lexpr_neg_of_ge_threehalf {t : ℝ} (ht : 3 / 2 ≤ t) : Lexpr t < 0 := by
  have hanti : AntitoneOn Lexpr (Set.Ici (3 / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun s hs => (Lexpr_hasDerivAt (by have := Set.mem_Ici.mp hs; linarith)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici, Set.mem_Ioi] at hs
      exact (Lexpr_hasDerivAt (by linarith)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici, Set.mem_Ioi] at hs
      exact (Lprime_neg_of_ge_threehalf (le_of_lt hs)).le
  exact lt_of_le_of_lt (hanti Set.left_mem_Ici (Set.mem_Ici.mpr ht) ht)
    (Lexpr_neg_on_Icc (by norm_num) (le_refl _))

/-- `L(t) < 0` on `[1/2, 1]`: tangent-at-2 (`A`), tangent-at-8 (`B`) → `512t³−492t²−252t+77 < 0`. -/
lemma Lexpr_neg_on_half_one {t : ℝ} (ht1 : 1 / 2 ≤ t) (ht2 : t ≤ 1) : Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Real.log 2 + (Aexpr t - 2) / 2 := by
    rw [show Real.log (Aexpr t) = Real.log 2 + Real.log (Aexpr t / 2) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hA0 (by norm_num))),
          show (2 : ℝ) * (Aexpr t / 2) = Aexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Aexpr t / 2 from div_pos hA0 (by norm_num))]
  have htanB : Real.log (Bexpr t) ≤ 3 * Real.log 2 + (Bexpr t - 8) / 8 := by
    rw [show Real.log (Bexpr t) = Real.log 8 + Real.log (Bexpr t / 8) from by
          rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
              show (8 : ℝ) * (Bexpr t / 8) = Bexpr t from by ring],
        show Real.log 8 = 3 * Real.log 2 from by
          rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]; push_cast; ring]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 8 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have hLbound : Lexpr t < 7 * t / 5 + t * (Aexpr t - 2) + (21 / 10 + (Bexpr t - 8) / 8) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Real.log 2 + (Aexpr t - 2) / 2 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB,
      mul_pos ht0 (show (0 : ℝ) < 7 / 10 - Real.log 2 by linarith), h2]
  have hcubic : 7 * t / 5 + t * (Aexpr t - 2) + (21 / 10 + (Bexpr t - 8) / 8) - Cexpr t
      = (512 * t ^ 3 - 492 * t ^ 2 - 252 * t + 77) / (120 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : (512 * t ^ 3 - 492 * t ^ 2 - 252 * t + 77) / (120 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht1, ht2, mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2), sq_nonneg (t - 1),
      sq_nonneg (2 * t - 1)]
  linarith [hLbound, hcneg]

/-- `L(t) < 0` on `[1/4, 1/2]`: `log A ≤ A−1`, tangent-at-4 (`B`) → `960t³−24t²−300t+9 < 0`. -/
lemma Lexpr_neg_on_quarter_half {t : ℝ} (ht1 : 1 / 4 ≤ t) (ht2 : t ≤ 1 / 2) : Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Aexpr t - 1 := Real.log_le_sub_one_of_pos hA0
  have htanB : Real.log (Bexpr t) ≤ 2 * Real.log 2 + (Bexpr t - 4) / 4 := by
    rw [show Real.log (Bexpr t) = Real.log 4 + Real.log (Bexpr t / 4) from by
          rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
              show (4 : ℝ) * (Bexpr t / 4) = Bexpr t from by ring],
        show Real.log 4 = 2 * Real.log 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; push_cast; ring]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 4 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have hLbound : Lexpr t < 2 * t * (Aexpr t - 1) + (7 / 5 + (Bexpr t - 4) / 4) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Aexpr t - 1 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB, h2]
  have hcubic : 2 * t * (Aexpr t - 1) + (7 / 5 + (Bexpr t - 4) / 4) - Cexpr t
      = (960 * t ^ 3 - 24 * t ^ 2 - 300 * t + 9) / (60 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : (960 * t ^ 3 - 24 * t ^ 2 - 300 * t + 9) / (60 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht1, ht2, mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2), sq_nonneg (4 * t - 1),
      sq_nonneg (2 * t - 1)]
  linarith [hLbound, hcneg]

/-- `L(t) < 0` on `(0, 1/4]`: `log A ≤ A−1`, tangent-at-2 (`B`) → `800t³+264t²−135t−4 < 0`. -/
lemma Lexpr_neg_on_zero_quarter {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 1 / 4) : Lexpr t < 0 := by
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Aexpr t - 1 := Real.log_le_sub_one_of_pos hA0
  have htanB : Real.log (Bexpr t) ≤ Real.log 2 + (Bexpr t - 2) / 2 := by
    rw [show Real.log (Bexpr t) = Real.log 2 + Real.log (Bexpr t / 2) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
          show (2 : ℝ) * (Bexpr t / 2) = Bexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 2 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have hLbound : Lexpr t < 2 * t * (Aexpr t - 1) + (7 / 10 + (Bexpr t - 2) / 2) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Aexpr t - 1 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB, h2]
  have hcubic : 2 * t * (Aexpr t - 1) + (7 / 10 + (Bexpr t - 2) / 2) - Cexpr t
      = (800 * t ^ 3 + 264 * t ^ 2 - 135 * t - 4) / (30 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : (800 * t ^ 3 + 264 * t ^ 2 - 135 * t - 4) / (30 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht0, ht2, mul_nonneg (sub_nonneg.mpr ht2) (mul_nonneg ht0.le ht0.le),
      mul_nonneg (sub_nonneg.mpr ht2) ht0.le]
  linarith [hLbound, hcneg]

/-- **`L(t) < 0` for every `t > 0`** (`lem:gamma-L-negative`): assembled from the five regions
`(0,1/4]`, `[1/4,1/2]`, `[1/2,1]`, `[1,3/2]`, `[3/2,∞)`. -/
theorem Lexpr_neg {t : ℝ} (ht : 0 < t) : Lexpr t < 0 := by
  rcases le_total t (1 / 4) with h | h
  · exact Lexpr_neg_on_zero_quarter ht h
  rcases le_total t (1 / 2) with h2 | h2
  · exact Lexpr_neg_on_quarter_half h h2
  rcases le_total t 1 with h3 | h3
  · exact Lexpr_neg_on_half_one h2 h3
  rcases le_total t (3 / 2) with h4 | h4
  · exact Lexpr_neg_on_Icc h3 h4
  · exact Lexpr_neg_of_ge_threehalf h4

end OddCycleBound.DenseRegion
