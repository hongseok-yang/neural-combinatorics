import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv

/-!
# The one-variable growth lemma `lem:J-growth` (paper §9, lines 3035–3277)

For odd `N ≥ 9`, `0 ≤ x < 1`, `1 − x ≥ 2x²/N`:
```
J_N(x) := (N+2)/N · (1−x)² (1+x³) · (N(1+x²)/(N−x²))^{3N/4−1} ≥ 1.
```
This is the single hardest analytic lemma of the intermediate region.  It is *not* a computational
certificate — the varying exponent `3N/4−1` makes it genuinely analytic — so it is exactly the kind of
proof the paper (and this formalization's end goal) wants.

The proof follows the manuscript: reduce `J_N ≥ 1` to `log J_N ≥ 0`, bound `log J_N ≥ L_N(x)` by
elementary logarithm inequalities, and then show `L_N > 0` region by region (`[0,1/4]` via a quadratic
discriminant, `[1/4,2/5]` via `∂_N ≥ 0` then `L_9`), and finally `Step 2` (`2/5 ≤ x ≤ β_N`) via `K_N`.

This first increment establishes the **elementary logarithm bounds** used to build `L_N`.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion

open Real

/-- `log(1+t) ≥ t − t²/2` for all `t ≥ 0` (via monotonicity: the difference has derivative
`t²/(1+t) ≥ 0`). -/
theorem log_one_add_ge_sub_half_sq {t : ℝ} (ht : 0 ≤ t) : t - t ^ 2 / 2 ≤ Real.log (1 + t) := by
  have hHD : ∀ x : ℝ, 0 ≤ x →
      HasDerivAt (fun s => Real.log (1 + s) - (s - s ^ 2 / 2)) (1 / (1 + x) - (1 - x)) x := by
    intro x hx
    have h1x : (1 : ℝ) + x ≠ 0 := by positivity
    have hlog : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + x)) x := by
      have := ((hasDerivAt_id x).const_add (1 : ℝ)).log h1x
      simpa [one_div] using this
    have hpoly : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - x) x := by
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) x x := by
        simpa using (hasDerivAt_pow 2 x).div_const 2
      exact (hasDerivAt_id x).sub h2
    exact hlog.sub hpoly
  have hmono : MonotoneOn (fun s => Real.log (1 + s) - (s - s ^ 2 / 2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x hx => (hHD x hx).continuousAt.continuousWithinAt)
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact (hHD x hx.le).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hHD x hx.le).deriv]
      have h1x : (0 : ℝ) < 1 + x := by linarith
      have : 1 / (1 + x) - (1 - x) = x ^ 2 / (1 + x) := by field_simp; ring
      rw [this]; positivity
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  norm_num [Real.log_one] at h
  linarith [h]

/-- `log(1−s) ≤ −s` for `s < 1` (from `log y ≤ y − 1`). -/
theorem log_one_sub_le_neg {s : ℝ} (hs : s < 1) : Real.log (1 - s) ≤ -s := by
  have h : Real.log (1 - s) ≤ (1 - s) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  linarith [h]

/-- `2 log(1−x) ≥ −2x − x² − (2/3)x³ − x⁴/(1−x)` for `0 ≤ x < 1` (via monotonicity: the difference has
derivative `x³(2−x)/(1−x)² ≥ 0`). -/
theorem two_log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -2 * x - x ^ 2 - 2 / 3 * x ^ 3 - x ^ 4 / (1 - x) ≤ 2 * Real.log (1 - x) := by
  -- work with `ψ(s) = 2 log(1−s) + 2s + s² + (2/3)s³ + s⁴/(1−s)` on `[0, x]`
  have hHD : ∀ s : ℝ, 0 ≤ s → s < 1 →
      HasDerivAt (fun t => 2 * Real.log (1 - t) + 2 * t + t ^ 2 + 2 / 3 * t ^ 3 + t ^ 4 / (1 - t))
        (2 * (-1 / (1 - s)) + 2 + 2 * s + 2 * s ^ 2
          + (4 * s ^ 3 * (1 - s) - s ^ 4 * (-1)) / (1 - s) ^ 2) s := by
    intro s hs0 hs1
    have h1s : (1 : ℝ) - s ≠ 0 := by linarith
    have hin : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
    have hlog : HasDerivAt (fun t => 2 * Real.log (1 - t)) (2 * (-1 / (1 - s))) s :=
      (hin.log h1s).const_mul (2 : ℝ)
    have h2t : HasDerivAt (fun t : ℝ => 2 * t) 2 s := by simpa using (hasDerivAt_id s).const_mul 2
    have ht2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have ht3 : HasDerivAt (fun t : ℝ => 2 / 3 * t ^ 3) (2 * s ^ 2) s := by
      have hv : (2 : ℝ) * s ^ 2 = 2 / 3 * (3 * s ^ 2) := by ring
      rw [hv]
      simpa using (hasDerivAt_pow 3 s).const_mul (2 / 3 : ℝ)
    have hnum : HasDerivAt (fun t : ℝ => t ^ 4) (4 * s ^ 3) s := by simpa using hasDerivAt_pow 4 s
    have hfrac : HasDerivAt (fun t : ℝ => t ^ 4 / (1 - t))
        ((4 * s ^ 3 * (1 - s) - s ^ 4 * (-1)) / (1 - s) ^ 2) s := hnum.div hin h1s
    exact (((hlog.add h2t).add ht2).add ht3).add hfrac
  have hmono : MonotoneOn
      (fun t => 2 * Real.log (1 - t) + 2 * t + t ^ 2 + 2 / 3 * t ^ 3 + t ^ 4 / (1 - t))
      (Set.Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      (fun s hs => (hHD s hs.1 hs.2).continuousAt.continuousWithinAt)
    · intro s hs
      rw [interior_Ico, Set.mem_Ioo] at hs
      exact (hHD s hs.1.le hs.2).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ico, Set.mem_Ioo] at hs
      rw [(hHD s hs.1.le hs.2).deriv]
      have h1s : (0 : ℝ) < 1 - s := by linarith [hs.2]
      have hexpand : 2 * (-1 / (1 - s)) + 2 + 2 * s + 2 * s ^ 2
          + (4 * s ^ 3 * (1 - s) - s ^ 4 * (-1)) / (1 - s) ^ 2
          = s ^ 3 * (2 - s) / (1 - s) ^ 2 := by field_simp; ring
      rw [hexpand]
      exact div_nonneg (mul_nonneg (pow_nonneg hs.1.le 3) (by linarith [hs.2])) (sq_nonneg _)
  have hmem0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have hmemx : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have h := hmono hmem0 hmemx hx0
  norm_num [Real.log_one] at h
  linarith [h]

/-- Paper `eq:log-shape-bound` (line 3061): `2 log(1−x) + log(1+x³) ≥ −2x − x² − x⁴/(1−x) − x⁶/2`. -/
theorem log_shape_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -2 * x - x ^ 2 - x ^ 4 / (1 - x) - x ^ 6 / 2
      ≤ 2 * Real.log (1 - x) + Real.log (1 + x ^ 3) := by
  have hB := two_log_one_sub_ge hx0 hx1
  have hA : x ^ 3 - (x ^ 3) ^ 2 / 2 ≤ Real.log (1 + x ^ 3) :=
    log_one_add_ge_sub_half_sq (by positivity)
  have hx3 : (0 : ℝ) ≤ 2 / 3 * x ^ 3 := by positivity
  have : (x ^ 3) ^ 2 = x ^ 6 := by ring
  rw [this] at hA
  linarith [hB, hA, hx3]

/-! ### The master lower bound `log J_N ≥ L_N` (paper eq:L-N-def, line 3066) -/

/-- The paper's lower envelope `L_N(x)` (paper `eq:L-N-def`, line 3066), written as the exact sum of the
three logarithm lower bounds, so the master estimate `log J_N ≥ L_N` becomes a one-line `linarith`.
Algebraically identical to the manuscript's
`2/N − 2/N² − 2x + [A(1+1/N)−1]x² − (A/2)x⁴ − x⁴/(1−x) − x⁶/2` with `A = 3N/4−1`. -/
def LN (N x : ℝ) : ℝ :=
  (2 / N - 2 / N ^ 2) + (-2 * x - x ^ 2 - x ^ 4 / (1 - x) - x ^ 6 / 2)
    + (3 * N / 4 - 1) * (x ^ 2 - x ^ 4 / 2 + x ^ 2 / N)

/-- **Paper Step 1 master estimate (line 3066):** `log J_N(x) ≥ L_N(x)`, in the form
`L_N ≤ log((N+2)/N) + (2 log(1−x) + log(1+x³)) + (3N/4−1)·log(N(1+x²)/(N−x²))`. -/
theorem logJ_ge_LN {N : ℝ} (hN : 9 ≤ N) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    LN N x ≤ Real.log ((N + 2) / N) + (2 * Real.log (1 - x) + Real.log (1 + x ^ 3))
      + (3 * N / 4 - 1) * Real.log (N * (1 + x ^ 2) / (N - x ^ 2)) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hx2lt1 : x ^ 2 < 1 := by nlinarith [hx0, hx1]
  have hNx2 : (0 : ℝ) < N - x ^ 2 := by nlinarith [hx2lt1, hN]
  have hxN : x ^ 2 / N < 1 := by rw [div_lt_one hNpos]; nlinarith [hx2lt1, hN]
  have hA : (0 : ℝ) ≤ 3 * N / 4 - 1 := by linarith
  have hb0 : 2 / N - 2 / N ^ 2 ≤ Real.log ((N + 2) / N) := by
    have h := log_one_add_ge_sub_half_sq (t := 2 / N) (by positivity)
    have he : (N + 2) / N = 1 + 2 / N := by field_simp
    have hsq : 2 / N - (2 / N) ^ 2 / 2 = 2 / N - 2 / N ^ 2 := by field_simp
    rw [he]; linarith [hsq ▸ h]
  have hb3 : x ^ 2 - x ^ 4 / 2 ≤ Real.log (1 + x ^ 2) := by
    have h := log_one_add_ge_sub_half_sq (t := x ^ 2) (by positivity)
    have hsq : (x ^ 2) ^ 2 / 2 = x ^ 4 / 2 := by ring
    linarith [hsq ▸ h]
  have hb4 : Real.log (1 - x ^ 2 / N) ≤ -(x ^ 2 / N) := log_one_sub_le_neg hxN
  have hshape := log_shape_bound hx0 hx1
  have hbase_eq : Real.log (N * (1 + x ^ 2) / (N - x ^ 2))
      = Real.log (1 + x ^ 2) - Real.log (1 - x ^ 2 / N) := by
    have e1 : (1 : ℝ) - x ^ 2 / N = (N - x ^ 2) / N := by field_simp
    rw [Real.log_div (mul_ne_zero hNpos.ne' (by positivity)) hNx2.ne',
      Real.log_mul hNpos.ne' (by positivity), e1, Real.log_div hNx2.ne' hNpos.ne']
    ring
  have hLBbase : x ^ 2 - x ^ 4 / 2 + x ^ 2 / N ≤ Real.log (N * (1 + x ^ 2) / (N - x ^ 2)) := by
    rw [hbase_eq]; linarith [hb3, hb4]
  have hALB := mul_le_mul_of_nonneg_left hLBbase hA
  unfold LN
  linarith [hb0, hshape, hALB]

/-! ### Step 1: `L_N > 0` on `[0, 2/5]` (paper lines 3082–3149) -/

/-- The cleared polynomial `1536 N² (1−x) · L_N(x)`; positivity of `L_N` is positivity of this
(both `1/N`, `1/N²` and `1/(1−x)` clear). -/
private def Rpoly (N x : ℝ) : ℝ :=
  576 * N ^ 3 * x ^ 5 - 576 * N ^ 3 * x ^ 4 - 1152 * N ^ 3 * x ^ 3 + 1152 * N ^ 3 * x ^ 2
    + 768 * N ^ 2 * x ^ 7 - 768 * N ^ 2 * x ^ 6 - 768 * N ^ 2 * x ^ 5 - 768 * N ^ 2 * x ^ 4
    + 1920 * N ^ 2 * x ^ 3 + 1152 * N ^ 2 * x ^ 2 - 3072 * N ^ 2 * x + 1536 * N * x ^ 3
    - 1536 * N * x ^ 2 - 3072 * N * x + 3072 * N + 3072 * x - 3072

private theorem LN_eq_Rpoly {N x : ℝ} (hN : (0:ℝ) < N) (hx : x < 1) :
    1536 * N ^ 2 * (1 - x) * LN N x = Rpoly N x := by
  have h1 : N ≠ 0 := hN.ne'
  have h2 : (1:ℝ) - x ≠ 0 := by linarith
  unfold LN Rpoly
  field_simp
  ring

private theorem pos_of_Rpoly {N x : ℝ} (hN : (0:ℝ) < N) (hx : x < 1) (hR : 0 < Rpoly N x) :
    0 < LN N x := by
  have hc : 0 < 1536 * N ^ 2 * (1 - x) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hN 2)) (by linarith)
  by_cases h : LN N x ≤ 0
  · exfalso
    have hle : 1536 * N ^ 2 * (1 - x) * LN N x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le h
    rw [LN_eq_Rpoly hN hx] at hle; linarith
  · exact not_le.mp h

/-- Paper Step 1a (lines 3082–3107): `L_N > 0` on `[0,1/4]` via the quadratic
`c_N − 2x + B_N x²` and its positive discriminant `B_N c_N − 1 > 0`. -/
theorem LN_pos_low {N x : ℝ} (hN : 9 ≤ N) (hx0 : 0 ≤ x) (hx14 : x ≤ 1 / 4) : 0 < LN N x := by
  have hNpos : (0:ℝ) < N := by linarith
  have h1x : (0:ℝ) < 1 - x := by linarith
  refine pos_of_Rpoly hNpos (by linarith) ?_
  -- `Q > 0` via the discriminant SOS `4aQ = (2ax − 3072N²)² + 3072N·bracket`
  have hbr : 0 < 1392 * N ^ 3 - 12476 * N ^ 2 + 1868 * N + 6144 := by
    nlinarith [hN, sq_nonneg (N - 9), mul_nonneg (sq_nonneg (N - 9)) (by linarith : (0:ℝ) ≤ N - 9)]
  have hinner : 0 < 1116 * N ^ 2 - 2003 * N - 1536 := by nlinarith [hN, sq_nonneg (N - 9)]
  have ha : 0 < N * (1116 * N ^ 2 - 2003 * N - 1536) := mul_pos hNpos hinner
  have hQ : 0 < 1116 * N ^ 3 * x ^ 2 - 2003 * N ^ 2 * x ^ 2 - 3072 * N ^ 2 * x
      - 1536 * N * x ^ 2 + 3072 * N - 3072 := by
    nlinarith [sq_nonneg (2 * (N * (1116 * N ^ 2 - 2003 * N - 1536)) * x - 3072 * N ^ 2),
      mul_pos hNpos hbr, ha]
  -- `Ea = R − Q(1−x) ≥ 0` via `part1 + part2`, both nonneg on `[0,1/4]`
  have hq : 0 ≤ -192 * x ^ 4 + 144 * x ^ 3 + 228 * x ^ 2 + 249 * x + 83 := by
    nlinarith [hx0, hx14, sq_nonneg x, mul_nonneg hx0 (mul_nonneg hx0 hx0)]
  have hp1 : 0 ≤ 36 * N ^ 3 * x ^ 2 * (1 - x) * (1 - 4 * x) * (4 * x + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg hNpos.le 3)) (sq_nonneg x)) (by linarith)) (by linarith)) (by linarith)
  have hp2 : 0 ≤ N ^ 2 * x ^ 2 * (1 - 4 * x) * (-192 * x ^ 4 + 144 * x ^ 3 + 228 * x ^ 2 + 249 * x + 83) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg N) (sq_nonneg x)) (by linarith)) hq
  unfold Rpoly
  nlinarith [mul_pos hQ h1x, hp1, hp2]

/-- Paper Step 1b (lines 3109–3149): `L_N > 0` on `[1/4,2/5]` via `L_N ≥ L_9` (monotone in `N`)
and `L_9 > 0`.  In cleared form: `R = 1536 N² · (L_9(1−x)) + (1536/81)·(N−9)·Dq` with `L_9(1−x) > 0`
and `Dq = c₂(N−9)² + d₁(N−9) + d₀ ≥ 0`. -/
theorem LN_pos_mid {N x : ℝ} (hN : 9 ≤ N) (hx14 : 1 / 4 ≤ x) (hx25 : x ≤ 2 / 5) : 0 < LN N x := by
  have hNpos : (0:ℝ) < N := by linarith
  have hx1 : x < 1 := by linarith
  have ha0 : (0:ℝ) ≤ x - 1 / 4 := by linarith
  have hb0 : (0:ℝ) ≤ 2 / 5 - x := by linarith
  have hw1 : (0:ℝ) ≤ x ^ 2 - 1 / 16 := by nlinarith [hx14]
  have hw2 : (0:ℝ) ≤ 4 / 25 - x ^ 2 := by nlinarith [hx25, hx14]
  refine pos_of_Rpoly hNpos hx1 ?_
  -- `L_9(x)(1−x) > 0`
  have hR9 : 0 < x ^ 7 / 2 - x ^ 6 / 2 + 23 * x ^ 5 / 8 - 31 * x ^ 4 / 8 - 97 * x ^ 3 / 18
      + 133 * x ^ 2 / 18 - 178 * x / 81 + 16 / 81 := by
    nlinarith [ha0, hb0, pow_nonneg ha0 2, mul_nonneg (pow_nonneg ha0 2) hb0, pow_nonneg hb0 3,
      pow_nonneg ha0 5, mul_nonneg (pow_nonneg ha0 3) (pow_nonneg hb0 2), pow_nonneg ha0 6,
      pow_nonneg ha0 7]
  -- `Dq = c₂(N−9)² + d₁(N−9) + d₀ ≥ 0`
  have hc2 : (0:ℝ) ≤ 243 * x ^ 5 / 8 - 243 * x ^ 4 / 8 - 243 * x ^ 3 / 4 + 243 * x ^ 2 / 4 := by
    have e : 243 * x ^ 5 / 8 - 243 * x ^ 4 / 8 - 243 * x ^ 3 / 4 + 243 * x ^ 2 / 4
        = 243 / 8 * x ^ 2 * ((1 - x) * (2 - x ^ 2)) := by ring
    rw [e]; exact mul_nonneg (by positivity) (mul_nonneg (by linarith) (by nlinarith [hx14, hx25]))
  have hd1 : (0:ℝ) ≤ 2187 * x ^ 5 / 4 - 2187 * x ^ 4 / 4 - 2205 * x ^ 3 / 2 + 2205 * x ^ 2 / 2
      + 16 * x - 16 := by
    have e : 2187 * x ^ 5 / 4 - 2187 * x ^ 4 / 4 - 2205 * x ^ 3 / 2 + 2205 * x ^ 2 / 2 + 16 * x - 16
        = (1 - x) * (-2187 * x ^ 4 / 4 + 2205 * x ^ 2 / 2 - 16) := by ring
    rw [e]; exact mul_nonneg (by linarith) (by nlinarith [mul_nonneg hw1 hw2, hw1, hw2])
  have hd0 : (0:ℝ) ≤ 19683 * x ^ 5 / 8 - 19683 * x ^ 4 / 8 - 20007 * x ^ 3 / 4 + 20007 * x ^ 2 / 4
      + 126 * x - 126 := by
    have e : 19683 * x ^ 5 / 8 - 19683 * x ^ 4 / 8 - 20007 * x ^ 3 / 4 + 20007 * x ^ 2 / 4
        + 126 * x - 126 = (1 - x) * (-19683 * x ^ 4 / 8 + 20007 * x ^ 2 / 4 - 126) := by ring
    rw [e]; exact mul_nonneg (by linarith) (by nlinarith [mul_nonneg hw1 hw2, hw1, hw2])
  have hN9 : (0:ℝ) ≤ N - 9 := by linarith
  have hDq : (0:ℝ) ≤ 243 * N ^ 2 * x ^ 5 / 8 - 243 * N ^ 2 * x ^ 4 / 8 - 243 * N ^ 2 * x ^ 3 / 4
      + 243 * N ^ 2 * x ^ 2 / 4 - 9 * N * x ^ 3 + 9 * N * x ^ 2 + 16 * N * x - 16 * N - 18 * x + 18 := by
    nlinarith [mul_nonneg hc2 (sq_nonneg (N - 9)), mul_nonneg hd1 hN9, hd0]
  have hD : (0:ℝ) ≤ (N - 9) * (243 * N ^ 2 * x ^ 5 / 8 - 243 * N ^ 2 * x ^ 4 / 8
      - 243 * N ^ 2 * x ^ 3 / 4 + 243 * N ^ 2 * x ^ 2 / 4 - 9 * N * x ^ 3 + 9 * N * x ^ 2
      + 16 * N * x - 16 * N - 18 * x + 18) := mul_nonneg hN9 hDq
  unfold Rpoly
  nlinarith [mul_pos (mul_pos (show (0:ℝ) < 1536 by norm_num) (pow_pos hNpos 2)) hR9, hD]

/-- **Paper Step 1 (lines 3082–3149):** `L_N > 0` on `[0,2/5]` for odd `N ≥ 9`. -/
theorem LN_pos {N x : ℝ} (hN : 9 ≤ N) (hx0 : 0 ≤ x) (hx25 : x ≤ 2 / 5) : 0 < LN N x := by
  by_cases h : x ≤ 1 / 4
  · exact LN_pos_low hN hx0 h
  · exact LN_pos_mid hN (not_le.mp h).le hx25

/-! ### Step 2: `K_N ≥ 1` on `[2/5, β_N]` (paper lines 3151–3277) -/

/-- Helper: to bound `c ≤ b^r` (real rpow) with `r·k = m`, raise to the `k`-th power and check the
Nat-power inequality `c^k ≤ b^m`. -/
private theorem rpow_ge_rat {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (r : ℝ) (k m : ℕ) (hk : k ≠ 0)
    (hrk : r * (k : ℝ) = (m : ℝ)) (h : c ^ k ≤ b ^ m) : c ≤ b ^ r := by
  have hck : c = (c ^ k) ^ ((k : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast c k, ← Real.rpow_mul hc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk),
      Real.rpow_one]
  have hbrk : (b ^ m) ^ ((k : ℝ)⁻¹) = b ^ r := by
    rw [← Real.rpow_natCast b m, ← Real.rpow_mul hb.le, ← hrk, mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk), mul_one]
  rw [hck, ← hbrk]
  exact Real.rpow_le_rpow (pow_nonneg hc k) h (by positivity)

/-- Paper `eq:K-N-def` (line 3159): `K_N(x) = (N+2)/N·(1−x)²(1+x³)(1+x²)^{3N/4−1}`. -/
noncomputable def KN (N x : ℝ) : ℝ :=
  (N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3) * (1 + x ^ 2) ^ (3 * N / 4 - 1)

private theorem KN_pos {N x : ℝ} (hN : 0 < N) (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 < KN N x := by
  unfold KN
  have h1 : 0 < (N + 2) / N := div_pos (by linarith) hN
  have h2 : 0 < (1 - x) ^ 2 := pow_pos (by linarith) 2
  have h3 : 0 < 1 + x ^ 3 := by nlinarith [pow_nonneg hx0 3]
  have h4 : 0 < (1 + x ^ 2) ^ (3 * N / 4 - 1) := Real.rpow_pos_of_pos (by positivity) _
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

private theorem log_KN {N x : ℝ} (hN : 0 < N) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (KN N x) = Real.log ((N + 2) / N) + 2 * Real.log (1 - x) + Real.log (1 + x ^ 3)
      + (3 * N / 4 - 1) * Real.log (1 + x ^ 2) := by
  unfold KN
  have h1 : (N + 2) / N ≠ 0 := (div_pos (by linarith) hN).ne'
  have h2 : (1 - x) ^ 2 ≠ 0 := (pow_pos (by linarith) 2).ne'
  have h3 : (1 : ℝ) + x ^ 3 ≠ 0 := (show (0:ℝ) < 1 + x ^ 3 by nlinarith [pow_nonneg hx0 3]).ne'
  have h4 : (1 + x ^ 2) ^ (3 * N / 4 - 1) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero h1 h2) h3) h4, Real.log_mul (mul_ne_zero h1 h2) h3,
    Real.log_mul h1 h2, Real.log_pow, Real.log_rpow (by positivity)]
  push_cast; ring

private theorem one_le_KN_of_log {N x : ℝ} (hpos : 0 < KN N x) (hg : 0 ≤ Real.log (KN N x)) :
    1 ≤ KN N x := by
  have h := Real.exp_le_exp.mpr hg
  rwa [Real.exp_zero, Real.exp_log hpos] at h

/-- Closed form of `K_N` at `x = 2/5`. -/
private theorem KN_two_fifths_eq {M : ℝ} :
    KN M (2 / 5) = (M + 2) / M * (1197 / 3125) * (29 / 25) ^ (3 * M / 4 - 1) := by
  unfold KN
  rw [show (1 - (2:ℝ) / 5) ^ 2 = 9 / 25 by norm_num,
    show (1 + ((2:ℝ) / 5) ^ 3) = 133 / 125 by norm_num,
    show (1 + ((2:ℝ) / 5) ^ 2) = 29 / 25 by norm_num]
  ring

/-- Paper endpoint `x = 2/5` (lines 3187–3212): `K_N(2/5) ≥ 1` for odd `N = 2k+9`, by induction on `k`
(base `K_9(2/5) ≥ 4150531/3906250 > 1` via `(29/25)^{23/4} ≥ 2837/1250`; step via the ratio
`N(N+4)/(N+2)²·(29/25)^{3/2} ≥ 117/121·31/25 > 1`). -/
private theorem KN_two_fifths_ind (k : ℕ) : 1 ≤ KN (2 * (k : ℝ) + 9) (2 / 5) := by
  induction k with
  | zero =>
    rw [show (2 * ((0:ℕ) : ℝ) + 9) = 9 by norm_num, KN_two_fifths_eq,
      show 3 * (9:ℝ) / 4 - 1 = 23 / 4 by norm_num]
    have hr : (2837 / 1250 : ℝ) ≤ (29 / 25) ^ ((23:ℝ) / 4) :=
      rpow_ge_rat (by norm_num) (by norm_num) (23 / 4) 4 23 (by norm_num) (by push_cast; norm_num)
        (by norm_num)
    nlinarith [hr]
  | succ k ih =>
    have hMpos : 0 < 2 * (k : ℝ) + 9 := by positivity
    rw [KN_two_fifths_eq] at ih
    have hcast : (2 * ((k + 1 : ℕ) : ℝ) + 9) = (2 * (k : ℝ) + 9) + 2 := by push_cast; ring
    rw [hcast, KN_two_fifths_eq]
    set M : ℝ := 2 * (k : ℝ) + 9 with hMdef
    have hexp : 3 * (M + 2) / 4 - 1 = (3 * M / 4 - 1) + 3 / 2 := by ring
    rw [hexp, Real.rpow_add (by norm_num)]
    set t : ℝ := (29 / 25 : ℝ) ^ (3 * M / 4 - 1) with htdef
    have htpos : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
    have hs : (31 / 25 : ℝ) ≤ (29 / 25 : ℝ) ^ ((3:ℝ) / 2) :=
      rpow_ge_rat (by norm_num) (by norm_num) (3 / 2) 2 3 (by norm_num) (by push_cast; norm_num)
        (by norm_num)
    set s : ℝ := (29 / 25 : ℝ) ^ ((3:ℝ) / 2) with hsdef
    have hspos : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
    have hMfrac : (117 / 121 : ℝ) ≤ M * (M + 4) / (M + 2) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hMpos]
    have hratio1 : (1 : ℝ) ≤ M * (M + 4) / (M + 2) ^ 2 * s := by
      calc (1 : ℝ) ≤ 117 / 121 * (31 / 25) := by norm_num
        _ ≤ M * (M + 4) / (M + 2) ^ 2 * s := mul_le_mul hMfrac hs (by norm_num) (by positivity)
    have hident : (M + 2 + 2) / (M + 2) * (1197 / 3125) * (t * s)
        = ((M + 2) / M * (1197 / 3125) * t) * (M * (M + 4) / (M + 2) ^ 2 * s) := by
      field_simp; ring
    rw [hident]
    have := mul_le_mul ih hratio1 (by norm_num) (by linarith [ih])
    linarith [this]

/-- Paper endpoint `x = 2/5`: `K_N(2/5) ≥ 1` for odd `N ≥ 9`. -/
theorem KN_two_fifths_ge_one {N : ℝ} (hodd : ∃ k : ℕ, N = 2 * (k : ℝ) + 9) : 1 ≤ KN N (2 / 5) := by
  obtain ⟨k, rfl⟩ := hodd; exact KN_two_fifths_ind k

/-- The uniform lower bound for `K_N` on the domain with `x ≥ 21/25` (paper's `x = β_N` region,
lines 3258–3274), using `(1−x)² ≥ 4x⁴/N²`, `x ≥ 21/25`.  `4·(21/25)⁴ = 777924/390625`. -/
private noncomputable def flb (N : ℝ) : ℝ :=
  (N + 2) / N * (4 * (21 / 25) ^ 4 / N ^ 2) * (159 / 100) * (17 / 10) ^ (3 * N / 4 - 1)

/-- `flb(N) ≥ 1` for odd `N = 2k+9`, by induction (base `flb(9) ≥ 1` via `(17/10)^{23/4} ≥ 21`;
step via ratio `M³(M+4)/(M+2)⁴·(17/10)^{3/2} ≥ 1`, using `(17/10)^{3/2} ≥ 2` and `N⁴−24N²−32N−16 ≥ 0`). -/
private theorem flb_ind (k : ℕ) : 1 ≤ flb (2 * (k : ℝ) + 9) := by
  induction k with
  | zero =>
    unfold flb
    rw [show (2 * ((0:ℕ) : ℝ) + 9) = 9 by norm_num, show 3 * (9:ℝ) / 4 - 1 = 23 / 4 by norm_num]
    have hr : (21 : ℝ) ≤ (17 / 10) ^ ((23:ℝ) / 4) :=
      rpow_ge_rat (by norm_num) (by norm_num) (23 / 4) 4 23 (by norm_num) (by push_cast; norm_num)
        (by norm_num)
    nlinarith [hr]
  | succ k ih =>
    unfold flb at ih ⊢
    have hcast : (2 * ((k + 1 : ℕ) : ℝ) + 9) = (2 * (k : ℝ) + 9) + 2 := by push_cast; ring
    rw [hcast]
    set M : ℝ := 2 * (k : ℝ) + 9 with hMdef
    have hMpos : 0 < M := by rw [hMdef]; positivity
    have hexp : 3 * (M + 2) / 4 - 1 = (3 * M / 4 - 1) + 3 / 2 := by ring
    rw [hexp, Real.rpow_add (by norm_num)]
    set t : ℝ := (17 / 10 : ℝ) ^ (3 * M / 4 - 1) with htdef
    have htpos : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
    have hs : (2 : ℝ) ≤ (17 / 10 : ℝ) ^ ((3:ℝ) / 2) :=
      rpow_ge_rat (by norm_num) (by norm_num) (3 / 2) 2 3 (by norm_num) (by push_cast; norm_num)
        (by norm_num)
    set s : ℝ := (17 / 10 : ℝ) ^ ((3:ℝ) / 2) with hsdef
    have hpoly : (M + 2) ^ 4 ≤ 2 * M ^ 3 * (M + 4) := by nlinarith [hMpos, sq_nonneg (M - 9)]
    have ha : 0 ≤ M ^ 3 * (M + 4) / (M + 2) ^ 4 :=
      div_nonneg (mul_nonneg (pow_nonneg hMpos.le 3) (by linarith)) (by positivity)
    have hratio : (1 : ℝ) ≤ M ^ 3 * (M + 4) / (M + 2) ^ 4 * s := by
      have hfrac : (1 : ℝ) ≤ 2 * M ^ 3 * (M + 4) / (M + 2) ^ 4 := by
        rw [le_div_iff₀ (by positivity)]; linarith [hpoly]
      calc (1 : ℝ) ≤ 2 * M ^ 3 * (M + 4) / (M + 2) ^ 4 := hfrac
        _ = M ^ 3 * (M + 4) / (M + 2) ^ 4 * 2 := by ring
        _ ≤ M ^ 3 * (M + 4) / (M + 2) ^ 4 * s := mul_le_mul_of_nonneg_left hs ha
    have hident : (M + 2 + 2) / (M + 2) * (4 * (21 / 25) ^ 4 / (M + 2) ^ 2) * (159 / 100) * (t * s)
        = ((M + 2) / M * (4 * (21 / 25) ^ 4 / M ^ 2) * (159 / 100) * t)
          * (M ^ 3 * (M + 4) / (M + 2) ^ 4 * s) := by
      field_simp; ring
    rw [hident]
    have := mul_le_mul ih hratio (by norm_num) (by linarith [ih])
    linarith [this]

/-- `flb(N) ≤ K_N(x)` for `x ≥ 21/25` in the domain (`2x²/N ≤ 1−x`), `N ≥ 9`. -/
private theorem KN_ge_flb {N x : ℝ} (hN : 9 ≤ N) (hx : 21 / 25 ≤ x) (hx1 : x < 1)
    (hdom : 2 * x ^ 2 / N ≤ 1 - x) : flb N ≤ KN N x := by
  have hNpos : 0 < N := by linarith
  have hA : 0 ≤ (N + 2) / N := div_nonneg (by linarith) hNpos.le
  have he0 : 0 ≤ 3 * N / 4 - 1 := by linarith
  unfold flb KN
  -- factor bounds
  have hB : 4 * (21 / 25 : ℝ) ^ 4 / N ^ 2 ≤ (1 - x) ^ 2 := by
    have hsq : (2 * x ^ 2 / N) ^ 2 ≤ (1 - x) ^ 2 := pow_le_pow_left₀ (by positivity) hdom 2
    have hstep : 4 * (21 / 25 : ℝ) ^ 4 / N ^ 2 ≤ 4 * x ^ 4 / N ^ 2 := by gcongr
    have heq : 4 * x ^ 4 / N ^ 2 = (2 * x ^ 2 / N) ^ 2 := by field_simp; ring
    calc 4 * (21 / 25 : ℝ) ^ 4 / N ^ 2 ≤ 4 * x ^ 4 / N ^ 2 := hstep
      _ = (2 * x ^ 2 / N) ^ 2 := heq
      _ ≤ (1 - x) ^ 2 := hsq
  have hC : (159 / 100 : ℝ) ≤ 1 + x ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]
  have hD : (17 / 10 : ℝ) ^ (3 * N / 4 - 1) ≤ (1 + x ^ 2) ^ (3 * N / 4 - 1) :=
    Real.rpow_le_rpow (by norm_num) (by nlinarith [sq_nonneg x, hx]) he0
  have hB0 : 0 ≤ (1 - x) ^ 2 := sq_nonneg _
  have hC0 : 0 ≤ 1 + x ^ 3 := by nlinarith [hC]
  have hDc : 0 ≤ (17 / 10 : ℝ) ^ (3 * N / 4 - 1) := Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hB hA) hC (by norm_num)
    (mul_nonneg hA hB0)) hD hDc (mul_nonneg (mul_nonneg hA hB0) hC0)

/-! ### Unimodality of `K_N` on `[2/5, 21/25]` via convexity of `P_N` (paper lines 3163–3185) -/

/-- Paper `eq:P-N` (line 3165): the quintic whose sign is opposite to `(log K_N)'`. -/
private def PNf (N x : ℝ) : ℝ :=
  3 * N * x ^ 5 - 3 * N * x ^ 4 + 3 * N * x ^ 2 - 3 * N * x + 6 * x ^ 5 - 2 * x ^ 4 + 10 * x ^ 3
    - 6 * x ^ 2 + 4 * x + 4

private def PNf' (N x : ℝ) : ℝ :=
  15 * N * x ^ 4 - 12 * N * x ^ 3 + 6 * N * x - 3 * N + 30 * x ^ 4 - 8 * x ^ 3 + 30 * x ^ 2 - 12 * x + 4

private theorem PNf_deriv_eq (N x : ℝ) : deriv (PNf N) x = PNf' N x := by
  have h : HasDerivAt (PNf N) (3 * N * (5 * x ^ 4) - 3 * N * (4 * x ^ 3) + 3 * N * (2 * x ^ 1)
      - 3 * N * 1 + 6 * (5 * x ^ 4) - 2 * (4 * x ^ 3) + 10 * (3 * x ^ 2) - 6 * (2 * x ^ 1) + 4 * 1) x := by
    unfold PNf
    exact ((((((((((hasDerivAt_pow 5 x).const_mul (3 * N)).sub
      ((hasDerivAt_pow 4 x).const_mul (3 * N))).add ((hasDerivAt_pow 2 x).const_mul (3 * N))).sub
      ((hasDerivAt_id x).const_mul (3 * N))).add ((hasDerivAt_pow 5 x).const_mul 6)).sub
      ((hasDerivAt_pow 4 x).const_mul 2)).add ((hasDerivAt_pow 3 x).const_mul 10)).sub
      ((hasDerivAt_pow 2 x).const_mul 6)).add ((hasDerivAt_id x).const_mul 4)).add_const 4
  rw [h.deriv]; unfold PNf'; ring

private theorem PNf_diff (N x : ℝ) : DifferentiableAt ℝ (PNf N) x := by
  unfold PNf
  exact (((((((((((hasDerivAt_pow 5 x).const_mul (3 * N)).sub
    ((hasDerivAt_pow 4 x).const_mul (3 * N))).add ((hasDerivAt_pow 2 x).const_mul (3 * N))).sub
    ((hasDerivAt_id x).const_mul (3 * N))).add ((hasDerivAt_pow 5 x).const_mul 6)).sub
    ((hasDerivAt_pow 4 x).const_mul 2)).add ((hasDerivAt_pow 3 x).const_mul 10)).sub
    ((hasDerivAt_pow 2 x).const_mul 6)).add ((hasDerivAt_id x).const_mul 4)).add_const 4).differentiableAt

private theorem PNf'_deriv_eq (N x : ℝ) : deriv (PNf' N) x =
    60 * N * x ^ 3 - 36 * N * x ^ 2 + 6 * N + 120 * x ^ 3 - 24 * x ^ 2 + 60 * x - 12 := by
  have h : HasDerivAt (PNf' N) (15 * N * (4 * x ^ 3) - 12 * N * (3 * x ^ 2) + 6 * N * 1
      + 30 * (4 * x ^ 3) - 8 * (3 * x ^ 2) + 30 * (2 * x ^ 1) - 12 * 1) x := by
    unfold PNf'
    exact ((((((((hasDerivAt_pow 4 x).const_mul (15 * N)).sub
      ((hasDerivAt_pow 3 x).const_mul (12 * N))).add ((hasDerivAt_id x).const_mul (6 * N))).sub_const
      (3 * N)).add ((hasDerivAt_pow 4 x).const_mul 30)).sub ((hasDerivAt_pow 3 x).const_mul 8)).add
      ((hasDerivAt_pow 2 x).const_mul 30)).sub ((hasDerivAt_id x).const_mul 12) |>.add_const 4
  rw [h.deriv]; ring

private theorem PNf'_diff (N x : ℝ) : DifferentiableAt ℝ (PNf' N) x := by
  unfold PNf'
  exact (((((((((hasDerivAt_pow 4 x).const_mul (15 * N)).sub
    ((hasDerivAt_pow 3 x).const_mul (12 * N))).add ((hasDerivAt_id x).const_mul (6 * N))).sub_const
    (3 * N)).add ((hasDerivAt_pow 4 x).const_mul 30)).sub ((hasDerivAt_pow 3 x).const_mul 8)).add
    ((hasDerivAt_pow 2 x).const_mul 30)).sub ((hasDerivAt_id x).const_mul 12) |>.add_const 4).differentiableAt

private theorem PNf_convexOn {N : ℝ} (hN : 9 ≤ N) :
    ConvexOn ℝ (Set.Icc (2 / 5 : ℝ) (21 / 25)) (PNf N) := by
  have hd1 : deriv (PNf N) = PNf' N := funext (PNf_deriv_eq N)
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
    (fun x _ => (PNf_diff N x).continuousAt.continuousWithinAt)
    (fun x _ => (PNf_diff N x).differentiableWithinAt)
    (fun x _ => by rw [hd1]; exact (PNf'_diff N x).differentiableWithinAt)
  intro x hx
  rw [interior_Icc, Set.mem_Ioo] at hx
  have hd2 : deriv^[2] (PNf N) x = 60 * N * x ^ 3 - 36 * N * x ^ 2 + 6 * N + 120 * x ^ 3
      - 24 * x ^ 2 + 60 * x - 12 := by
    show deriv (deriv (PNf N)) x = _
    rw [hd1, PNf'_deriv_eq]
  rw [hd2]
  have hx0 : (0:ℝ) < x := by linarith [hx.1]
  have hp1 : (0:ℝ) ≤ 10 * x ^ 3 - 6 * x ^ 2 + 1 := by
    nlinarith [hx.1, hx.2, hx0, mul_nonneg (mul_nonneg hx0.le hx0.le)
      (by linarith [hx.1] : (0:ℝ) ≤ 5 * x - 2), mul_nonneg hx0.le
      (by linarith [hx.1] : (0:ℝ) ≤ 5 * x - 2), sq_nonneg (2 * x - 1)]
  have hp2 : (0:ℝ) ≤ 120 * x ^ 3 - 24 * x ^ 2 + 60 * x - 12 := by
    nlinarith [mul_nonneg (by linarith [hx.1] : (0:ℝ) ≤ 5 * x - 1)
      (by positivity : (0:ℝ) ≤ 2 * x ^ 2 + 1)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N) hp1, hp2]

/-- Sublevel-set convexity: on `[2/5,21/25]`, `P_N ≤ 0` at both ends of a subinterval forces
`P_N ≤ 0` throughout it. -/
private theorem PNf_le_between {N a s b : ℝ} (hN : 9 ≤ N)
    (ha : a ∈ Set.Icc (2 / 5 : ℝ) (21 / 25)) (hb : b ∈ Set.Icc (2 / 5 : ℝ) (21 / 25))
    (has : a ≤ s) (hsb : s ≤ b) (hpa : PNf N a ≤ 0) (hpb : PNf N b ≤ 0) : PNf N s ≤ 0 := by
  rcases eq_or_lt_of_le (le_trans has hsb) with hab | hab
  · rw [le_antisymm (hab ▸ hsb) has]; exact hpa
  · have hba : (0:ℝ) < b - a := by linarith
    have hbane : b - a ≠ 0 := hba.ne'
    have hw1 : (0:ℝ) ≤ (b - s) / (b - a) := div_nonneg (by linarith) hba.le
    have hw2 : (0:ℝ) ≤ (s - a) / (b - a) := div_nonneg (by linarith) hba.le
    have hsum : (b - s) / (b - a) + (s - a) / (b - a) = 1 := by
      rw [← add_div, div_eq_one_iff_eq hbane]; ring
    have hcomb : ((b - s) / (b - a)) • a + ((s - a) / (b - a)) • b = s := by
      simp only [smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hbane]; ring
    have hconv := (PNf_convexOn hN).2 ha hb hw1 hw2 hsum
    rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
    nlinarith [hconv, mul_nonneg hw1 (neg_nonneg.mpr hpa), mul_nonneg hw2 (neg_nonneg.mpr hpb)]

/-- `G_N(y) = log K_N(y)`, the log of `K_N` (paper's `log K_N`). -/
private noncomputable def Gf (N y : ℝ) : ℝ :=
  Real.log ((N + 2) / N) + 2 * Real.log (1 - y) + Real.log (1 + y ^ 3)
    + (3 * N / 4 - 1) * Real.log (1 + y ^ 2)

private theorem Gf_diff {N x : ℝ} (hN : 0 < N) (hx1 : x < 1) (hx3 : 0 < 1 + x ^ 3) :
    DifferentiableAt ℝ (Gf N) x := by
  have h1x : (1:ℝ) - x ≠ 0 := (show (0:ℝ) < 1 - x by linarith).ne'
  have hlin : HasDerivAt (fun y:ℝ => 1 - y) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
  have h13 : HasDerivAt (fun y:ℝ => 1 + y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x).const_add 1
  have h12 : HasDerivAt (fun y:ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  unfold Gf
  exact ((((hasDerivAt_const x (Real.log ((N + 2) / N))).add ((hlin.log h1x).const_mul 2)).add
    (h13.log hx3.ne')).add ((h12.log (by positivity)).const_mul (3 * N / 4 - 1))).differentiableAt

private theorem Gf_deriv_eq {N x : ℝ} (hN : 0 < N) (hx1 : x < 1) (hx3 : 0 < 1 + x ^ 3) :
    deriv (Gf N) x = 2 * (-1 / (1 - x)) + 3 * x ^ 2 / (1 + x ^ 3)
      + (3 * N / 4 - 1) * (2 * x / (1 + x ^ 2)) := by
  have h1x : (1:ℝ) - x ≠ 0 := (show (0:ℝ) < 1 - x by linarith).ne'
  have hlin : HasDerivAt (fun y:ℝ => 1 - y) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
  have h13 : HasDerivAt (fun y:ℝ => 1 + y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x).const_add 1
  have h12 : HasDerivAt (fun y:ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have h : HasDerivAt (Gf N) (0 + 2 * (-1 / (1 - x)) + 3 * x ^ 2 / (1 + x ^ 3)
      + (3 * N / 4 - 1) * (2 * x / (1 + x ^ 2))) x := by
    unfold Gf
    exact (((hasDerivAt_const x (Real.log ((N + 2) / N))).add ((hlin.log h1x).const_mul 2)).add
      (h13.log hx3.ne')).add ((h12.log (by positivity)).const_mul (3 * N / 4 - 1))
  rw [h.deriv]; ring

/-- On any subinterval of `[2/5,21/25]` where `P_N ≤ 0`, `G_N` (= `log K_N`) is nondecreasing. -/
private theorem Gf_monotoneOn {N p q : ℝ} (hN : 9 ≤ N) (hp : 2 / 5 ≤ p) (hq : q ≤ 21 / 25)
    (hP : ∀ y ∈ Set.Icc p q, PNf N y ≤ 0) : MonotoneOn (Gf N) (Set.Icc p q) := by
  have hNpos : (0:ℝ) < N := by linarith
  have hdom : ∀ y ∈ Set.Icc p q, y < 1 ∧ 0 < 1 + y ^ 3 := fun y hy => by
    simp only [Set.mem_Icc] at hy
    exact ⟨by linarith [hy.2, hq],
      by nlinarith [hy.1, hp, pow_nonneg (show (0:ℝ) ≤ y by linarith [hy.1, hp]) 3]⟩
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun y hy => (Gf_diff hNpos (hdom y hy).1 (hdom y hy).2).continuousAt.continuousWithinAt)
  · intro y hy
    rw [interior_Icc] at hy
    have hy' : y ∈ Set.Icc p q := ⟨(Set.mem_Ioo.mp hy).1.le, (Set.mem_Ioo.mp hy).2.le⟩
    exact (Gf_diff hNpos (hdom y hy').1 (hdom y hy').2).differentiableWithinAt
  · intro y hy
    rw [interior_Icc, Set.mem_Ioo] at hy
    have hy' : y ∈ Set.Icc p q := ⟨hy.1.le, hy.2.le⟩
    have h1y : (0:ℝ) < 1 - y := by linarith [hy.2, hq]
    have h3y : (0:ℝ) < 1 + y ^ 3 := (hdom y hy').2
    have h2y : (0:ℝ) < 1 + y ^ 2 := by positivity
    rw [Gf_deriv_eq hNpos (by linarith [hy.2, hq]) h3y]
    have hden : (0:ℝ) < 2 * (1 - y) * (1 + y ^ 3) * (1 + y ^ 2) :=
      mul_pos (mul_pos (mul_pos (by norm_num) h1y) h3y) h2y
    have hPy : PNf N y ≤ 0 := hP y hy'
    have hid : (2 * (-1 / (1 - y)) + 3 * y ^ 2 / (1 + y ^ 3) + (3 * N / 4 - 1) * (2 * y / (1 + y ^ 2)))
        * (2 * (1 - y) * (1 + y ^ 3) * (1 + y ^ 2)) = -PNf N y := by
      have := h1y.ne'; have := h3y.ne'; have := h2y.ne'; unfold PNf; field_simp; ring
    have hG' : 2 * (-1 / (1 - y)) + 3 * y ^ 2 / (1 + y ^ 3) + (3 * N / 4 - 1) * (2 * y / (1 + y ^ 2))
        = -PNf N y / (2 * (1 - y) * (1 + y ^ 3) * (1 + y ^ 2)) := by
      rw [eq_div_iff hden.ne']; linarith [hid]
    rw [hG']; exact div_nonneg (by linarith [hPy]) hden.le

/-- On any subinterval of `[2/5,21/25]` where `P_N ≥ 0`, `G_N` (= `log K_N`) is nonincreasing. -/
private theorem Gf_antitoneOn {N p q : ℝ} (hN : 9 ≤ N) (hp : 2 / 5 ≤ p) (hq : q ≤ 21 / 25)
    (hP : ∀ y ∈ Set.Icc p q, 0 ≤ PNf N y) : AntitoneOn (Gf N) (Set.Icc p q) := by
  have hNpos : (0:ℝ) < N := by linarith
  have hdom : ∀ y ∈ Set.Icc p q, y < 1 ∧ 0 < 1 + y ^ 3 := fun y hy => by
    simp only [Set.mem_Icc] at hy
    exact ⟨by linarith [hy.2, hq],
      by nlinarith [hy.1, hp, pow_nonneg (show (0:ℝ) ≤ y by linarith [hy.1, hp]) 3]⟩
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun y hy => (Gf_diff hNpos (hdom y hy).1 (hdom y hy).2).continuousAt.continuousWithinAt)
  · intro y hy
    rw [interior_Icc] at hy
    have hy' : y ∈ Set.Icc p q := ⟨(Set.mem_Ioo.mp hy).1.le, (Set.mem_Ioo.mp hy).2.le⟩
    exact (Gf_diff hNpos (hdom y hy').1 (hdom y hy').2).differentiableWithinAt
  · intro y hy
    rw [interior_Icc, Set.mem_Ioo] at hy
    have hy' : y ∈ Set.Icc p q := ⟨hy.1.le, hy.2.le⟩
    have h1y : (0:ℝ) < 1 - y := by linarith [hy.2, hq]
    have h3y : (0:ℝ) < 1 + y ^ 3 := (hdom y hy').2
    have h2y : (0:ℝ) < 1 + y ^ 2 := by positivity
    rw [Gf_deriv_eq hNpos (by linarith [hy.2, hq]) h3y]
    have hden : (0:ℝ) < 2 * (1 - y) * (1 + y ^ 3) * (1 + y ^ 2) :=
      mul_pos (mul_pos (mul_pos (by norm_num) h1y) h3y) h2y
    have hPy : 0 ≤ PNf N y := hP y hy'
    have hid : (2 * (-1 / (1 - y)) + 3 * y ^ 2 / (1 + y ^ 3) + (3 * N / 4 - 1) * (2 * y / (1 + y ^ 2)))
        * (2 * (1 - y) * (1 + y ^ 3) * (1 + y ^ 2)) = -PNf N y := by
      have := h1y.ne'; have := h3y.ne'; have := h2y.ne'; unfold PNf; field_simp; ring
    have hG' : 2 * (-1 / (1 - y)) + 3 * y ^ 2 / (1 + y ^ 3) + (3 * N / 4 - 1) * (2 * y / (1 + y ^ 2))
        = -PNf N y / (2 * (1 - y) * (1 + y ^ 3) * (1 + y ^ 2)) := by
      rw [eq_div_iff hden.ne']; linarith [hid]
    rw [hG', neg_div]; exact neg_nonpos.mpr (div_nonneg hPy hden.le)

/-- **Paper endpoint assembly (`eq:K-N-def`, lines 3163–3277):** `K_N(x) ≥ 1` for odd `N ≥ 9`,
`x ≥ 2/5`, and `x` in the domain `2x²/N ≤ 1−x` (i.e. `x ≤ β_N`). -/
theorem KN_ge_one {N x : ℝ} (hodd : ∃ k : ℕ, N = 2 * (k : ℝ) + 9) (hN : 9 ≤ N) (hx : 2 / 5 ≤ x)
    (hdom : 2 * x ^ 2 / N ≤ 1 - x) : 1 ≤ KN N x := by
  have hNpos : (0:ℝ) < N := by linarith
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hx1 : x < 1 := by
    have hpos : (0:ℝ) < 2 * x ^ 2 / N := div_pos (by nlinarith [hx]) hNpos
    linarith [hdom, hpos]
  have hP25 : PNf N (2 / 5) ≤ 0 := by unfold PNf; nlinarith [hN]
  have hK25 : 1 ≤ KN N (2 / 5) := KN_two_fifths_ge_one hodd
  have hflb : 1 ≤ flb N := by obtain ⟨k, rfl⟩ := hodd; exact flb_ind k
  have h21dom : 2 * (21 / 25 : ℝ) ^ 2 / N ≤ 1 - 21 / 25 := by
    rw [div_le_iff₀ hNpos]; nlinarith [hN]
  have hK21 : 1 ≤ KN N (21 / 25) :=
    le_trans hflb (KN_ge_flb hN (le_refl (21 / 25 : ℝ)) (by norm_num) h21dom)
  by_cases hxc : x ≤ 21 / 25
  · by_cases hPN : PNf N x ≤ 0
    · have hmono := Gf_monotoneOn hN (le_refl (2 / 5 : ℝ)) hxc
        (fun y hy => PNf_le_between hN ⟨le_refl _, by norm_num⟩ ⟨hx, hxc⟩
          (Set.mem_Icc.mp hy).1 (Set.mem_Icc.mp hy).2 hP25 hPN)
      have hGle : Gf N (2 / 5) ≤ Gf N x := hmono ⟨le_refl _, hx⟩ ⟨hx, le_refl _⟩ hx
      have e1 : Real.log (KN N x) = Gf N x := log_KN hNpos hx0 hx1
      have e2 : Real.log (KN N (2 / 5)) = Gf N (2 / 5) := log_KN hNpos (by norm_num) (by norm_num)
      refine one_le_KN_of_log (KN_pos hNpos hx0 hx1) ?_
      rw [e1]; linarith [Real.log_nonneg hK25, hGle, e2.symm.le, e2.le]
    · have hPge : ∀ y ∈ Set.Icc x (21 / 25), 0 ≤ PNf N y := by
        intro y hy; simp only [Set.mem_Icc] at hy
        by_contra hlt; push_neg at hlt
        exact absurd (PNf_le_between hN ⟨by norm_num, by norm_num⟩
          ⟨by linarith [hy.1, hx], hy.2⟩ hx hy.1 hP25 hlt.le) hPN
      have hanti := Gf_antitoneOn hN hx (le_refl (21 / 25 : ℝ)) hPge
      have hGle : Gf N (21 / 25) ≤ Gf N x := hanti ⟨le_refl _, hxc⟩ ⟨hxc, le_refl _⟩ hxc
      have e1 : Real.log (KN N x) = Gf N x := log_KN hNpos hx0 hx1
      have e2 : Real.log (KN N (21 / 25)) = Gf N (21 / 25) := log_KN hNpos (by norm_num) (by norm_num)
      refine one_le_KN_of_log (KN_pos hNpos hx0 hx1) ?_
      rw [e1]; linarith [Real.log_nonneg hK21, hGle, e2.symm.le, e2.le]
  · exact le_trans hflb (KN_ge_flb hN (le_of_lt (not_le.mp hxc)) hx1 hdom)

/-! ### The one-variable growth lemma `lem:J-growth` (paper line 3035) -/

private theorem log_J {N x : ℝ} (hN : 9 ≤ N) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log ((N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3)
        * (N * (1 + x ^ 2) / (N - x ^ 2)) ^ (3 * N / 4 - 1))
      = Real.log ((N + 2) / N) + (2 * Real.log (1 - x) + Real.log (1 + x ^ 3))
        + (3 * N / 4 - 1) * Real.log (N * (1 + x ^ 2) / (N - x ^ 2)) := by
  have hNpos : (0:ℝ) < N := by linarith
  have hNx2 : (0:ℝ) < N - x ^ 2 := by nlinarith [hN, hx0, hx1]
  have hbase : (0:ℝ) < N * (1 + x ^ 2) / (N - x ^ 2) := div_pos (mul_pos hNpos (by positivity)) hNx2
  have h1 : (N + 2) / N ≠ 0 := (div_pos (by linarith) hNpos).ne'
  have h2 : (1 - x) ^ 2 ≠ 0 := (pow_pos (by linarith) 2).ne'
  have h3 : (1:ℝ) + x ^ 3 ≠ 0 := (show (0:ℝ) < 1 + x ^ 3 by nlinarith [pow_nonneg hx0 3]).ne'
  have h4 : (N * (1 + x ^ 2) / (N - x ^ 2)) ^ (3 * N / 4 - 1) ≠ 0 := (Real.rpow_pos_of_pos hbase _).ne'
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero h1 h2) h3) h4, Real.log_mul (mul_ne_zero h1 h2) h3,
    Real.log_mul h1 h2, Real.log_pow, Real.log_rpow hbase]
  push_cast; ring

/-- **Paper `lem:J-growth` (line 3035):** for odd `N = 2k+9 ≥ 9`, `0 ≤ x < 1` with `2x²/N ≤ 1−x`,
`J_N(x) = (N+2)/N·(1−x)²(1+x³)(N(1+x²)/(N−x²))^{3N/4−1} ≥ 1`. -/
theorem J_growth {N x : ℝ} (hodd : ∃ k : ℕ, N = 2 * (k : ℝ) + 9) (hN : 9 ≤ N) (hx0 : 0 ≤ x)
    (hx1 : x < 1) (hdom : 2 * x ^ 2 / N ≤ 1 - x) :
    1 ≤ (N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3)
      * (N * (1 + x ^ 2) / (N - x ^ 2)) ^ (3 * N / 4 - 1) := by
  have hNpos : (0:ℝ) < N := by linarith
  have hNx2 : (0:ℝ) < N - x ^ 2 := by nlinarith [hN, hx0, hx1]
  have hbase : (0:ℝ) < N * (1 + x ^ 2) / (N - x ^ 2) := div_pos (mul_pos hNpos (by positivity)) hNx2
  have hP : (0:ℝ) ≤ (N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3) :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith) hNpos.le) (sq_nonneg _))
      (by nlinarith [pow_nonneg hx0 3])
  have hJpos : (0:ℝ) < (N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3)
      * (N * (1 + x ^ 2) / (N - x ^ 2)) ^ (3 * N / 4 - 1) :=
    mul_pos (mul_pos (mul_pos (div_pos (by linarith) hNpos) (pow_pos (by linarith) 2))
      (by nlinarith [pow_nonneg hx0 3])) (Real.rpow_pos_of_pos hbase _)
  by_cases hxc : x ≤ 2 / 5
  · have hlog0 : 0 ≤ Real.log ((N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3)
        * (N * (1 + x ^ 2) / (N - x ^ 2)) ^ (3 * N / 4 - 1)) := by
      rw [log_J hN hx0 hx1]; linarith [logJ_ge_LN hN hx0 hx1, LN_pos hN hx0 hxc]
    have h := Real.exp_le_exp.mpr hlog0
    rwa [Real.exp_zero, Real.exp_log hJpos] at h
  · have hKN := KN_ge_one hodd hN (le_of_lt (not_le.mp hxc)) hdom
    have hbaseg : (1 + x ^ 2 : ℝ) ≤ N * (1 + x ^ 2) / (N - x ^ 2) := by
      rw [le_div_iff₀ hNx2]
      nlinarith [mul_nonneg (sq_nonneg x) (show (0:ℝ) ≤ 1 + x ^ 2 by positivity)]
    have hrpow : (1 + x ^ 2) ^ (3 * N / 4 - 1) ≤ (N * (1 + x ^ 2) / (N - x ^ 2)) ^ (3 * N / 4 - 1) :=
      Real.rpow_le_rpow (by positivity) hbaseg (by linarith)
    have hJge : KN N x ≤ (N + 2) / N * (1 - x) ^ 2 * (1 + x ^ 3)
        * (N * (1 + x ^ 2) / (N - x ^ 2)) ^ (3 * N / 4 - 1) := by
      unfold KN; exact mul_le_mul_of_nonneg_left hrpow hP
    linarith [hKN, hJge]

end OddCycleBound.IntermediateRegion
