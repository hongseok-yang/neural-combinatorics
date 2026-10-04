import ApicesCommonness.Cycles.Conditional.Diamond

/-!
# One apex on a finite host

Blueprint `thm:finite-main`, one-apex part: for even `n ≥ 4`,

```
  A_{n/2,1} ≥ E (Q♯₁)ⁿ ≥ (E (Q♯₁)⁴)^{n/4} ≥ (X² / (1 + b))^{n/4} ≥ 1,      X = E Π₁.
```

The steps are `prop:conditional-trace`, moment monotonicity (`E_pow_ge_rpow`, weighted Jensen at the
real exponent `n/4 ≥ 1`), `lem:quartic-support` with `Z₁ = 1 + b > 0`, and `lem:diamond`:
`X ≥ 1 + 2b + c/3 ≥ 1 + b`, so `X² / (1 + b) ≥ 1 + b ≥ 1`.
-/

open Finset

namespace ApicesCommonness

/-- `(x⁴)^{n/4} = xⁿ` for `x ≥ 0`. -/
lemma pow_four_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ 4) ^ ((n : ℝ) / 4) = x ^ n := by
  rw [← Real.rpow_natCast x 4, ← Real.rpow_mul hx, show ((4 : ℕ) : ℝ) * ((n : ℝ) / 4) = (n : ℝ) by
    push_cast; ring, Real.rpow_natCast]

namespace FiniteKernel

variable {d s : ℕ} (K : FiniteKernel d)

/-- **Moment monotonicity** on the sampling space: `(E X⁴)^{n/4} ≤ E Xⁿ` for `X ≥ 0`, `n ≥ 4`. -/
lemma E_pow_ge_rpow {X : Sample d s → ℝ} (hX : ∀ ω, 0 ≤ X ω) {n : ℕ} (h4 : 4 ≤ n) :
    (K.E fun ω => X ω ^ 4) ^ ((n : ℝ) / 4) ≤ K.E fun ω => X ω ^ n := by
  have hp : (1 : ℝ) ≤ (n : ℝ) / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    exact_mod_cast (by omega : 1 * 4 ≤ n)
  have h := Real.rpow_arith_mean_le_arith_mean_rpow univ K.prob (fun ω => X ω ^ 4)
    (fun ω _ => K.prob_nonneg ω) K.sum_prob (fun ω _ => by have := hX ω; positivity) hp
  simp only [pow_four_rpow (hX _)] at h
  exact h

/-- **`thm:finite-main`, one apex.**  For even `n ≥ 4`,
`A_{n/2,1} ≥ (X² / (1 + b))^{n/4} ≥ 1` with `X = E Π₁`. -/
theorem one_apex_bound {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    (K.EPi 1 ^ 2 / (1 + K.b)) ^ ((n : ℝ) / 4) ≤ K.A n 1 ∧
      1 ≤ (K.EPi 1 ^ 2 / (1 + K.b)) ^ ((n : ℝ) / 4) := by
  obtain ⟨hZ, hX, -, hXlow⟩ := K.diamond_lower_bound
  have hb := K.b_nonneg
  have hc := K.c_nonneg
  have hZpos : 0 < K.Z 1 := by rw [hZ]; linarith
  have hsupp := (K.sharp_fourth_support (s := 1)).2 hZpos
  rw [hZ] at hsupp
  have hexp : (0 : ℝ) ≤ (n : ℝ) / 4 := by positivity
  have hbase : 0 ≤ K.EPi 1 ^ 2 / (1 + K.b) := div_nonneg (sq_nonneg _) (by linarith)
  refine ⟨?_, ?_⟩
  · calc (K.EPi 1 ^ 2 / (1 + K.b)) ^ ((n : ℝ) / 4)
        ≤ (K.E fun ω : Sample d 1 => K.condQs ω ^ 4) ^ ((n : ℝ) / 4) :=
          Real.rpow_le_rpow hbase hsupp hexp
      _ ≤ K.E fun ω : Sample d 1 => K.condQs ω ^ n := K.E_pow_ge_rpow K.condQs_nonneg h4
      _ ≤ K.A n 1 := (K.conditional_trace_bound (s := 1) hn h4).2
  · refine Real.one_le_rpow ?_ hexp
    -- `X ≥ 1 + 2b + c/3 ≥ 1 + b`, so `X² / (1 + b) ≥ 1 + b ≥ 1`
    have hX1 : 1 + K.b ≤ K.EPi 1 := by linarith
    rw [le_div_iff₀ (by linarith)]
    nlinarith

/-- `A_{n/2,1} ≥ 1` on every finite host. -/
theorem one_le_A_one {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) : 1 ≤ K.A n 1 :=
  (K.one_apex_bound hn h4).2.trans (K.one_apex_bound hn h4).1

end FiniteKernel

end ApicesCommonness
