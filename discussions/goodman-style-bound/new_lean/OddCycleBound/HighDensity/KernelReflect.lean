/-
# High-density theorem — the reflection inequality (M5/M6 shared machinery, part D core)

The reflection step of `thm:r1` and `thm:strip` pairs a point `s` in the negative window with its
reflection `ŝ = 2sₐ − s` in a positive partner band.  Because `q + ŝ = 1 − (q+s)`, the `ρ`-values
satisfy `ρ(q+s) + ρ(q+ŝ) ≥ 0` (`rho_reflect`), and the kernel weight is larger at the partner
(`κ(ŝ) ≥ κ(s)`).  The abstract inequality behind "the partner pays for the deficit" is:
`0 < a ≤ b`, `0 ≤ y`, `0 ≤ x + y  ⟹  0 ≤ a·x + b·y`.
-/

import OddCycleBound.HighDensity.RhoLemma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **Abstract weighted reflection.**  With `a = κ(s) ≤ κ(ŝ) = b` (both positive), `x = ρ(q+s)` the
possibly-negative value, `y = ρ(q+ŝ) ≥ 0` the partner value, and `x + y ≥ 0` (reflection), the
`κ`-weighted pair is nonnegative: `a·x + b·y = a·(x+y) + (b−a)·y ≥ 0`. -/
lemma reflection_weighted {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 ≤ y)
    (hxy : 0 ≤ x + y) : 0 ≤ a * x + b * y := by
  nlinarith [mul_nonneg ha hxy, mul_nonneg (sub_nonneg.mpr hab) hy]

/-- **Reflection pairing (D).**  Pair the right half `(c, c+δ)` of the negative window with the left
half `(c−δ, c)` around the center `c = 1/2 − q` (so `q + (2c−s) = 1 − (q+s)`).  If `κ ≥ 0` is
continuous and satisfies the reflection monotonicity `κ(2c−x) ≤ κ(x)` on `[c−δ,c]`, and `n = 2t+1 ≤ m`,
then the two half-integrals of `κ(s)·ρ(q+s)` sum to a nonnegative value: the partner band pays for the
possible deficit.  (This is the step whose earlier version was flawed — `rmk:r1-history`.) -/
lemma reflection_pair_nonneg {m t : ℕ} (hm : (2 * (t : ℝ) + 1) ≤ (m : ℝ)) (q : ℝ) (κ : ℝ → ℝ)
    (hκcont : Continuous κ) (c δ : ℝ) (hδ : 0 ≤ δ) (hc : c = 1 / 2 - q)
    (hκ0 : ∀ x, 0 ≤ κ x) (hκrefl : ∀ x ∈ Set.Icc (c - δ) c, κ (2 * c - x) ≤ κ x) :
    0 ≤ (∫ s in c..(c + δ), κ s * rho (2 * t + 1) m (q + s))
        + ∫ s in (c - δ)..c, κ s * rho (2 * t + 1) m (q + s) := by
  have hcont : Continuous (fun s => κ s * rho (2 * t + 1) m (q + s)) := by
    unfold rho; fun_prop
  have hfi : IntervalIntegrable (fun x => κ (2 * c - x) * rho (2 * t + 1) m (q + (2 * c - x)))
      volume (c - δ) c := by
    apply Continuous.intervalIntegrable
    exact (hκcont.comp (by fun_prop)).mul (by unfold rho; fun_prop)
  have hgi : IntervalIntegrable (fun s => κ s * rho (2 * t + 1) m (q + s)) volume (c - δ) c :=
    hcont.intervalIntegrable _ _
  have hrefl : (∫ x in (c - δ)..c, κ (2 * c - x) * rho (2 * t + 1) m (q + (2 * c - x)))
      = ∫ s in c..(c + δ), κ s * rho (2 * t + 1) m (q + s) := by
    rw [intervalIntegral.integral_comp_sub_left (fun s => κ s * rho (2 * t + 1) m (q + s)) (2 * c)]
    congr 1 <;> ring
  rw [← hrefl, ← intervalIntegral.integral_add hfi hgi]
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x hx
  refine reflection_weighted (hκ0 _) (hκrefl x hx)
    (rho_window_left t m hm (q + x) (by have := hx.2; rw [hc] at this; linarith)) ?_
  have he : (1 : ℝ) - (q + x) = q + (2 * c - x) := by rw [hc]; ring
  have := rho_reflect t m hm (q + x)
  rw [he] at this; linarith

/-- A region where `ρ(q+s) ≥ 0` contributes nonnegatively to the kernel integral (finite interval). -/
lemma region_nonneg {m t : ℕ} (κ : ℝ → ℝ) (q a b : ℝ) (hab : a ≤ b) (hκ0 : ∀ x, 0 ≤ κ x)
    (hρ : ∀ s ∈ Set.Icc a b, 0 ≤ rho (2 * t + 1) m (q + s)) :
    0 ≤ ∫ s in a..b, κ s * rho (2 * t + 1) m (q + s) := by
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  exact mul_nonneg (hκ0 s) (hρ s hs)

/-- The tail `(b,∞)` (where `ρ ≥ 0`) contributes nonnegatively to the kernel integral. -/
lemma tail_nonneg {m t : ℕ} (κ : ℝ → ℝ) (q b : ℝ) (hκ0 : ∀ x, 0 ≤ κ x)
    (hρ : ∀ s ∈ Set.Ioi b, 0 ≤ rho (2 * t + 1) m (q + s)) :
    0 ≤ ∫ s in Set.Ioi b, κ s * rho (2 * t + 1) m (q + s) := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro s hs
  exact mul_nonneg (hκ0 s) (hρ s hs)

end OddCycleBound.HighDensity
