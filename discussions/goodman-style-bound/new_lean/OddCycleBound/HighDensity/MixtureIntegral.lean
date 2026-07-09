/-
# High-density theorem — the Dirichlet-mixture positivity transfer (M1, Stage 2, `cor:diagonal`)

The algebraic mixture identity (`SymmetricPoly.lean`) exhibits `multiKernel` as `diagKernel` under the
substitution `ℓʲ ↦ h_j(L)/C(j+r−1,r−1)`.  The remaining content of `thm:mixture`/`cor:diagonal` is the
*positivity transfer*: `diagKernel ≥ 0` on `[−½,½]` ⟹ `multiKernel ≥ 0` on `[−½,½]ʳ`.  This is proved
by the interval-integral route (plan R3 mitigation): `h_j(L)/C(j+r−1,r−1)` is the `j`-th moment of the
Dirichlet mean `Σ Θᵢλᵢ`, realised as an iterated 1-D integral (`dirExp`); a nonnegative integrand
integrates to a nonnegative value.

This file (Stage 2a): the **natural Beta integral** `∫₀¹ tⁱ(1−t)ᵏ = i!·k!/(i+k+1)!`, the single
special-function fact the Dirichlet moment formula (`eq:dir-moment`) rests on.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import OddCycleBound.HighDensity.SymmetricPoly

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- **Natural Beta integral.**  `∫₀¹ tⁱ·(1−t)ᵏ dt = i!·k!/(i+k+1)!`.  Induction on `k`, one
integration by parts (`u = (1−t)^{k+1}`, `v' = tⁱ`); the boundary terms vanish. -/
lemma beta_nat : ∀ (i k : ℕ),
    (∫ t in (0:ℝ)..1, t ^ i * (1 - t) ^ k)
      = (Nat.factorial i * Nat.factorial k : ℝ) / (Nat.factorial (i + k + 1))
  | i, 0 => by
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.add_zero]
      rw [integral_pow, one_pow, zero_pow (by omega : i + 1 ≠ 0), sub_zero]
      have hfac : (Nat.factorial (i + 1) : ℝ) = (i + 1 : ℝ) * (Nat.factorial i : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hne : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have hi1 : (i + 1 : ℝ) ≠ 0 := by positivity
      rw [hfac]
      field_simp
  | i, (k + 1) => by
      have hi1 : (i + 1 : ℝ) ≠ 0 := by positivity
      -- IBP: u = (1-t)^{k+1}, v' = t^i, v = t^{i+1}/(i+1)
      have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
          HasDerivAt (fun t => (1 - t) ^ (k + 1)) (-((k + 1 : ℝ) * (1 - x) ^ k)) x := by
        intro x _
        have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := (hasDerivAt_id x).const_sub 1
        have h2 := h1.pow (k + 1)
        simp only [Nat.add_sub_cancel] at h2
        have heq : (↑(k + 1) : ℝ) * (1 - x) ^ k * (-1) = -((k + 1 : ℝ) * (1 - x) ^ k) := by
          push_cast; ring
        rwa [heq] at h2
      have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
          HasDerivAt (fun t => t ^ (i + 1) / (i + 1 : ℝ)) (x ^ i) x := by
        intro x _
        have h2 := (hasDerivAt_pow (i + 1) x).div_const (i + 1 : ℝ)
        simp only [Nat.add_sub_cancel] at h2
        have heq : (↑(i + 1) : ℝ) * x ^ i / (i + 1 : ℝ) = x ^ i := by
          push_cast; field_simp
        rwa [heq] at h2
      have hu' : IntervalIntegrable (fun x => -((k + 1 : ℝ) * (1 - x) ^ k)) volume 0 1 :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have hv' : IntervalIntegrable (fun x : ℝ => x ^ i) volume 0 1 :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have IBP := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div, mul_zero, one_pow, sub_zero] at IBP
      have hLHS : (∫ t in (0:ℝ)..1, t ^ i * (1 - t) ^ (k + 1))
          = ∫ t in (0:ℝ)..1, (1 - t) ^ (k + 1) * t ^ i := by
        apply integral_congr; intro x _; ring
      have hRHS : (∫ x in (0:ℝ)..1, -((k + 1 : ℝ) * (1 - x) ^ k) * (x ^ (i + 1) / (i + 1)))
          = -(((k + 1 : ℝ) / (i + 1)) * ∫ t in (0:ℝ)..1, t ^ (i + 1) * (1 - t) ^ k) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        apply integral_congr; intro x _; ring
      rw [hLHS, IBP, hRHS, beta_nat (i + 1) k]
      rw [show (i + 1) + k + 1 = i + (k + 1) + 1 from by omega]
      have e1 : (Nat.factorial (i + 1) : ℝ) = (i + 1 : ℝ) * (Nat.factorial i : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have e2 : (Nat.factorial (k + 1) : ℝ) = (k + 1 : ℝ) * (Nat.factorial k : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [e1, e2]
      field_simp
      ring

end OddCycleBound.HighDensity
