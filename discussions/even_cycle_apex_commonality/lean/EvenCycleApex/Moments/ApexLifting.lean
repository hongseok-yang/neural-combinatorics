import EvenCycleApex.Moments.Basic
import EvenCycleApex.Conditional.Trace

/-!
# Apex-number lifting

Blueprint `lem:apex-lifting`, on a finite host: if `R_n > 0` and `1 ≤ s ≤ k`, then

```
  A_{n/2,k} ≥ A_{n/2,s}^{k/s} / R_n^{k/s − 1}.
```

On the space of a colour `σ` and `n` cycle vertices `x`, let `ν(σ, x) = ½ ∏ᵢ w(xᵢ) ∏_{cycle} S_σ`
(a nonnegative measure of total mass `R_n`) and `ξ(σ, x) = ∑ₜ wₜ ∏ᵢ S_σ(xᵢ, t)`, the apex codegree
(`apexWeight`).  Then `A_{n/2,j} = ∫ ξʲ dν` for every `j` (`hostDensity_apexCycle_eq_xi`: `j`
independent new vertices contribute `j` copies of `ξ` and no edges among them), and Jensen at
exponent `k/s ≥ 1` for the probability measure `ν / R_n`, applied to `ξ^s`, gives the claim.
-/

open Finset SimpleGraph

namespace EvenCycleApex

variable {d : ℕ}

/-- The apex codegree `ξ(x) = ∑ₜ wₜ ∏ᵢ L(xᵢ, t)` of a cycle tuple `x`. -/
def apexWeight (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) {n : ℕ} (x : Fin n → Fin d) : ℝ :=
  ∑ t, w t * ∏ i, L (x i) t

/-- `t(C_n^{+s}, L) = ∑ₓ ∏ᵢ w(xᵢ) ∏_{cycle} L · ξ(x)^s`. -/
theorem hostDensity_apexCycle_eq_xi (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) (n s : ℕ) :
    hostDensity w (apexCycle n s) L
      = ∑ x : Fin n → Fin d, (∏ i, w (x i)) *
          (∏ p ∈ edgePairs (cycleGraph n), L (x p.1) (x p.2)) * apexWeight w L x ^ s := by
  rw [hostDensity_apexCycle]
  refine sum_congr rfl fun x _ => ?_
  have hz : ∑ z : Fin s → Fin d, (∏ j, w (z j)) * ∏ i, ∏ j, L (x i) (z j)
      = apexWeight w L x ^ s := by
    calc ∑ z : Fin s → Fin d, (∏ j, w (z j)) * ∏ i, ∏ j, L (x i) (z j)
        = ∑ z : Fin s → Fin d, ∏ j, (w (z j) * ∏ i, L (x i) (z j)) := by
          refine sum_congr rfl fun z _ => ?_
          rw [prod_comm (s := univ) (t := univ), ← prod_mul_distrib]
      _ = ∏ _j : Fin s, ∑ t, w t * ∏ i, L (x i) t :=
          (Fintype.prod_sum (fun (_ : Fin s) (t : Fin d) => w t * ∏ i, L (x i) t)).symm
      _ = apexWeight w L x ^ s := by rw [prod_const, card_univ, Fintype.card_fin]; rfl
  rw [← hz, mul_sum]
  refine sum_congr rfl fun z _ => by ring

namespace FiniteKernel

variable (K : FiniteKernel d)

/-- **`lem:apex-lifting`.**  If `R_n > 0` and `1 ≤ s ≤ k`, then
`A_{n/2,k} ≥ A_{n/2,s}^{k/s} / R_n^{k/s − 1}`. -/
theorem apex_number_moment_lifting {n s k : ℕ} (hs : 1 ≤ s) (hsk : s ≤ k) (hR : 0 < K.R n) :
    K.A n s ^ ((k : ℝ) / s) / K.R n ^ ((k : ℝ) / s - 1) ≤ K.A n k := by
  classical
  -- the measure `ν` and the variable `ξ` on `Bool × (Fin n → Fin d)`
  set ν : Bool × (Fin n → Fin d) → ℝ := fun ω => (1 / 2) * ((∏ i, K.w (ω.2 i)) *
    ∏ p ∈ edgePairs (cycleGraph n), K.S (colour ω.1) (ω.2 p.1) (ω.2 p.2)) with hν
  set ξ : Bool × (Fin n → Fin d) → ℝ := fun ω => apexWeight K.w (K.S (colour ω.1)) ω.2 with hξ
  have hν0 : ∀ ω, 0 ≤ ν ω := fun ω => mul_nonneg (by norm_num) (mul_nonneg
    (prod_nonneg fun i _ => K.w_nonneg _) (prod_nonneg fun p _ => K.S_nonneg (colour_cases _) _ _))
  have hξ0 : ∀ ω, 0 ≤ ξ ω := fun ω => sum_nonneg fun t _ => mul_nonneg (K.w_nonneg t)
    (prod_nonneg fun i _ => K.S_nonneg (colour_cases _) _ _)
  have hA : ∀ j, K.A n j = ∑ ω, ν ω * ξ ω ^ j := fun j => by
    rw [A, hostDensity_apexCycle_eq_xi, hostDensity_apexCycle_eq_xi, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [hν, hξ, colour_true, colour_false, add_div, sum_div]
    congr 1 <;> refine sum_congr rfl fun x _ => by ring
  have hRν : K.R n = ∑ ω, ν ω := by
    rw [R, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hν, hostDensity, colour_true, colour_false, add_div, sum_div]
    congr 1 <;> refine sum_congr rfl fun x _ => by ring
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hks : (1 : ℝ) ≤ (k : ℝ) / s := by
    rw [le_div_iff₀ hs0, one_mul]; exact_mod_cast hsk
  -- Jensen for `ν / R`
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow univ (fun ω => ν ω / K.R n)
    (fun ω => ξ ω ^ s) (fun ω _ => div_nonneg (hν0 ω) hR.le)
    (by rw [← sum_div, ← hRν, div_self hR.ne']) (fun ω _ => pow_nonneg (hξ0 ω) s) hks
  have hpow : ∀ ω, (ξ ω ^ s) ^ ((k : ℝ) / s) = ξ ω ^ k := fun ω => by
    rw [← Real.rpow_natCast (ξ ω) s, ← Real.rpow_mul (hξ0 ω), mul_div_cancel₀ _ hs0.ne',
      Real.rpow_natCast]
  simp only [hpow, div_mul_eq_mul_div, ← sum_div, ← hA] at hJ
  -- `(A_s / R)^{k/s} ≤ A_k / R`, then clear `R`
  have hAs0 : 0 ≤ K.A n s := by rw [hA]; exact sum_nonneg fun ω _ => mul_nonneg (hν0 ω) (by
    have := hξ0 ω; positivity)
  rw [Real.div_rpow hAs0 hR.le] at hJ
  have hRpow : K.R n ^ ((k : ℝ) / s) = K.R n ^ ((k : ℝ) / s - 1) * K.R n := by
    rw [← Real.rpow_add_one hR.ne']; ring_nf
  rw [hRpow, div_le_div_iff₀ (by positivity) hR, ← mul_assoc] at hJ
  rw [div_le_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right hJ hR

end FiniteKernel

end EvenCycleApex
