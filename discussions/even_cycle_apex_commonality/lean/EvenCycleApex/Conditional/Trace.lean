import EvenCycleApex.Conditional.Defs
import EvenCycleApex.Graph.ApexEdges

/-!
# The conditional trace representation

Blueprint `prop:conditional-trace` and `lem:quartic-support`.

* `hostDensity_apexCycle`: on a host, the density of `C_n^{+s}` splits the vertex map into its cycle
  part `x` and its apex part `z` (`Fin (n + s) → Fin d ≃ (Fin n → Fin d) × (Fin s → Fin d)`), with
  the edge product `∏_{cycle} L(xᵢ, xⱼ) · ∏ᵢⱼ L(xᵢ, zⱼ)` (`prod_edgePairs_apexCycle`).
* `trace_condB_pow`: `Tr Bⁿ = ∑ₓ ∏ᵢ w(xᵢ) h(xᵢ) ∏_{cycle} S_σ(xᵢ, xⱼ)` — the copied closed-walk
  expansion with weights `w · h`; the two factors `√h` at each cycle vertex multiply to `h`.
* `hostDensity_apexCycle_eq_sum_trace`: averaging the `s` apices reproduces the `n s` apex edges,
  `t(C_n^{+s}, S_σ) = ∑_z ∏ⱼ w(zⱼ) · Tr B_{σ,z}ⁿ`.
* `conditional_trace_bound` (**`prop:conditional-trace`**): `A_{n/2,s} = E Tr Bⁿ ≥ E (Q♯)ⁿ` for even
  `n ≥ 4`, from `‖Bg‖^n ≤ Tr Bⁿ` at the conditional unit vector (and both sides `0` if `D = 0`).
* `sharp_fourth_support` (**`lem:quartic-support`**): `(Q♯)⁴ ≥ 2Π − D²` pointwise, and
  `E (Q♯)⁴ ≥ (E Π)² / Z` with `Z = E D² > 0`, by Cauchy–Schwarz on `E Π = E D (Q♯)²`.
-/

open Finset Matrix SimpleGraph

namespace EvenCycleApex

variable {d : ℕ}

/-- The host density of `C_n^{+s}`, split into the cycle part and the apex part. -/
theorem hostDensity_apexCycle (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) (n s : ℕ) :
    hostDensity w (apexCycle n s) L
      = ∑ x : Fin n → Fin d, ∑ z : Fin s → Fin d, (∏ i, w (x i)) * (∏ j, w (z j)) *
          ((∏ p ∈ edgePairs (cycleGraph n), L (x p.1) (x p.2)) * ∏ i, ∏ j, L (x i) (z j)) := by
  unfold hostDensity
  rw [← (appendEquiv n s (Fin d)).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => sum_congr rfl fun z _ => ?_
  simp only [appendEquiv, Equiv.coe_fn_mk]
  rw [show ∏ p ∈ edgePairs (apexCycle n s), L (Fin.append x z p.1) (Fin.append x z p.2)
      = (∏ p ∈ edgePairs (cycleGraph n),
          L (Fin.append x z (Fin.castAdd s p.1)) (Fin.append x z (Fin.castAdd s p.2))) *
        ∏ i : Fin n, ∏ j : Fin s,
          L (Fin.append x z (Fin.castAdd s i)) (Fin.append x z (Fin.natAdd n j)) from
      prod_edgePairs_apexCycle (fun a b => L (Fin.append x z a) (Fin.append x z b)),
    Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

namespace FiniteKernel

variable {s : ℕ} (K : FiniteKernel d)

/-- `A_{n/2,s} = E_σ t(C_n^{+s}, S_σ)` on the host. -/
noncomputable def A (n s : ℕ) : ℝ :=
  (hostDensity K.w (apexCycle n s) (K.S 1) + hostDensity K.w (apexCycle n s) (K.S (-1))) / 2

lemma colour_true : colour true = 1 := by simp [colour]

lemma colour_false : colour false = -1 := by simp [colour]

/-- `Tr Bⁿ` as a sum over closed walks with weights `w · h`. -/
theorem trace_condB_pow (ω : Sample d s) {n : ℕ} (hn : 3 ≤ n) :
    trace (K.condB ω ^ n) = ∑ x : Fin n → Fin d, (∏ i, K.w (x i)) * (∏ i, K.condH ω (x i)) *
      ∏ p ∈ edgePairs (cycleGraph n), K.S (colour ω.1) (x p.1) (x p.2) := by
  rw [condB, ← hostDensity_cycle_eq_trace (K.condW_nonneg ω) (K.S_symm _) hn]
  unfold hostDensity
  refine sum_congr rfl fun x _ => ?_
  simp only [condW, prod_mul_distrib]

/-- Averaging the apices reproduces the apex edges:
`t(C_n^{+s}, S_σ) = ∑_z ∏ⱼ w(zⱼ) Tr B_{σ,z}ⁿ`. -/
theorem hostDensity_apexCycle_eq_sum_trace (b : Bool) {n : ℕ} (hn : 3 ≤ n) :
    hostDensity K.w (apexCycle n s) (K.S (colour b))
      = ∑ z : Fin s → Fin d, (∏ j, K.w (z j)) * trace (K.condB (b, z) ^ n) := by
  rw [hostDensity_apexCycle, sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [trace_condB_pow K (b, z) hn, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have hh : ∏ i, K.condH (b, z) (x i) = ∏ i, ∏ j, K.S (colour b) (x i) (z j) := by
    refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => K.S_symm _ _ _
  rw [hh]
  ring

/-- `A_{n/2,s} = E Tr Bⁿ`. -/
theorem A_eq_E_trace {n : ℕ} (hn : 3 ≤ n) :
    K.A n s = K.E (fun ω : Sample d s => trace (K.condB ω ^ n)) := by
  have ht := K.hostDensity_apexCycle_eq_sum_trace (s := s) true hn
  have hf := K.hostDensity_apexCycle_eq_sum_trace (s := s) false hn
  rw [colour_true] at ht
  rw [colour_false] at hf
  rw [E_eq_colours, A, ht, hf]

/-- `Tr Bⁿ ≥ (Q♯)ⁿ` for even `n ≥ 2`. -/
theorem condQs_pow_le_trace (ω : Sample d s) {n : ℕ} (hn : Even n) (h2 : 2 ≤ n) :
    K.condQs ω ^ n ≤ trace (K.condB ω ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by obtain ⟨k, hk⟩ := hn; omega⟩
  rcases (K.condD_nonneg ω).eq_or_lt with hD | hD
  · rw [condQs, ← hD, div_zero, Real.sqrt_zero, zero_pow (by omega)]
    exact trace_pow_nonneg (K.condB_isHermitian ω) hn
  · have h := normSq_pow_le_trace_pow (K.condB_isHermitian ω) (K.condVec_dot_self ω hD) m
    rwa [K.condB_condVec_normSq ω, ← pow_mul] at h

/-- Expectation is monotone. -/
lemma E_mono {F G : Sample d s → ℝ} (h : ∀ ω, F ω ≤ G ω) : K.E F ≤ K.E G :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (K.prob_nonneg ω)

lemma E_nonneg {F : Sample d s → ℝ} (h : ∀ ω, 0 ≤ F ω) : 0 ≤ K.E F :=
  sum_nonneg fun ω _ => mul_nonneg (K.prob_nonneg ω) (h ω)

/-- **`prop:conditional-trace`.**  For even `n ≥ 4`, `A_{n/2,s} = E Tr Bⁿ ≥ E (Q♯)ⁿ`. -/
theorem conditional_trace_bound {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    K.A n s = K.E (fun ω : Sample d s => trace (K.condB ω ^ n)) ∧
      K.E (fun ω : Sample d s => K.condQs ω ^ n) ≤ K.A n s := by
  refine ⟨K.A_eq_E_trace (by omega), ?_⟩
  rw [K.A_eq_E_trace (by omega)]
  exact K.E_mono fun ω => K.condQs_pow_le_trace ω hn (by omega)

/-! ### `lem:quartic-support` -/

/-- `(Q♯)⁴ ≥ 2Π − D²`: the difference is `(Π/D − D)²`. -/
theorem condQs_four_ge (ω : Sample d s) :
    2 * K.condPi ω - K.condD ω ^ 2 ≤ K.condQs ω ^ 4 := by
  rcases (K.condD_nonneg ω).eq_or_lt with hD | hD
  · rw [condQs, ← hD, K.condPi_eq_zero_of_condD ω hD.symm, div_zero, Real.sqrt_zero]
    norm_num
  · have hq : K.condQs ω ^ 2 = K.condPi ω / K.condD ω := by
      rw [condQs, Real.sq_sqrt (div_nonneg (K.condPi_nonneg ω) hD.le)]
    have h4 : K.condQs ω ^ 4 = (K.condPi ω / K.condD ω) ^ 2 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, hq]
    have hid : (K.condPi ω / K.condD ω) ^ 2 - (2 * K.condPi ω - K.condD ω ^ 2)
        = (K.condPi ω / K.condD ω - K.condD ω) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (K.condPi ω / K.condD ω - K.condD ω)]

/-- `Z_s = E D²`. -/
noncomputable def Z (s : ℕ) : ℝ := K.E (fun ω : Sample d s => K.condD ω ^ 2)

/-- `E Π_s`. -/
noncomputable def EPi (s : ℕ) : ℝ := K.E (fun ω : Sample d s => K.condPi ω)

/-- **`lem:quartic-support`.**  `(Q♯)⁴ ≥ 2Π − D²` pointwise, and `E (Q♯)⁴ ≥ (E Π)² / Z` if
`Z = E D² > 0`. -/
theorem sharp_fourth_support :
    (∀ ω : Sample d s, 2 * K.condPi ω - K.condD ω ^ 2 ≤ K.condQs ω ^ 4) ∧
      (0 < K.Z s → K.EPi s ^ 2 / K.Z s ≤ K.E (fun ω : Sample d s => K.condQs ω ^ 4)) := by
  refine ⟨K.condQs_four_ge, fun hZ => ?_⟩
  -- `E Π = E D (Q♯)²`, then Cauchy–Schwarz
  have hEPi : K.EPi s = ∑ ω : Sample d s, K.prob ω * K.condD ω * K.condQs ω ^ 2 := by
    rw [EPi, E]
    refine sum_congr rfl fun ω _ => ?_
    rw [mul_assoc, K.condD_mul_condQs_sq ω]
  have hcs : K.EPi s ^ 2 ≤ K.Z s * K.E (fun ω : Sample d s => K.condQs ω ^ 4) := by
    rw [hEPi, Z, E, E]
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul univ
      (fun ω _ => mul_nonneg (K.prob_nonneg ω) (sq_nonneg _))
      (fun ω _ => mul_nonneg (K.prob_nonneg ω) (by positivity)) (fun ω _ => le_of_eq ?_)
    ring
  rw [div_le_iff₀ hZ, mul_comm]
  exact hcs

end FiniteKernel

end EvenCycleApex
