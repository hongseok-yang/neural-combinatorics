import EvenCycleApex.Finite.OneApex
import EvenCycleApex.Moments.ApexLifting

/-!
# Two apices on a finite host, without a certificate

Plan D10 (approved by the user, 2026-09-27).  The blueprint proves `E Π₂ ≥ Z₂` with the certificate
`mean_two`; commonality for two apices needs only `E (Q♯₂)⁴ ≥ 1`, which follows from the one-apex
machinery at `n = 4`:

```
  E (Q♯₂)⁴ ≥ (E Π₂)² / Z₂                         lem:quartic-support,  Z₂ = R₄ ≥ 1 > 0
  E Π₂ = A_{2,1}                                  K_{1,2,2} = C₄⁺¹, a relabelling on Fin 5
  A_{2,1} ≥ X² / (1 + b) ≥ (1 + 2b + c/3)² / (1 + b)      the k = 1 bound at n = 4, lem:diamond
  R₄ = 1 + 2a + 4b + c ≤ 1 + 6b + c              a ≤ b
  ⟹ E (Q♯₂)⁴ ≥ Θ(b, c) := (1 + 2b + c/3)⁴ / ((1 + b)² (1 + 6b + c)) ≥ 1.
```

`two_apex_scalar_inequality`: `(1 + 2b + c/3)⁴ − (1 + b)²(1 + 6b + c) = c/3 + 11b² + (terms ≥ 0)`, so
`Θ ≥ 1`, strictly unless `b = c = 0`.  Then `A_{n/2,2} ≥ E (Q♯₂)ⁿ ≥ (E (Q♯₂)⁴)^{n/4} ≥ Θ^{n/4} ≥ 1`
(`two_apex_bound`).  This is the mechanism of Grzesik–Lee–Lidický–Volec, *On tripartite common
graphs*, Theorem 4.3, in the blueprint's conditional-moment language.
-/

open Finset SimpleGraph

namespace EvenCycleApex

/-- **`two_apex_scalar_inequality`** (plan D10).  For `b, c ≥ 0`,
`(1 + b)²(1 + 6b + c) + c/3 + 11b² ≤ (1 + 2b + c/3)⁴`. -/
theorem two_apex_scalar_inequality {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (1 + b) ^ 2 * (1 + 6 * b + c) + (c / 3 + 11 * b ^ 2) ≤ (1 + 2 * b + c / 3) ^ 4 := by
  have key : (1 + 2 * b + c / 3) ^ 4 - ((1 + b) ^ 2 * (1 + 6 * b + c) + (c / 3 + 11 * b ^ 2))
      = 6 * b * c + 2 * c ^ 2 / 3 + 26 * b ^ 3 + 15 * b ^ 2 * c + 8 * b * c ^ 2 / 3
        + 4 * c ^ 3 / 27 + (2 * b + c / 3) ^ 4 := by ring
  have : 0 ≤ 6 * b * c + 2 * c ^ 2 / 3 + 26 * b ^ 3 + 15 * b ^ 2 * c + 8 * b * c ^ 2 / 3
      + 4 * c ^ 3 / 27 + (2 * b + c / 3) ^ 4 := by positivity
  linarith

/-- `Θ(b, c) = (1 + 2b + c/3)⁴ / ((1 + b)² (1 + 6b + c))`. -/
noncomputable def twoApexTheta (b c : ℝ) : ℝ := (1 + 2 * b + c / 3) ^ 4 / ((1 + b) ^ 2 * (1 + 6 * b + c))

lemma one_le_twoApexTheta {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) : 1 ≤ twoApexTheta b c := by
  rw [twoApexTheta, one_le_div (by positivity)]
  have := two_apex_scalar_inequality hb hc
  nlinarith [sq_nonneg b]

/-- `Θ > 1` as soon as `c > 0`. -/
lemma one_lt_twoApexTheta {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) : 1 < twoApexTheta b c := by
  rw [twoApexTheta, one_lt_div (by positivity)]
  have := two_apex_scalar_inequality hb hc.le
  nlinarith [sq_nonneg b]

/-! ### Two-apex moments as graph densities -/

variable {d : ℕ}

/-- The edges of `K_{1,2,2}` as the conditional sum `E_{z₀,z₁} Π₂` sees them, on `Fin 5`:
apices `z₀ = 0`, `z₁ = 1`, inner vertex `x = 2`, its two further neighbours `y = 3`, `y' = 4`. -/
def pi2Edges : Finset (Fin 5 × Fin 5) :=
  {(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)}

lemma edgePairs_apexCycle_four_one :
    edgePairs (apexCycle 4 1) = {(0, 1), (0, 3), (1, 2), (2, 3), (0, 4), (1, 4), (2, 4), (3, 4)} := by
  decide

/-- `E_z D₂² ` is the four-cycle density (`z₀ – x – z₁ – y – z₀`). -/
lemma sum_two_apex_D_sq (w : Fin d → ℝ) {L : Fin d → Fin d → ℝ} (hL : ∀ i j, L i j = L j i) :
    ∑ z : Fin 2 → Fin d, (∏ j, w (z j)) * (∑ x, w x * ∏ j, L (z j) x) ^ 2
      = edgeDensity w c4Edges L := by
  unfold edgeDensity c4Edges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_two, Fin.prod_univ_four]
  simp
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sq, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [hL x b]
  ring

/-- `E_z Π₂` is the density of `K_{1,2,2}`. -/
lemma sum_two_apex_Pi (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) :
    ∑ z : Fin 2 → Fin d, (∏ j, w (z j)) *
        ∑ x, w x * (∏ j, L (z j) x) * (∑ y, w y * L x y * ∏ j, L (z j) y) ^ 2
      = edgeDensity w pi2Edges L := by
  unfold edgeDensity pi2Edges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_two, Fin.prod_univ_five]
  simp
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  simp only [sq, mul_sum, sum_mul]
  refine sum_congr rfl fun e _ => sum_congr rfl fun f _ => ?_
  ring

namespace FiniteKernel

variable (K : FiniteKernel d)

/-- Sampling expectations over two apices, colour by colour. -/
private lemma E_two_colour (F : Sample d 2 → ℝ) :
    K.E F = (∑ z : Fin 2 → Fin d, (∏ j, K.w (z j)) * F (true, z)
      + ∑ z : Fin 2 → Fin d, (∏ j, K.w (z j)) * F (false, z)) / 2 := K.E_eq_colours F

/-- **`Z₂ = R₄`** (`lem:codegree-moments`, two apices). -/
theorem Z_two : K.Z 2 = K.R 4 := by
  have ht : ∑ z : Fin 2 → Fin d, (∏ j, K.w (z j)) * K.condD (true, z) ^ 2
      = edgeDensity K.w c4Edges (K.S 1) := by
    rw [← sum_two_apex_D_sq K.w (K.S_symm 1)]
    simp only [condD, condH, colour_true]
  have hf : ∑ z : Fin 2 → Fin d, (∏ j, K.w (z j)) * K.condD (false, z) ^ 2
      = edgeDensity K.w c4Edges (K.S (-1)) := by
    rw [← sum_two_apex_D_sq K.w (K.S_symm (-1))]
    simp only [condD, condH, colour_false]
  rw [Z, E_two_colour, ht, hf, R, hostDensity_eq_edgeDensity, hostDensity_eq_edgeDensity,
    edgePairs_cycleGraph_four]

/-- `R₄ ≤ 1 + 6b + c`, from `R₄ = 1 + 2a + 4b + c` and `a ≤ b`. -/
lemma R_four_le : K.R 4 ≤ 1 + 6 * K.b + K.c := by
  rw [K.R_four]; linarith [K.a_le_b]

lemma one_le_R_four : 1 ≤ K.R 4 := by
  rw [K.R_four]; linarith [K.a_nonneg, K.b_nonneg, K.c_nonneg]

/-- **`E Π₂ = A_{2,1}`** (plan D10, `FiniteKernel.twoApex_Pi_eq_oneApex`): the graph of `Π₂` is
`K_{1,2,2} = C₄⁺¹`, a relabelling of the 5-vertex host sum. -/
theorem twoApex_Pi_eq_oneApex : K.EPi 2 = K.A 4 1 := by
  have hiso : ∀ L : Fin d → Fin d → ℝ, (∀ i j, L i j = L j i) →
      edgeDensity K.w pi2Edges L = hostDensity K.w (apexCycle 4 1) L := fun L hL => by
    rw [hostDensity_eq_edgeDensity, edgePairs_apexCycle_four_one]
    exact edgeDensity_eq_of_iso K.w hL (by decide) (by decide)
  have ht : ∑ z : Fin 2 → Fin d, (∏ j, K.w (z j)) * K.condPi (true, z)
      = edgeDensity K.w pi2Edges (K.S 1) := by
    rw [← sum_two_apex_Pi K.w (K.S 1)]
    simp only [condPi, condA, condH, colour_true]
  have hf : ∑ z : Fin 2 → Fin d, (∏ j, K.w (z j)) * K.condPi (false, z)
      = edgeDensity K.w pi2Edges (K.S (-1)) := by
    rw [← sum_two_apex_Pi K.w (K.S (-1))]
    simp only [condPi, condA, condH, colour_false]
  rw [EPi, E_two_colour, ht, hf, A, hiso _ (K.S_symm 1), hiso _ (K.S_symm (-1))]

/-- **`E (Q♯₂)⁴ ≥ Θ(b, c) ≥ 1`** (plan D10, `FiniteKernel.two_apex_fourth_moment_ge_one`). -/
theorem two_apex_fourth_moment_ge_one :
    twoApexTheta K.b K.c ≤ K.E (fun ω : Sample d 2 => K.condQs ω ^ 4) ∧
      1 ≤ twoApexTheta K.b K.c := by
  obtain ⟨-, -, -, hXlow⟩ := K.diamond_lower_bound
  have hb := K.b_nonneg
  have hc := K.c_nonneg
  have hR1 := K.one_le_R_four
  have hZ : 0 < K.Z 2 := by rw [K.Z_two]; linarith
  have hsupp := (K.sharp_fourth_support (s := 2)).2 hZ
  rw [K.Z_two, K.twoApex_Pi_eq_oneApex] at hsupp
  -- `A_{2,1} ≥ X²/(1+b) ≥ (1 + 2b + c/3)²/(1+b)`
  have hA41 : K.EPi 1 ^ 2 / (1 + K.b) ≤ K.A 4 1 := by
    have h := (K.one_apex_bound (n := 4) (by decide) le_rfl).1
    rwa [show ((4 : ℕ) : ℝ) / 4 = 1 by norm_num, Real.rpow_one] at h
  have hX0 : 0 ≤ 1 + 2 * K.b + K.c / 3 := by positivity
  have hXsq : (1 + 2 * K.b + K.c / 3) ^ 2 ≤ K.EPi 1 ^ 2 := pow_le_pow_left₀ hX0 hXlow 2
  have hA : (1 + 2 * K.b + K.c / 3) ^ 2 / (1 + K.b) ≤ K.A 4 1 :=
    (div_le_div_of_nonneg_right hXsq (by linarith)).trans hA41
  have hA0 : 0 ≤ (1 + 2 * K.b + K.c / 3) ^ 2 / (1 + K.b) := by positivity
  have hAsq : ((1 + 2 * K.b + K.c / 3) ^ 2 / (1 + K.b)) ^ 2 ≤ K.A 4 1 ^ 2 :=
    pow_le_pow_left₀ hA0 hA 2
  refine ⟨?_, one_le_twoApexTheta hb hc⟩
  calc twoApexTheta K.b K.c
      = ((1 + 2 * K.b + K.c / 3) ^ 2 / (1 + K.b)) ^ 2 / (1 + 6 * K.b + K.c) := by
        rw [twoApexTheta, div_pow, ← pow_mul, div_div]
    _ ≤ K.A 4 1 ^ 2 / (1 + 6 * K.b + K.c) :=
        div_le_div_of_nonneg_right hAsq (by positivity)
    _ ≤ K.A 4 1 ^ 2 / K.R 4 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) K.R_four_le
    _ ≤ K.E (fun ω : Sample d 2 => K.condQs ω ^ 4) := hsupp

/-- **`thm:finite-main`, two apices (plan D10).**  For even `n ≥ 4`,
`A_{n/2,2} ≥ Θ(b, c)^{n/4} ≥ 1`. -/
theorem two_apex_bound {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    twoApexTheta K.b K.c ^ ((n : ℝ) / 4) ≤ K.A n 2 ∧ 1 ≤ twoApexTheta K.b K.c ^ ((n : ℝ) / 4) := by
  obtain ⟨hθ, hθ1⟩ := K.two_apex_fourth_moment_ge_one
  have hexp : (0 : ℝ) ≤ (n : ℝ) / 4 := by positivity
  refine ⟨?_, Real.one_le_rpow hθ1 hexp⟩
  calc twoApexTheta K.b K.c ^ ((n : ℝ) / 4)
      ≤ (K.E fun ω : Sample d 2 => K.condQs ω ^ 4) ^ ((n : ℝ) / 4) :=
        Real.rpow_le_rpow (by linarith) hθ hexp
    _ ≤ K.E fun ω : Sample d 2 => K.condQs ω ^ n := K.E_pow_ge_rpow K.condQs_nonneg h4
    _ ≤ K.A n 2 := (K.conditional_trace_bound (s := 2) hn h4).2

/-- `A_{n/2,2} ≥ 1` on every finite host. -/
theorem one_le_A_two {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) : 1 ≤ K.A n 2 :=
  (K.two_apex_bound hn h4).2.trans (K.two_apex_bound hn h4).1

end FiniteKernel

end EvenCycleApex
