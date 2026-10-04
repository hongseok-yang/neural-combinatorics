import ApicesCommonness.Cycles.Host.EvenCycle
import ApicesCommonness.Cycles.Host.ScalarBounds

/-!
# Conditional quantities for an arbitrary apex number

Blueprint `def:conditional`, `lem:conditional-bounds`, `lem:conditional-vector`.

The sampling space is `Sample d s = Bool × (Fin s → Fin d)`: a colour (`true ↦ σ = 1`,
`false ↦ σ = −1`), each with probability `1/2`, and `s` independent apex coordinates with weights
`w`; `prob ω = ½ ∏ⱼ w(zⱼ)` and `E F = ∑_ω prob ω · F ω`.  For a sample `ω = (σ, z)`:

```
  h(x) = ∏ⱼ S_σ(zⱼ, x),   D = E_x h,   A_in(x) = E_y S_σ(x, y) h(y),
  N = E_x h A_in,   Π = E_x h A_in²,   Q = N / D,   Q♯ = √(Π / D),
  B = the Euclidean matrix of `M_{√h} T_{S_σ} M_{√h}` = hostMatrix (w · h) S_σ.
```

Lean's convention `x / 0 = 0` gives the blueprint's `D = 0` branches (`Q = Q♯ = 0`) without a case
split.  The conditional unit vector is `gₓ = √(wₓ hₓ) / √D` (`condVec`), and for `D > 0`:
`g ⬝ g = 1`, `⟨g, Bg⟩ = Q`, `‖Bg‖² = Π / D = (Q♯)²` (`lem:conditional-vector`).
-/

open Finset Matrix

namespace ApicesCommonness

/-- The sampling space of the conditional argument: a colour and `s` apex coordinates. -/
abbrev Sample (d s : ℕ) := Bool × (Fin s → Fin d)

/-- The colour `σ = ±1` of a sample. -/
def colour (b : Bool) : ℝ := if b then 1 else -1

lemma colour_cases (b : Bool) : colour b = 1 ∨ colour b = -1 := by
  cases b <;> simp [colour]

namespace FiniteKernel

variable {d s : ℕ} (K : FiniteKernel d)

/-! ### The probability space -/

/-- The probability of a sample, `½ ∏ⱼ w(zⱼ)`. -/
noncomputable def prob (ω : Sample d s) : ℝ := (1 / 2) * ∏ j, K.w (ω.2 j)

lemma prob_nonneg (ω : Sample d s) : 0 ≤ K.prob ω :=
  mul_nonneg (by norm_num) (prod_nonneg fun j _ => K.w_nonneg _)

lemma sum_prob : ∑ ω : Sample d s, K.prob ω = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [prob, ← mul_sum, sum_prod_weights, K.w_sum, one_pow, Fintype.sum_bool]
  norm_num

/-- Expectation over the colour and the apices. -/
noncomputable def E (F : Sample d s → ℝ) : ℝ := ∑ ω, K.prob ω * F ω

/-- The expectation splits into the two colours. -/
lemma E_eq_colours (F : Sample d s → ℝ) :
    K.E F = (∑ z, (∏ j, K.w (z j)) * F (true, z) + ∑ z, (∏ j, K.w (z j)) * F (false, z)) / 2 := by
  rw [E, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [prob, add_div, sum_div]
  congr 1 <;> refine sum_congr rfl fun z _ => by ring

/-! ### `def:conditional` -/

/-- `h(x) = ∏ⱼ S_σ(zⱼ, x)`. -/
def condH (ω : Sample d s) (x : Fin d) : ℝ := ∏ j, K.S (colour ω.1) (ω.2 j) x

/-- `D = E_x h(x)`. -/
def condD (ω : Sample d s) : ℝ := ∑ x, K.w x * K.condH ω x

/-- `A_in(x) = E_y S_σ(x, y) h(y)`. -/
def condA (ω : Sample d s) (x : Fin d) : ℝ := ∑ y, K.w y * K.S (colour ω.1) x y * K.condH ω y

/-- `N = E_x h(x) A_in(x)`. -/
def condN (ω : Sample d s) : ℝ := ∑ x, K.w x * K.condH ω x * K.condA ω x

/-- `Π = E_x h(x) A_in(x)²`. -/
def condPi (ω : Sample d s) : ℝ := ∑ x, K.w x * K.condH ω x * K.condA ω x ^ 2

/-- `Q = N / D` (`0` when `D = 0`). -/
noncomputable def condQ (ω : Sample d s) : ℝ := K.condN ω / K.condD ω

/-- `Q♯ = √(Π / D)` (`0` when `D = 0`). -/
noncomputable def condQs (ω : Sample d s) : ℝ := Real.sqrt (K.condPi ω / K.condD ω)

/-- The conditional weights `wₓ h(x)`. -/
def condW (ω : Sample d s) (x : Fin d) : ℝ := K.w x * K.condH ω x

/-- `B`, the Euclidean matrix of `M_{√h} T_{S_σ} M_{√h}`. -/
noncomputable def condB (ω : Sample d s) : Matrix (Fin d) (Fin d) ℝ :=
  hostMatrix (K.condW ω) (K.S (colour ω.1))

/-! ### `lem:conditional-bounds` -/

variable (ω : Sample d s)

lemma S_colour_nonneg (x y : Fin d) : 0 ≤ K.S (colour ω.1) x y :=
  K.S_nonneg (colour_cases _) x y

lemma S_colour_le_two (x y : Fin d) : K.S (colour ω.1) x y ≤ 2 :=
  K.S_le_two (colour_cases _) x y

lemma condH_nonneg (x : Fin d) : 0 ≤ K.condH ω x :=
  prod_nonneg fun _ _ => K.S_colour_nonneg ω _ _

lemma condH_le (x : Fin d) : K.condH ω x ≤ 2 ^ s := by
  calc K.condH ω x ≤ ∏ _j : Fin s, (2 : ℝ) :=
        prod_le_prod (fun _ _ => K.S_colour_nonneg ω _ _) fun _ _ => K.S_colour_le_two ω _ _
    _ = 2 ^ s := by simp

lemma condW_nonneg (x : Fin d) : 0 ≤ K.condW ω x := mul_nonneg (K.w_nonneg x) (K.condH_nonneg ω x)

lemma condD_nonneg : 0 ≤ K.condD ω := sum_nonneg fun x _ => K.condW_nonneg ω x

lemma condD_le : K.condD ω ≤ 2 ^ s := by
  calc K.condD ω ≤ ∑ x, K.w x * 2 ^ s :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (K.condH_le ω x) (K.w_nonneg x)
    _ = 2 ^ s := by rw [← sum_mul, K.w_sum, one_mul]

lemma condA_nonneg (x : Fin d) : 0 ≤ K.condA ω x :=
  sum_nonneg fun y _ => mul_nonneg (mul_nonneg (K.w_nonneg y) (K.S_colour_nonneg ω _ _))
    (K.condH_nonneg ω y)

lemma condA_le (x : Fin d) : K.condA ω x ≤ 2 * K.condD ω := by
  rw [condD, mul_sum]
  refine sum_le_sum fun y _ => ?_
  have := K.S_colour_le_two ω x y
  have h0 := K.condH_nonneg ω y
  have hw := K.w_nonneg y
  nlinarith [mul_nonneg hw h0]

lemma condN_nonneg : 0 ≤ K.condN ω :=
  sum_nonneg fun x _ => mul_nonneg (K.condW_nonneg ω x) (K.condA_nonneg ω x)

lemma condPi_nonneg : 0 ≤ K.condPi ω :=
  sum_nonneg fun x _ => mul_nonneg (K.condW_nonneg ω x) (sq_nonneg _)

lemma condPi_le : K.condPi ω ≤ 4 * K.condD ω ^ 3 := by
  have hD := K.condD_nonneg ω
  calc K.condPi ω ≤ ∑ x, K.condW ω x * (2 * K.condD ω) ^ 2 := by
        refine sum_le_sum fun x _ => ?_
        rw [show K.w x * K.condH ω x = K.condW ω x from rfl]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (K.condA_nonneg ω x) (K.condA_le ω x) 2) (K.condW_nonneg ω x)
    _ = 4 * K.condD ω ^ 3 := by rw [← sum_mul, show ∑ x, K.condW ω x = K.condD ω from rfl]; ring

/-- If `D = 0`, then `h` vanishes at every point of positive mass. -/
lemma condW_eq_zero_of_condD (hD : K.condD ω = 0) (x : Fin d) : K.condW ω x = 0 :=
  (sum_eq_zero_iff_of_nonneg fun y _ => K.condW_nonneg ω y).mp hD x (mem_univ x)

lemma condN_eq_zero_of_condD (hD : K.condD ω = 0) : K.condN ω = 0 := by
  refine sum_eq_zero fun x _ => ?_
  rw [show K.w x * K.condH ω x = K.condW ω x from rfl, K.condW_eq_zero_of_condD ω hD x, zero_mul]

lemma condPi_eq_zero_of_condD (hD : K.condD ω = 0) : K.condPi ω = 0 := by
  refine sum_eq_zero fun x _ => ?_
  rw [show K.w x * K.condH ω x = K.condW ω x from rfl, K.condW_eq_zero_of_condD ω hD x, zero_mul]

/-- Cauchy–Schwarz for the conditional weights: `N² ≤ D Π`. -/
lemma condN_sq_le : K.condN ω ^ 2 ≤ K.condD ω * K.condPi ω :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul univ (fun x _ => K.condW_nonneg ω x)
    (fun x _ => mul_nonneg (K.condW_nonneg ω x) (sq_nonneg _))
    (fun x _ => le_of_eq (by ring))

lemma condQs_nonneg : 0 ≤ K.condQs ω := Real.sqrt_nonneg _

lemma condQ_nonneg : 0 ≤ K.condQ ω := div_nonneg (K.condN_nonneg ω) (K.condD_nonneg ω)

/-- `Q ≤ Q♯`. -/
lemma condQ_le_condQs : K.condQ ω ≤ K.condQs ω := by
  rcases (K.condD_nonneg ω).eq_or_lt with hD | hD
  · rw [condQ, condQs, ← hD, div_zero, div_zero, Real.sqrt_zero]
  · refine Real.le_sqrt_of_sq_le ?_
    rw [condQ, div_pow, div_le_div_iff₀ (by positivity) hD]
    nlinarith [K.condN_sq_le ω]

/-- `D (Q♯)² = Π`. -/
lemma condD_mul_condQs_sq : K.condD ω * K.condQs ω ^ 2 = K.condPi ω := by
  rcases (K.condD_nonneg ω).eq_or_lt with hD | hD
  · rw [← hD, zero_mul, K.condPi_eq_zero_of_condD ω hD.symm]
  · rw [condQs, Real.sq_sqrt (div_nonneg (K.condPi_nonneg ω) hD.le)]
    field_simp

/-- `Q♯ ≤ 2 D ≤ 2^{s+1}`. -/
lemma condQs_le : K.condQs ω ≤ 2 * K.condD ω := by
  have hD0 := K.condD_nonneg ω
  rcases hD0.eq_or_lt with hD | hD
  · rw [condQs, ← hD, div_zero, Real.sqrt_zero, mul_zero]
  · rw [condQs]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hD]
    nlinarith [K.condPi_le ω]

/-! ### `lem:conditional-vector` -/

/-- The conditional unit vector `gₓ = √(wₓ hₓ) / √D` in Euclidean coordinates. -/
noncomputable def condVec (ω : Sample d s) (x : Fin d) : ℝ :=
  Real.sqrt (K.condW ω x) / Real.sqrt (K.condD ω)

lemma condVec_dot_self (hD : 0 < K.condD ω) : K.condVec ω ⬝ᵥ K.condVec ω = 1 := by
  simp only [dotProduct, condVec, div_mul_div_comm,
    Real.mul_self_sqrt (K.condW_nonneg ω _), Real.mul_self_sqrt hD.le, ← sum_div]
  exact div_self hD.ne'

lemma condB_mulVec_condVec (x : Fin d) :
    (K.condB ω *ᵥ K.condVec ω) x = Real.sqrt (K.condW ω x) * K.condA ω x / Real.sqrt (K.condD ω) := by
  simp only [mulVec, dotProduct, condB, hostMatrix_apply, condVec, condA, mul_sum, sum_div]
  refine sum_congr rfl fun y _ => ?_
  have hy : Real.sqrt (K.condW ω y) * Real.sqrt (K.condW ω y) = K.w y * K.condH ω y :=
    Real.mul_self_sqrt (K.condW_nonneg ω y)
  calc K.S (colour ω.1) x y * Real.sqrt (K.condW ω x) * Real.sqrt (K.condW ω y) *
        (Real.sqrt (K.condW ω y) / Real.sqrt (K.condD ω))
      = Real.sqrt (K.condW ω x) *
          (K.S (colour ω.1) x y * (Real.sqrt (K.condW ω y) * Real.sqrt (K.condW ω y))) /
          Real.sqrt (K.condD ω) := by ring
    _ = Real.sqrt (K.condW ω x) * (K.w y * K.S (colour ω.1) x y * K.condH ω y) /
          Real.sqrt (K.condD ω) := by rw [hy]; ring

/-- `‖B g‖² = Π / D = (Q♯)²`. -/
lemma condB_condVec_normSq :
    (K.condB ω *ᵥ K.condVec ω) ⬝ᵥ (K.condB ω *ᵥ K.condVec ω) = K.condQs ω ^ 2 := by
  have hPD : 0 ≤ K.condPi ω / K.condD ω := div_nonneg (K.condPi_nonneg ω) (K.condD_nonneg ω)
  rw [condQs, Real.sq_sqrt hPD]
  simp only [dotProduct, condB_mulVec_condVec, condPi, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [div_mul_div_comm, Real.mul_self_sqrt (K.condD_nonneg ω)]
  have hx := Real.mul_self_sqrt (K.condW_nonneg ω x)
  calc Real.sqrt (K.condW ω x) * K.condA ω x * (Real.sqrt (K.condW ω x) * K.condA ω x) /
        K.condD ω
      = (Real.sqrt (K.condW ω x) * Real.sqrt (K.condW ω x)) * K.condA ω x ^ 2 / K.condD ω := by
        ring
    _ = K.w x * K.condH ω x * K.condA ω x ^ 2 / K.condD ω := by rw [hx]; rfl

/-- `⟨g, B g⟩ = Q`. -/
lemma condVec_rayleigh : K.condVec ω ⬝ᵥ (K.condB ω *ᵥ K.condVec ω) = K.condQ ω := by
  simp only [dotProduct, condB_mulVec_condVec, condVec, condQ, condN, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [div_mul_div_comm, Real.mul_self_sqrt (K.condD_nonneg ω)]
  have hx := Real.mul_self_sqrt (K.condW_nonneg ω x)
  calc Real.sqrt (K.condW ω x) * (Real.sqrt (K.condW ω x) * K.condA ω x) / K.condD ω
      = (Real.sqrt (K.condW ω x) * Real.sqrt (K.condW ω x)) * K.condA ω x / K.condD ω := by ring
    _ = K.w x * K.condH ω x * K.condA ω x / K.condD ω := by rw [hx]; rfl

lemma condB_isHermitian : (K.condB ω).IsHermitian := hostMatrix_isHermitian _ (K.S_symm _)

end FiniteKernel

end ApicesCommonness
