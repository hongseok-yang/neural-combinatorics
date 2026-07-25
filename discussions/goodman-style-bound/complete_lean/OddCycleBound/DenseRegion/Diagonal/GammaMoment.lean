/-
# Dense region (Phase D) — the gamma expectation and its moments (paper §4, lines 1473–1521)

Foundation for the Laplace–gamma smoothing (`lem:dense-gamma-smoothing`) and the moment
inequality (`lem:gamma-moment`).  We work with the **unnormalized** gamma functional
`gExp r f = ∫_{(0,∞)} y^{r-1} e^{-y} f(y) dy = Γ(r)·E[f(Y)]`, `Y ~ Γ(r,1)`.  Sign facts and
inequalities transfer to the normalized expectation because `Γ(r) = (r-1)! > 0`.

This file proves the analytic substrate:
* `intPowExp` : `∫_{(0,∞)} y^k e^{-y} = k!`  (the one special-function input, from `Real.Gamma`);
* `gExp_integrableOn`, `gExp_monomial`, and the algebra of `gExp` (const-mul, add, finset sum,
  nonnegativity on nonnegative integrands).

The moment inequality `lem:gamma-moment` and the shifted-gamma positivity `prop:dense-gamma-positive`
build on this substrate.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open MeasureTheory Set Real
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/-- **The base gamma integral.**  `∫_{(0,∞)} y^k e^{-y} dy = k!`, via `Real.Gamma`. -/
lemma intPowExp (k : ℕ) :
    ∫ y in Set.Ioi (0 : ℝ), y ^ k * Real.exp (-y) = (Nat.factorial k : ℝ) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := 1) (by positivity) one_pos
  rw [one_div, inv_one, Real.one_rpow, one_mul, show (k : ℝ) + 1 - 1 = (k : ℝ) from by ring,
      Real.Gamma_nat_eq_factorial] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  rw [Set.mem_Ioi] at hy
  rw [Real.rpow_natCast, one_mul]

/-- **Scaled base gamma integral (Laplace kernel).**  For `w > 0` and `m ≥ 1`,
`∫_{(0,∞)} t^{m-1} e^{-w t} dt = (m-1)! / w^m`.  This is the Laplace representation of `w^{-m}`
used by the gamma-smoothing step (`lem:dense-gamma-smoothing`). -/
lemma intPowExpMul (m : ℕ) (hm : 1 ≤ m) (w : ℝ) (hw : 0 < w) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (m - 1) * Real.exp (-(w * t))
      = (Nat.factorial (m - 1) : ℝ) / w ^ m := by
  have hΓ : Real.Gamma (m : ℝ) = (Nat.factorial (m - 1) : ℝ) := by
    rw [show (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 from by rw [Nat.cast_sub hm]; ring,
      Real.Gamma_nat_eq_factorial]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ)) (r := w) (by positivity) hw
  have hRHS : (1 / w) ^ (m : ℝ) * Real.Gamma (m : ℝ) = (Nat.factorial (m - 1) : ℝ) / w ^ m := by
    rw [hΓ, Real.rpow_natCast, div_pow, one_pow]; ring
  rw [hRHS] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [Set.mem_Ioi] at ht
  rw [show (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) from by rw [Nat.cast_sub hm, Nat.cast_one],
    Real.rpow_natCast]

/-- The **unnormalized gamma functional** `gExp r f = ∫_{(0,∞)} y^{r-1} e^{-y} f(y) dy`.
Equal to `Γ(r)·E[f(Y)]` for `Y ~ Γ(r,1)`; used only on polynomials `f`. -/
noncomputable def gExp (r : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1) * Real.exp (-y) * f y

/-- Integrability of `y^{r-1} e^{-y} · y^i` on `(0,∞)` (exponential decay beats the polynomial). -/
lemma gExp_integrableOn (r i : ℕ) :
    IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * y ^ i) (Set.Ioi (0 : ℝ)) := by
  have hconv := Real.GammaIntegral_convergent (s := ((r - 1 + i : ℕ) : ℝ) + 1) (by positivity)
  refine hconv.congr_fun (fun y hy => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hy
  have he : ((r - 1 + i : ℕ) : ℝ) + 1 - 1 = ((r - 1 + i : ℕ) : ℝ) := by ring
  simp only [he, Real.rpow_natCast, pow_add]
  ring

/-- `gExp r` on a monomial: `gExp r (y^i) = (r-1+i)!` (`= Γ(r+i)`). -/
lemma gExp_monomial (r i : ℕ) :
    gExp r (fun y => y ^ i) = (Nat.factorial (r - 1 + i) : ℝ) := by
  unfold gExp
  rw [show (∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1) * Real.exp (-y) * y ^ i)
        = ∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1 + i) * Real.exp (-y) from ?_, intPowExp]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  rw [pow_add]; ring

/-- **Nonnegativity.**  If `f ≥ 0` on `(0,∞)` then `gExp r f ≥ 0` (the weight is nonnegative). -/
lemma gExp_nonneg (r : ℕ) (f : ℝ → ℝ) (hf : ∀ y ∈ Set.Ioi (0 : ℝ), 0 ≤ f y) :
    0 ≤ gExp r f := by
  refine setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  rw [Set.mem_Ioi] at hy
  exact mul_nonneg (mul_nonneg (pow_nonneg hy.le _) (Real.exp_pos _).le) (hf y (Set.mem_Ioi.mpr hy))

/-- **Homogeneity.**  `gExp r (c·f) = c · gExp r f`. -/
lemma gExp_const_mul (r : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    gExp r (fun y => c * f y) = c * gExp r f := by
  unfold gExp
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  ring

/-- Integrability of `y^{r-1} e^{-y} · (a y + b)^k` on `(0,∞)` (a polynomial times the weight). -/
lemma gExp_affinePow_integrableOn (r k : ℕ) (a b : ℝ) :
    IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * (a * y + b) ^ k) (Set.Ioi (0 : ℝ)) := by
  have hrw : (fun y => y ^ (r - 1) * Real.exp (-y) * (a * y + b) ^ k)
      = fun y => ∑ i ∈ Finset.range (k + 1),
          ((Nat.choose k i : ℝ) * a ^ i * b ^ (k - i)) * (y ^ (r - 1) * Real.exp (-y) * y ^ i) := by
    funext y
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_pow]; ring
  rw [hrw]
  exact integrable_finsetSum _ (fun i _ => (gExp_integrableOn r i).const_mul _)

/-- **Additivity** (given integrability of both weighted integrands). -/
lemma gExp_add (r : ℕ) (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * f y) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * g y) (Set.Ioi (0 : ℝ))) :
    gExp r (fun y => f y + g y) = gExp r f + gExp r g := by
  unfold gExp
  rw [← MeasureTheory.integral_add hf hg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  ring

/-- **Subtractivity** (given integrability of both weighted integrands). -/
lemma gExp_sub (r : ℕ) (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * f y) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * g y) (Set.Ioi (0 : ℝ))) :
    gExp r (fun y => f y - g y) = gExp r f - gExp r g := by
  unfold gExp
  rw [← MeasureTheory.integral_sub hf hg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  ring

/-- **Finite additivity** (given integrability of each weighted summand). -/
lemma gExp_finset_sum {ι : Type*} (r : ℕ) (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * F i y) (Set.Ioi (0 : ℝ))) :
    gExp r (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, gExp r (F i) := by
  unfold gExp
  rw [← MeasureTheory.integral_finsetSum s hF]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  rw [Finset.mul_sum]

end OddCycleBound.DenseRegion
