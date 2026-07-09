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

/-! ### The Dirichlet-mean expectation `dirExp`

`dirExp L f = E_{Θ~Dir(1^{|L|})}[f(Σ Θᵢ·Lᵢ)]`, realised as an iterated 1-D integral by peeling the
first Dirichlet coordinate `Θ₁ ~ Beta(1, |L|−1)` (density `(|L|−1)(1−t)^{|L|−2}`) and conditioning:
`Σ Θᵢ Lᵢ = t·L₀ + (1−t)·Σ Θ'ⱼ L'ⱼ`.  Used only on polynomials `f`; `dirExp [] := 0` is never reached
(the mixture uses lists of length `r ≥ 1`). -/
noncomputable def dirExp : List ℝ → (ℝ → ℝ) → ℝ
  | [], _ => 0
  | [a], f => f a
  | (a :: b :: L), f =>
      ∫ t in (0:ℝ)..1,
        ((b :: L).length : ℝ) * (1 - t) ^ ((b :: L).length - 1)
          * dirExp (b :: L) (fun x => f (t * a + (1 - t) * x))

/-- **Positivity of `dirExp` (P1).**  If `f ≥ 0` on `[a,b]` and every entry of `L` lies in `[a,b]`,
then `dirExp L f ≥ 0` — the Dirichlet mean `Σ Θᵢ Lᵢ` stays in `[a,b]` (convexity), so the integrand is
pointwise nonnegative. -/
lemma dirExp_nonneg : ∀ (L : List ℝ) (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
    (∀ x ∈ Set.Icc a b, 0 ≤ f x) → (∀ x ∈ L, x ∈ Set.Icc a b) → 0 ≤ dirExp L f
  | [], f, a, b, _, _, _ => by simp [dirExp]
  | [c], f, a, b, _, hf, hL => by
      rw [dirExp]; exact hf c (hL c (by simp))
  | (c :: d :: L), f, a, b, hab, hf, hL => by
      rw [dirExp]
      apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
      intro t ht
      have h0t : (0:ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hc : c ∈ Set.Icc a b := hL c (by simp)
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
      · refine dirExp_nonneg (d :: L) _ a b hab ?_
          (fun x hx => hL x (List.mem_cons_of_mem c hx))
        intro x hx
        exact hf _ ⟨by nlinarith [hc.1, hx.1], by nlinarith [hc.2, hx.2]⟩

/-! ### The positivity transfer `cor:diagonal`, reduced to the mixture bridge

The unconditional engine (`dirExp_nonneg`) reduces `cor:diagonal` to the single **mixture bridge**
`multiKernel m r q L = dirExp L (diagKernel m r q ·)`.  That bridge is the remaining analytic
obligation and combines two facts, both still to formalise:

* **`dirExp` is linear** in its function argument over finite sums of monomials (so it commutes with
  `diagKernel_expand`'s `Σⱼ kerB_j·C(j+r−1,r−1)·(·)ʲ`);
* the **Dirichlet moment formula `eq:dir-moment`**  `dirExp L (·ʲ) = h_j(L)/C(j+|L|−1,|L|−1)`  (proved by
  induction on `L` via `beta_nat`), which then cancels the `C(j+r−1,r−1)` factor against
  `multiKernel_expand`'s `Σⱼ kerB_j·h_j(L)`.

Both are integrability-carrying inductions on `L`; they are the next Stage-2 target. -/
theorem multiKernel_nonneg_of_diag {m r : ℕ} (q : ℝ) (L : List ℝ)
    (hbridge : multiKernel m r q L = dirExp L (fun x => diagKernel m r q x))
    (hdiag : ∀ ℓ ∈ Set.Icc (-(1:ℝ) / 2) (1 / 2), 0 ≤ diagKernel m r q ℓ)
    (hL : ∀ x ∈ L, x ∈ Set.Icc (-(1:ℝ) / 2) (1 / 2)) :
    0 ≤ multiKernel m r q L := by
  rw [hbridge]
  exact dirExp_nonneg L _ (-(1:ℝ) / 2) (1 / 2) (by norm_num) hdiag hL

/-! ### Linearity of `dirExp` (the mixture bridge, part 1)

`dirExp L` is linear in its function argument; the only obstacle is integrability at each recursion
step, which we discharge via a parametric-continuity lemma: `w ↦ dirExp L (F w ·)` is continuous
whenever `F` is jointly continuous.  The recursion grows the parameter space by `×ℝ`, so the lemma is
stated for an arbitrary parameter type. -/

/-- **Parametric continuity of `dirExp`.**  For jointly-continuous `F : X → ℝ → ℝ`, the map
`w ↦ dirExp L (F w ·)` is continuous.  (Supplies interval-integrability in the linearity induction.) -/
lemma dirExp_param_continuous : ∀ (L : List ℝ) {X : Type} [TopologicalSpace X] (F : X → ℝ → ℝ),
    Continuous (Function.uncurry F) → Continuous (fun w => dirExp L (fun x => F w x))
  | [], _, _, _, _ => by simp only [dirExp]; exact continuous_const
  | [c], X, _, F, hF => by
      simp only [dirExp]
      exact hF.comp (show Continuous (fun w : X => (w, c)) from by fun_prop)
  | (c :: d :: L), X, _, F, hF => by
      simp only [dirExp]
      have hG : Continuous (Function.uncurry
          (fun (p : X × ℝ) (x : ℝ) => F p.1 (p.2 * c + (1 - p.2) * x))) :=
        hF.comp (show Continuous (fun q : (X × ℝ) × ℝ =>
          (q.1.1, q.1.2 * c + (1 - q.1.2) * q.2)) from by fun_prop)
      have hrec := dirExp_param_continuous (d :: L)
        (fun (p : X × ℝ) (x : ℝ) => F p.1 (p.2 * c + (1 - p.2) * x)) hG
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ 0 1
      have hρ : Continuous (fun p : X × ℝ =>
          ((d :: L).length : ℝ) * (1 - p.2) ^ ((d :: L).length - 1)) := by fun_prop
      exact hρ.mul hrec

/-- Controlled one-step unfolding of `dirExp` at a `≥2` list. -/
lemma dirExp_cons_cons (c d : ℝ) (L : List ℝ) (f : ℝ → ℝ) :
    dirExp (c :: d :: L) f
      = ∫ t in (0:ℝ)..1, ((d :: L).length : ℝ) * (1 - t) ^ ((d :: L).length - 1)
          * dirExp (d :: L) (fun x => f (t * c + (1 - t) * x)) := rfl

/-- Interval-integrability of the `dirExp` recursion integrand for continuous `f`. -/
lemma dirExp_intervalIntegrable (T : List ℝ) (c : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    IntervalIntegrable
      (fun t => (T.length : ℝ) * (1 - t) ^ (T.length - 1) * dirExp T (fun x => f (t * c + (1 - t) * x)))
      volume 0 1 := by
  have hpc : Continuous (fun t => dirExp T (fun x => f (t * c + (1 - t) * x))) :=
    dirExp_param_continuous T (fun (t : ℝ) (x : ℝ) => f (t * c + (1 - t) * x)) (hf.comp (by fun_prop))
  exact Continuous.intervalIntegrable
    ((by fun_prop : Continuous (fun t : ℝ => (T.length : ℝ) * (1 - t) ^ (T.length - 1))).mul hpc) _ _

/-- `dirExp L 0 = 0`. -/
lemma dirExp_zero : ∀ (L : List ℝ), dirExp L (fun _ => 0) = 0
  | [] => rfl
  | [_] => rfl
  | (c :: d :: L) => by
      rw [dirExp_cons_cons]
      simp only [dirExp_zero (d :: L), mul_zero, intervalIntegral.integral_zero]

/-- `dirExp` is homogeneous in its function argument. -/
lemma dirExp_smul : ∀ (L : List ℝ) (a : ℝ) (f : ℝ → ℝ),
    dirExp L (fun x => a * f x) = a * dirExp L f
  | [], a, f => by simp [dirExp]
  | [c], a, f => by simp [dirExp]
  | (c :: d :: L), a, f => by
      rw [dirExp_cons_cons, dirExp_cons_cons, ← intervalIntegral.integral_const_mul]
      refine integral_congr fun t _ => ?_
      rw [dirExp_smul (d :: L) a (fun x => f (t * c + (1 - t) * x))]
      ring

/-- `dirExp` is additive in its (continuous) function argument. -/
lemma dirExp_add : ∀ (L : List ℝ) (f g : ℝ → ℝ), Continuous f → Continuous g →
    dirExp L (fun x => f x + g x) = dirExp L f + dirExp L g
  | [], f, g, _, _ => by simp [dirExp]
  | [c], f, g, _, _ => by simp [dirExp]
  | (c :: d :: L), f, g, hf, hg => by
      rw [dirExp_cons_cons, dirExp_cons_cons, dirExp_cons_cons,
        ← intervalIntegral.integral_add
          (dirExp_intervalIntegrable (d :: L) c f hf) (dirExp_intervalIntegrable (d :: L) c g hg)]
      refine integral_congr fun t _ => ?_
      rw [dirExp_add (d :: L) (fun x => f (t * c + (1 - t) * x)) (fun x => g (t * c + (1 - t) * x))
        (by fun_prop) (by fun_prop)]
      ring

/-- `dirExp` commutes with finite sums of continuous functions. -/
lemma dirExp_finset_sum {ι : Type*} (L : List ℝ) (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i, Continuous (F i)) :
    dirExp L (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, dirExp L (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Finset.sum_empty, dirExp_zero]
  | @insert a s ha ih =>
      have hcs : Continuous (fun x => ∑ i ∈ s, F i x) := continuous_finset_sum s fun i _ => hF i
      rw [show (fun x => ∑ i ∈ insert a s, F i x) = (fun x => F a x + ∑ i ∈ s, F i x) from by
            funext x; rw [Finset.sum_insert ha],
        dirExp_add L (F a) (fun x => ∑ i ∈ s, F i x) (hF a) hcs, ih, Finset.sum_insert ha]

end OddCycleBound.HighDensity
