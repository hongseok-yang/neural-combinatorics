/-
# High-density theorem — Milestone M0a: the finite-rank two-sided identity

This file makes the **cheap, decisive go/no-go check** for the moment route of the high-density
odd-cycle theorem (`HIGH_DENSITY_FORMALIZATION_PLAN.md` §0, M0a): the *finite-rank* form of the
two-sided spectral-shift identity (`paper_new.tex` Thm `thm:two-sided`), which is **pure block-matrix
algebra with no limit**.

Setup (finite rank).  Fix a finite index set `ι` (the eigen/coordinate directions of the compression
`A`).  With hub scalar `q`, hub–body coupling vector `g : ι → ℝ`, and body block `A : Matrix ι ι ℝ`,
form the block operators on `Option ι` (`none` = the constant/hub direction `𝟙`):

```
        T_U = [[ q ,  gᵀ ],          M = [[ p ,  gᵀ ],        p = 1 - q.
               [ g ,  A  ]]                [ g , -A  ]]
```

`M` is the sign-flip conjugate of `T_W = J − T_U` on `𝟙^⊥`, hence isospectral to `T_W`
(`paper_new.tex` §`sec:two-sided`), so `t(C_m,W) = Tr(M^m)` and `t(C_m,U) = Tr(T_U^m)` in finite rank.
The paper's identity is `Tr(M^m) + Tr(T_U^m) = p^m + q^m + S_m`.

**What M0a checks.**  For odd `m`, the `det(I ± zA)` factors cancel and everything `A`-dependent drops
out of the *sum*, leaving `p^m + q^m + S_m` with `S_m` depending only on `p, q` and the moments
`s_j = ⟨g, Aʲ g⟩`.  We verify this **directly** for the first nontrivial odd length `m = 3`, where
`S_3 = 3 s_0 = 3‖g‖²`.  The decisive structural fact — *every term containing `A` cancels between the
two sides because it carries an odd number of `A`-factors and `M` flips the sign of `A`* — is exactly
what the `m = 3` computation exhibits (no symmetry of `A` is even needed at this length).

This validates the algebra of the moment route "for real" (plan §0: "if it holds the route is
validated; if it fights, the algebra is wrong and you learn it in days") before the heavy
general-`m` `PowerSeries`/log-det bridge (M0b) is built.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace OddCycleBound.DenseRegion

open Matrix
open scoped BigOperators

variable {ι : Type*}

/-- The finite-rank block operator `[[q, gᵀ], [g, A]]` on `Option ι`, with the hub direction indexed
by `none` and the body directions by `some i`.  Cf. `paper_new.tex` §`sec:setup2`. -/
def blockOp (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix (Option ι) (Option ι) ℝ
  | none,   none   => q
  | none,   some j => g j
  | some i, none   => g i
  | some i, some j => A i j

@[simp] lemma blockOp_none_none (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    blockOp q g A none none = q := rfl

@[simp] lemma blockOp_none_some (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (j : ι) :
    blockOp q g A none (some j) = g j := rfl

@[simp] lemma blockOp_some_none (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (i : ι) :
    blockOp q g A (some i) none = g i := rfl

@[simp] lemma blockOp_some_some (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (i j : ι) :
    blockOp q g A (some i) (some j) = A i j := rfl

variable [Fintype ι] [DecidableEq ι]

/-- Trace of a cube, written as an explicit triple sum over the index set. -/
lemma trace_pow3_eq (X : Matrix (Option ι) (Option ι) ℝ) :
    trace (X ^ 3) = ∑ x, ∑ z, ∑ y, X x y * X y z * X z x := by
  have hx : X ^ 3 = X * X * X := by
    rw [pow_succ, pow_succ, pow_one]
  rw [hx]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]

/-- Trace of a fifth power, as an explicit five-fold sum (the shape used for the length-5 identity). -/
lemma trace_pow5_eq (X : Matrix (Option ι) (Option ι) ℝ) :
    trace (X ^ 5) = ∑ a, ∑ e, ∑ d, ∑ c, ∑ b, X a b * X b c * X c d * X d e * X e a := by
  have hx : X ^ 5 = X * X * X * X * X := by
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  rw [hx]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]

/-- **Milestone M0a (length 3).**  The finite-rank two-sided spectral-shift identity at `m = 3`
(`paper_new.tex` Thm `thm:two-sided`, `S_3 = 3 s_0`).  Every `A`-dependent term carries an odd number
of `A`-factors and hence cancels between the two block operators (`M` flips the sign of `A`), leaving
`p^3 + q^3 + 3‖g‖²`.  No symmetry of `A` is needed at this length. -/
theorem two_sided_finrank_three (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    trace (blockOp q g A ^ 3) + trace (blockOp (1 - q) g (-A) ^ 3)
      = q ^ 3 + (1 - q) ^ 3 + 3 * ∑ i, g i ^ 2 := by
  rw [trace_pow3_eq, trace_pow3_eq]
  simp only [Fintype.sum_option, blockOp_none_none, blockOp_none_some, blockOp_some_none,
    blockOp_some_some, Matrix.neg_apply]
  -- Split the nested `∑ (a + b)` and push every negation outside its sum, so each `A`-term of the
  -- `M`-block becomes the exact negative of the matching `A`-term of the `T_U`-block.
  simp only [Finset.sum_add_distrib, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib]
  -- The six quadratic `g`-sums (three with coefficient `q`, three with `1 - q`) collapse to `3‖g‖²`.
  have hg : (∑ x, g x * g x * q) + (∑ x, q * g x * g x) + (∑ x, g x * q * g x)
      + (∑ x, g x * g x * (1 - q)) + (∑ x, (1 - q) * g x * g x) + (∑ x, g x * (1 - q) * g x)
      = 3 * ∑ i, g i ^ 2 := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  -- All `A`-terms cancel in pairs; `hg` supplies the surviving quadratic contribution.
  linear_combination hg

/-! ### Finite-rank moments and their parity

The general-`m` identity (`paper_new.tex` `thm:two-sided`) is governed by the compression moments
`s_j = ⟨g, Aʲ g⟩` (`paper_new.tex` §`sec:setup2`).  We record the finite-rank moment and the single
fact that powers the odd-`m` cancellation: replacing `A` by `−A` (the `T_U → M` block move) multiplies
`s_j` by `(−1)ʲ`.  Odd moments are therefore antisymmetric and drop out of the two-sided *sum*, whereas
even moments survive — the mechanism that makes `S_3 = 3s_0` `A`-independent but `S_5` depend on
`s_1, s_2`. -/

/-- The finite-rank moment `s_j = ⟨g, Aʲ g⟩` in the compression chart. -/
noncomputable def frMoment (g : ι → ℝ) (A : Matrix ι ι ℝ) (j : ℕ) : ℝ :=
  ∑ i, ∑ k, g i * (A ^ j) i k * g k

/-- `s_0 = ‖g‖²`. -/
lemma frMoment_zero (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    frMoment g A 0 = ∑ i, g i ^ 2 := by
  unfold frMoment
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pow_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [pow_two]

/-- `s_1 = ⟨g, A g⟩` in expanded form (the shape produced by a trace expansion). -/
lemma frMoment_one (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    frMoment g A 1 = ∑ i, ∑ j, g i * A i j * g j := by
  simp only [frMoment, pow_one]

/-- `s_2 = ⟨g, A² g⟩` in expanded triple-sum form (the shape produced by a trace expansion). -/
lemma frMoment_two (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    frMoment g A 2 = ∑ i, ∑ j, ∑ k, g i * A i j * A j k * g k := by
  simp only [frMoment, pow_two, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  conv_lhs => rw [Finset.sum_comm]

/-- **Moment parity.**  `s_j(−A) = (−1)ʲ s_j(A)`: the sign flip of the compression multiplies the
`j`-th moment by `(−1)ʲ`.  This drives the odd-`m` cancellation in the two-sided identity. -/
lemma frMoment_neg (g : ι → ℝ) (A : Matrix ι ι ℝ) (j : ℕ) :
    frMoment g (-A) j = (-1 : ℝ) ^ j * frMoment g A j := by
  have hpow : (-A) ^ j = ((-1 : ℝ) ^ j) • A ^ j := by
    rw [← neg_one_smul ℝ A, smul_pow]
  unfold frMoment
  rw [hpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply]
  ring

/-- **Pure-block trace parity.**  `Tr((−A)^m) = (−1)^m Tr(A^m)`.  This is the `Tr(A^m)` contribution
to the two-sided identity — equivalently the `det(I ± zA)` factors of `paper_new.tex` §`sec:two-sided`
— and the second cancellation pillar alongside `frMoment_neg`. -/
lemma trace_neg_pow (A : Matrix ι ι ℝ) (m : ℕ) :
    trace ((-A) ^ m) = (-1 : ℝ) ^ m * trace (A ^ m) := by
  have hpow : (-A) ^ m = ((-1 : ℝ) ^ m) • A ^ m := by
    rw [← neg_one_smul ℝ A, smul_pow]
  rw [hpow, trace_smul, smul_eq_mul]

/-- Odd powers: the pure-block trace is antisymmetric, `Tr((−A)^m) = −Tr(A^m)`, so it cancels in the
two-sided *sum* — the mechanism behind the vanishing of `Tr(A^m)` for odd `m`. -/
lemma trace_neg_pow_odd {m : ℕ} (hm : Odd m) (A : Matrix ι ι ℝ) :
    trace ((-A) ^ m) = - trace (A ^ m) := by
  rw [trace_neg_pow, hm.neg_one_pow, neg_one_mul]

/-- Odd moments are antisymmetric, `s_m(−A) = −s_m(A)`, hence cancel in the two-sided sum. -/
lemma frMoment_neg_odd {m : ℕ} (hm : Odd m) (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    frMoment g (-A) m = - frMoment g A m := by
  rw [frMoment_neg, hm.neg_one_pow, neg_one_mul]

/-- The length-3 two-sided identity in moment form: the surviving term is exactly `3 s_0`
(`paper_new.tex` `S_3 = 3 s_0`). -/
theorem two_sided_finrank_three_moment (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    trace (blockOp q g A ^ 3) + trace (blockOp (1 - q) g (-A) ^ 3)
      = q ^ 3 + (1 - q) ^ 3 + 3 * frMoment g A 0 := by
  rw [two_sided_finrank_three, frMoment_zero]

end OddCycleBound.DenseRegion
