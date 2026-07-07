/-
# High-density theorem — general-`m` block-power recursion (toward the necklace decomposition)

The universal (all-odd-`m`) two-sided identity is **not** obtained length by length.  Its combinatorial
core is a single general-`m` decomposition of `Tr(blockOp q g A ^ m)`, proved by induction on `m`,
after which the two general-`m` parity pillars (`frMoment_neg`, `trace_neg_pow` in `FiniteRank.lean`)
collapse the `A`-terms for every odd `m` at once.

This file builds the elementary, symbolic-in-`m` foundation for that decomposition: the one-step block
recursion `P^{m+1} = P^m · P` resolved over the hub (`none`) / body (`some i`) split of `Option ι`,
the four resulting component recursions for the block entries of `P^m`, and the split of the trace into
its hub entry plus body diagonal.  Unrolling the body-matrix recursion `δ_{m+1} = c_m gᵀ + δ_m A`
(next step) produces exactly the necklace sum `Tr(A^m) + Σ (moment-products)`.

Notation, writing `P = blockOp q g A`:
* `(P^m) none none`         — hub↔hub entry  (scalar `α_m`);
* `(P^m) none (some j)`     — hub↔body row   (`β_m`);
* `(P^m) (some i) none`     — body↔hub col   (`γ_m`);
* `(P^m) (some i) (some j)` — body↔body block (`δ_m`, an `ι×ι` matrix), whose trace carries `Tr(A^m)`.
-/

import OddCycleBound.HighDensity.FiniteRank

namespace OddCycleBound.HighDensity

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Block recursion engine.**  One step of `P^{m+1} = P^m · P` with the intermediate index summed
over `Option ι`, split into the hub term (`none`) and the body sum (`some i`).  Every component
recursion below is a specialisation of this single general-`m` identity. -/
lemma blockOp_pow_succ_apply (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) (x y : Option ι) :
    (blockOp q g A ^ (m + 1)) x y
      = (blockOp q g A ^ m) x none * blockOp q g A none y
        + ∑ i, (blockOp q g A ^ m) x (some i) * blockOp q g A (some i) y := by
  rw [pow_succ, Matrix.mul_apply, Fintype.sum_option]

/-- Hub↔hub recursion: `α_{m+1} = α_m q + ⟨β_m, g⟩`. -/
lemma blockOp_pow_succ_none_none (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    (blockOp q g A ^ (m + 1)) none none
      = (blockOp q g A ^ m) none none * q
        + ∑ i, (blockOp q g A ^ m) none (some i) * g i := by
  rw [blockOp_pow_succ_apply]
  simp only [blockOp_none_none, blockOp_some_none]

/-- Hub↔body recursion: `β_{m+1}(j) = α_m g_j + (β_m A)_j`. -/
lemma blockOp_pow_succ_none_some (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) (j : ι) :
    (blockOp q g A ^ (m + 1)) none (some j)
      = (blockOp q g A ^ m) none none * g j
        + ∑ i, (blockOp q g A ^ m) none (some i) * A i j := by
  rw [blockOp_pow_succ_apply]
  simp only [blockOp_none_some, blockOp_some_some]

/-- Body↔hub recursion: `γ_{m+1}(i) = γ_m(i) q + (δ_m g)_i`. -/
lemma blockOp_pow_succ_some_none (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) (i : ι) :
    (blockOp q g A ^ (m + 1)) (some i) none
      = (blockOp q g A ^ m) (some i) none * q
        + ∑ k, (blockOp q g A ^ m) (some i) (some k) * g k := by
  rw [blockOp_pow_succ_apply]
  simp only [blockOp_none_none, blockOp_some_none]

/-- Body↔body recursion: `δ_{m+1} = γ_m gᵀ + δ_m A` (the transfer step carrying `Tr(A^m)`). -/
lemma blockOp_pow_succ_some_some (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    (blockOp q g A ^ (m + 1)) (some i) (some j)
      = (blockOp q g A ^ m) (some i) none * g j
        + ∑ k, (blockOp q g A ^ m) (some i) (some k) * A k j := by
  rw [blockOp_pow_succ_apply]
  simp only [blockOp_none_some, blockOp_some_some]

/-- The trace of any power splits into the hub entry plus the body diagonal:
`Tr(P^m) = α_m + Tr(δ_m)`.  The body diagonal is where `Tr(A^m)` and the surviving even moments live. -/
lemma trace_blockOp_pow (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    trace (blockOp q g A ^ m)
      = (blockOp q g A ^ m) none none
        + ∑ i, (blockOp q g A ^ m) (some i) (some i) := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_option]

end OddCycleBound.HighDensity
