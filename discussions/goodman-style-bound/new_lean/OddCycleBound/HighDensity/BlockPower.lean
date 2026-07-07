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
import Mathlib.Tactic.Abel

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

/-! ### Unrolling the body block: isolating `A^m`

The body↔hub column `γ_m` and the body block `δ_m` as first-class objects, and the unrolled form of
`δ_m` that separates the pure compression power `A^m` from the moment-coupling rank-one terms.  Taking
the trace, `Tr(A^m)` cancels for odd `m` (via `trace_neg_pow`), and the coupling terms carry the
moments. -/

/-- Body↔hub column `γ_m` of `P^m`: `γ_m(i) = (P^m)_{(some i), none}`. -/
noncomputable def hubCol (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) : ι → ℝ :=
  fun i => (blockOp q g A ^ m) (some i) none

/-- Body↔body block `δ_m` of `P^m` as an `ι×ι` matrix: `δ_m(i,j) = (P^m)_{(some i),(some j)}`. -/
noncomputable def bodyBlock (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) : Matrix ι ι ℝ :=
  fun i j => (blockOp q g A ^ m) (some i) (some j)

@[simp] lemma bodyBlock_zero (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    bodyBlock q g A 0 = 1 := by
  ext i j
  simp only [bodyBlock, pow_zero, Matrix.one_apply, Option.some.injEq]

/-- Transfer step for the body block: `δ_{m+1} = γ_m gᵀ + δ_m A`. -/
lemma bodyBlock_succ (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    bodyBlock q g A (m + 1) = vecMulVec (hubCol q g A m) g + bodyBlock q g A m * A := by
  ext i j
  simp only [bodyBlock, blockOp_pow_succ_some_some, Matrix.add_apply, Matrix.vecMulVec_apply,
    hubCol, Matrix.mul_apply]

/-- **Unrolled body block.**  `δ_m = A^m + Σ_{t<m} (γ_t gᵀ) A^{m-1-t}` — the pure compression power
`A^m` plus rank-one moment-coupling terms.  This is the matrix-level heart of the necklace
decomposition. -/
lemma bodyBlock_eq (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    bodyBlock q g A m
      = A ^ m + ∑ t ∈ Finset.range m, vecMulVec (hubCol q g A t) g * A ^ (m - 1 - t) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : (∑ t ∈ Finset.range m, vecMulVec (hubCol q g A t) g * A ^ (m - 1 - t)) * A
        = ∑ t ∈ Finset.range m, vecMulVec (hubCol q g A t) g * A ^ (m - t) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_range] at ht
      rw [Matrix.mul_assoc, ← pow_succ]
      have : m - 1 - t + 1 = m - t := by omega
      rw [this]
    rw [bodyBlock_succ, ih, add_mul, hsum, Finset.sum_range_succ]
    simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, Matrix.mul_one]
    rw [pow_succ A m]
    abel

@[simp] lemma hubCol_zero (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    hubCol q g A 0 = 0 := by
  ext i
  simp [hubCol, pow_zero]

/-- Recursion for the body↔hub column: `γ_{m+1} = q γ_m + δ_m g`. -/
lemma hubCol_succ (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    hubCol q g A (m + 1) = q • hubCol q g A m + bodyBlock q g A m *ᵥ g := by
  ext i
  simp only [hubCol, blockOp_pow_succ_some_none, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, bodyBlock]
  ring

/-- **Unrolled body↔hub column.**  `γ_m = Σ_{u<m} q^{m-1-u} (δ_u g)` — the continued-fraction closure
of the coupled `γ`/`δ` recursion.  Together with `bodyBlock_eq` this puts both coupled sequences in
closed form over powers of `A` and `q`. -/
lemma hubCol_eq (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    hubCol q g A m
      = ∑ u ∈ Finset.range m, q ^ (m - 1 - u) • (bodyBlock q g A u *ᵥ g) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : q • (∑ u ∈ Finset.range m, q ^ (m - 1 - u) • (bodyBlock q g A u *ᵥ g))
        = ∑ u ∈ Finset.range m, q ^ (m - u) • (bodyBlock q g A u *ᵥ g) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_range] at hu
      rw [smul_smul, ← pow_succ']
      have : m - 1 - u + 1 = m - u := by omega
      rw [this]
    rw [hubCol_succ, ih, hsum, Finset.sum_range_succ]
    simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, one_smul]

/-- Trace of the unrolled body block: `Tr(δ_m) = Tr(A^m) + Σ_{t<m} Tr((γ_t gᵀ) A^{m-1-t})`.
Isolates the pure compression trace `Tr(A^m)`. -/
lemma trace_bodyBlock (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    trace (bodyBlock q g A m)
      = trace (A ^ m)
        + ∑ t ∈ Finset.range m, trace (vecMulVec (hubCol q g A t) g * A ^ (m - 1 - t)) := by
  rw [bodyBlock_eq, trace_add, trace_sum]

/-- **`Tr(P^m)` with `A^m` isolated.**  `Tr(blockOp q g A ^ m) = α_m + Tr(A^m) + Σ_{t<m} (coupling_t)`,
where `α_m = (P^m)_{none,none}` is the hub return and each coupling term is
`Tr((γ_t gᵀ) A^{m-1-t})` (a moment-product).  Under the two-sided move `A ↦ −A` (`P ↦ M`), the
`Tr(A^m)` term cancels for odd `m` by `trace_neg_pow`; the coupling terms carry the surviving even
moments.  This is the structural skeleton of the necklace decomposition. -/
lemma trace_blockOp_pow_eq (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) (m : ℕ) :
    trace (blockOp q g A ^ m)
      = (blockOp q g A ^ m) none none + trace (A ^ m)
        + ∑ t ∈ Finset.range m, trace (vecMulVec (hubCol q g A t) g * A ^ (m - 1 - t)) := by
  rw [trace_blockOp_pow]
  have hbody : (∑ i, (blockOp q g A ^ m) (some i) (some i)) = trace (bodyBlock q g A m) := by
    simp only [bodyBlock, Matrix.trace, Matrix.diag_apply]
  rw [hbody, trace_bodyBlock, ← add_assoc]

/-- **Two-sided trace, `Tr(A^m)` cancelled (odd `m`).**  Applying the skeleton to `P = blockOp q g A`
and `M = blockOp (1−q) g (−A)` and using pillar 1 (`trace_neg_pow_odd`: `Tr((−A)^m) = −Tr(A^m)` for odd
`m`), the pure compression trace drops out of the two-sided sum, leaving only the hub returns and the
moment-coupling terms.  This is the general-`m` realisation of the `det(I±zA)`-cancellation of
`paper_new.tex` §`sec:two-sided`, valid for *every* odd `m` at once. -/
lemma two_sided_trace_eq {m : ℕ} (hm : Odd m) (q : ℝ) (g : ι → ℝ) (A : Matrix ι ι ℝ) :
    trace (blockOp q g A ^ m) + trace (blockOp (1 - q) g (-A) ^ m)
      = ((blockOp q g A ^ m) none none + (blockOp (1 - q) g (-A) ^ m) none none)
        + (∑ t ∈ Finset.range m, trace (vecMulVec (hubCol q g A t) g * A ^ (m - 1 - t))
           + ∑ t ∈ Finset.range m,
               trace (vecMulVec (hubCol (1 - q) g (-A) t) g * (-A) ^ (m - 1 - t))) := by
  rw [trace_blockOp_pow_eq, trace_blockOp_pow_eq, trace_neg_pow_odd hm]
  abel

end OddCycleBound.HighDensity
