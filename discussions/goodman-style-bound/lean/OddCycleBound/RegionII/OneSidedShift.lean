import OddCycleBound.RegionII.SpectralFoundation
import OddCycleBound.HighDensity.BlockPower

/-!
# The one-sided spectral shift

This file starts the first major Region-II acceptance checkpoint.  It
specializes the copied general block-power recursion to

`M = [[p, gᵀ], [g, -A]]`

and isolates all hub/body coupling terms in `oneSidedShift`.  The resulting
identity is symbolic in the odd cycle length; it is not proved separately for
individual values of `m`.
-/

open scoped BigOperators

noncomputable section

namespace OddCycleBound.RegionII

open Matrix
open OddCycleBound.HighDensity

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The finite one-sided shift left after extracting `p^m` and the odd
compression trace from `Tr([[p,gᵀ],[g,-A]]^m)`.

The two sums are respectively the hub-return and body-return coupling terms
from the universal block-power recursion.  Since `hubCol` and `bodyBlock` are
finite recurrences, this is a finite polynomial in `p`, the entries of `A`,
and the entries of `g`. -/
noncomputable def oneSidedShift
    (p : Real) (g : ι → Real) (A : Matrix ι ι Real) (m : Nat) : Real :=
  (∑ t ∈ Finset.range m,
      p ^ (m - 1 - t) * (hubCol p g (-A) t ⬝ᵥ g)) +
    ∑ t ∈ Finset.range m,
      Matrix.trace (vecMulVec (hubCol p g (-A) t) g * (-A) ^ (m - 1 - t))

@[simp]
theorem oneSidedShift_zero (p : Real) (g : ι → Real)
    (A : Matrix ι ι Real) :
    oneSidedShift p g A 0 = 0 := by
  simp [oneSidedShift]

/-- Universal finite-matrix one-sided spectral-shift identity. -/
theorem one_sided_matrix_identity
    {m : Nat} (hm : Odd m) (p : Real) (g : ι → Real)
    {A : Matrix ι ι Real} (hA : A.IsSymm) :
    Matrix.trace (blockOp p g (-A) ^ m) =
      p ^ m - Matrix.trace (A ^ m) + oneSidedShift p g A m := by
  have hnegA : (-A).IsSymm := by
    show (-A)ᵀ = -A
    rw [Matrix.transpose_neg, hA.eq]
  rw [trace_blockOp_pow_eq,
    show (blockOp p g (-A) ^ m) none none = hubEntry p g (-A) m from rfl,
    hubEntry_eq p g hnegA, trace_neg_pow_odd hm]
  unfold oneSidedShift
  ring

/-- The shift is exactly the difference between the full block trace and its
uncoupled one-sided baseline. -/
theorem oneSidedShift_eq_trace_sub
    {m : Nat} (hm : Odd m) (p : Real) (g : ι → Real)
    {A : Matrix ι ι Real} (hA : A.IsSymm) :
    oneSidedShift p g A m =
      Matrix.trace (blockOp p g (-A) ^ m) - p ^ m + Matrix.trace (A ^ m) := by
  rw [one_sided_matrix_identity hm p g hA]
  ring

end OddCycleBound.RegionII
