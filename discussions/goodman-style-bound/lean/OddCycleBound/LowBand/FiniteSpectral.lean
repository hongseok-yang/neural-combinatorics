import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Finite-dimensional spectral moment lemmas

This file is only a finite-dimensional sanity check for the spectral algebra.
It is **not** used by the graphon-facing C9 theorem.  In particular, it should
not be read as an approximation theorem for graphons: arbitrary graphon
operators need not have finitely many non-zero eigenvalues.

The grounded C9 interface lives in `OddCycleBound.LowBand.InfiniteSpectral`,
where the spectral data are countably indexed and the trace identities are
explicit hypotheses to be proved from compact self-adjoint graphon operator
theory.
-/

noncomputable section

open scoped InnerProductSpace

namespace OddCycleBound
namespace LowBand
namespace FiniteSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {n : ℕ} (hn : Module.finrank ℝ E = n)
variable (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)

/-- Powers of a self-adjoint operator are diagonal on its eigenvector basis. -/
lemma pow_apply_eigenvectorBasis (k : ℕ) (i : Fin n) :
    (T ^ k) (hT.eigenvectorBasis hn i) =
      ((hT.eigenvalues hn i : ℝ) ^ k) • hT.eigenvectorBasis hn i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      simp [ih, hT.apply_eigenvectorBasis hn i, smul_smul, pow_succ]
      ring_nf

/-- The trace of a power is the corresponding spectral moment. -/
lemma trace_pow_eq_sum_eigenvalues_pow (k : ℕ) :
    (T ^ k).trace ℝ E = ∑ i : Fin n, (hT.eigenvalues hn i : ℝ) ^ k := by
  rw [LinearMap.trace_eq_sum_inner (T ^ k) (hT.eigenvectorBasis hn)]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_apply_eigenvectorBasis hn T hT k i]
  simp [inner_smul_right, OrthonormalBasis.norm_eq_one]

/-- The quadratic trace moment of a self-adjoint operator. -/
lemma trace_sq_eq_sum_eigenvalues_sq :
    (T ^ 2).trace ℝ E = ∑ i : Fin n, (hT.eigenvalues hn i : ℝ) ^ 2 :=
  trace_pow_eq_sum_eigenvalues_pow hn T hT 2

/-- The cubic trace moment of a self-adjoint operator. -/
lemma trace_cube_eq_sum_eigenvalues_cube :
    (T ^ 3).trace ℝ E = ∑ i : Fin n, (hT.eigenvalues hn i : ℝ) ^ 3 :=
  trace_pow_eq_sum_eigenvalues_pow hn T hT 3

/-- The ninth trace moment of a self-adjoint operator, the moment used for C9. -/
lemma trace_ninth_eq_sum_eigenvalues_ninth :
    (T ^ 9).trace ℝ E = ∑ i : Fin n, (hT.eigenvalues hn i : ℝ) ^ 9 :=
  trace_pow_eq_sum_eigenvalues_pow hn T hT 9

/-- Ninth-power mass contributed by non-principal negative eigenvalues.

The argument is indexed by an explicitly chosen principal index so the same
definition can be reused after reindexing within a genuinely finite-dimensional
operator. -/
def negativeNinthMass (eigen : Fin n → ℝ) (principal : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase principal, max (-(eigen i ^ 9)) 0

private lemma neg_max_neg_zero_le_self (a : ℝ) : -max (-a) 0 ≤ a := by
  by_cases ha : 0 ≤ a
  · have hmax : max (-a) 0 = 0 := by
      exact max_eq_right (by linarith)
    rw [hmax]
    linarith
  · have hmax : max (-a) 0 = -a := by
      exact max_eq_left (by linarith)
    rw [hmax]
    linarith

/-- Splitting off one eigenvalue, the total ninth moment dominates that
eigenvalue's ninth power minus the negative ninth-power mass of all others. -/
lemma principal_pow_sub_negativeNinthMass_le_sum_pow
    (eigen : Fin n → ℝ) (principal : Fin n) :
    eigen principal ^ 9 - negativeNinthMass eigen principal ≤
      ∑ i : Fin n, eigen i ^ 9 := by
  have hsum :
      ∑ i ∈ Finset.univ.erase principal, (-(max (-(eigen i ^ 9)) 0))
        ≤ ∑ i ∈ Finset.univ.erase principal, eigen i ^ 9 := by
    apply Finset.sum_le_sum
    intro i _
    exact neg_max_neg_zero_le_self (eigen i ^ 9)
  have hsplit :=
    Finset.add_sum_erase Finset.univ (fun i : Fin n => eigen i ^ 9)
      (Finset.mem_univ principal)
  calc
    eigen principal ^ 9 - negativeNinthMass eigen principal
        = eigen principal ^ 9 +
            ∑ i ∈ Finset.univ.erase principal, (-(max (-(eigen i ^ 9)) 0)) := by
          simp [negativeNinthMass, Finset.sum_neg_distrib]
          ring
    _ ≤ eigen principal ^ 9 + ∑ i ∈ Finset.univ.erase principal, eigen i ^ 9 := by
          linarith
    _ = ∑ i : Fin n, eigen i ^ 9 := hsplit

/-- Finite-dimensional operator form of the C9 trace lower bound:
`tr(T^9)` is at least the principal ninth power minus the non-principal
negative ninth-power mass. -/
lemma principal_pow_sub_negativeNinthMass_le_trace_ninth (principal : Fin n) :
    hT.eigenvalues hn principal ^ 9 -
        negativeNinthMass (fun i : Fin n => hT.eigenvalues hn i) principal
      ≤ (T ^ 9).trace ℝ E := by
  rw [trace_ninth_eq_sum_eigenvalues_ninth hn T hT]
  exact principal_pow_sub_negativeNinthMass_le_sum_pow
    (fun i : Fin n => hT.eigenvalues hn i) principal

/-- The same trace lower bound using the largest eigenvalue index. -/
lemma top_pow_sub_negativeNinthMass_le_trace_ninth (hnpos : 0 < n) :
    hT.eigenvalues hn ⟨0, hnpos⟩ ^ 9 -
        negativeNinthMass (fun i : Fin n => hT.eigenvalues hn i) ⟨0, hnpos⟩
      ≤ (T ^ 9).trace ℝ E :=
  principal_pow_sub_negativeNinthMass_le_trace_ninth hn T hT ⟨0, hnpos⟩

/-- Rayleigh quotients expanded in the self-adjoint eigenbasis. -/
lemma rayleigh_eq_sum_eigenvalues_mul_sq (x : E) :
    ⟪x, T x⟫_ℝ =
      ∑ i : Fin n, hT.eigenvalues hn i * ((hT.eigenvectorBasis hn).repr x i) ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map x (T x)]
  rw [PiLp.inner_apply]
  simp_rw [hT.eigenvectorBasis_apply_self_apply hn x]
  simp [pow_two, mul_comm, mul_left_comm]

/-- Parseval for the coordinates in the self-adjoint eigenbasis, over `ℝ`. -/
lemma sum_eigenbasis_repr_sq_eq_norm_sq (x : E) :
    ∑ i : Fin n, ((hT.eigenvectorBasis hn).repr x i) ^ 2 = ‖x‖ ^ 2 := by
  simpa [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs] using
    (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x

/-- A unit vector's Rayleigh quotient is bounded by the top eigenvalue. -/
lemma rayleigh_le_top_eigenvalue {x : E} (hnpos : 0 < n) (hx : ‖x‖ = 1) :
    ⟪x, T x⟫_ℝ ≤ hT.eigenvalues hn ⟨0, hnpos⟩ := by
  rw [rayleigh_eq_sum_eigenvalues_mul_sq hn T hT x]
  calc
    ∑ i : Fin n, hT.eigenvalues hn i * ((hT.eigenvectorBasis hn).repr x i) ^ 2
        ≤ ∑ i : Fin n,
            hT.eigenvalues hn ⟨0, hnpos⟩ * ((hT.eigenvectorBasis hn).repr x i) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hzero_le : (⟨0, hnpos⟩ : Fin n) ≤ i := by
            exact (Fin.mk_le_mk).mpr (Nat.zero_le i.val)
          exact mul_le_mul_of_nonneg_right
            ((hT.eigenvalues_antitone hn) hzero_le) (sq_nonneg _)
    _ = hT.eigenvalues hn ⟨0, hnpos⟩ := by
          rw [← Finset.mul_sum]
          rw [sum_eigenbasis_repr_sq_eq_norm_sq hn T hT x, hx]
          ring

end FiniteSpectral
end LowBand
end OddCycleBound
