import OddCycleBound.RegionII.GraphonShiftIdentity

/-!
# Region II frontier spectrum

This file starts the one-frontier reduction for the complement compression.
The complement compression eigenvalues are the negatives of the centered
`W`-operator eigenvalues used by the arbitrary-graphon spectral foundation.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity
open OddCycleBound.LowBand.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

/-- Canonical nonzero eigenvalues of the complement compression
`A = -P T_W P`. -/
def complementEigenvalue (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Real :=
  -centeredEigenvalue hW i

/-- A scalar odd-power estimate used in the no-frontier case. -/
lemma odd_pow_le_q_pow_mul_sq {q x : Real} {m : Nat}
    (hq : 0 ≤ q) (hxq : x ≤ q) (hm : Odd m) (hm3 : 3 ≤ m) :
    x ^ m ≤ q ^ (m - 2) * x ^ 2 := by
  by_cases hx : 0 ≤ x
  · have hpow : x ^ (m - 2) ≤ q ^ (m - 2) :=
      pow_le_pow_left₀ hx hxq (m - 2)
    have hmul := mul_le_mul_of_nonneg_right hpow (sq_nonneg x)
    calc
      x ^ m = x ^ (m - 2) * x ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ q ^ (m - 2) * x ^ 2 := hmul
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hleft : x ^ m ≤ 0 := by
      rw [show x = -(-x) by ring, hm.neg_pow]
      exact neg_nonpos.mpr (pow_nonneg (by linarith) m)
    exact hleft.trans (mul_nonneg (pow_nonneg hq _) (sq_nonneg x))

/-- Every eigenvalue of the centered graphon compression, hence also of its
negative complement compression, has absolute value at most `1/2`. -/
theorem abs_centeredEigenvalue_le_half (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) :
    |centeredEigenvalue hW i| ≤ (1 : Real) / 2 := by
  have hnormMode : ‖centeredEigenmode hW i‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have hop : ‖centeredKernelOp hW‖ ≤ (1 : Real) / 2 := by
    rw [centeredKernelOp_eq_centeredGraphonOp hW]
    exact norm_centeredGraphonOp_le_half hW
  calc
    |centeredEigenvalue hW i| =
        ‖centeredEigenvalue hW i • centeredEigenmode hW i‖ := by
          rw [norm_smul, hnormMode, mul_one, Real.norm_eq_abs]
    _ = ‖centeredKernelOp hW (centeredEigenmode hW i)‖ := by
          rw [centeredKernelOp_eq_centeredGraphonOp hW,
            centeredEigenmode_diagonal hW i]
    _ ≤ ‖centeredKernelOp hW‖ * ‖centeredEigenmode hW i‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ = ‖centeredKernelOp hW‖ := by rw [hnormMode, mul_one]
    _ ≤ (1 : Real) / 2 := hop

theorem abs_complementEigenvalue_le_half (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) :
    |complementEigenvalue hW i| ≤ (1 : Real) / 2 := by
  simpa [complementEigenvalue] using abs_centeredEigenvalue_le_half hW i

/-- There is at most one complement-compression eigenvalue above the Region
II threshold `q = 1-p`. -/
theorem complement_frontier_unique
    (hW : IsGraphon W mu)
    (hq : (1 : Real) / 3 < 1 - edgeDensity W mu)
    {i j : CenteredEigenIndex hW}
    (hi : 1 - edgeDensity W mu < complementEigenvalue hW i)
    (hj : 1 - edgeDensity W mu < complementEigenvalue hW j) :
    i = j := by
  classical
  by_contra hij
  have hbudget := centeredEigenvalue_finite_square_budget hW ({i, j} : Finset _)
  have hkernel := centeredKernel_hilbertSchmidt_budget hW
  have hsquares :
      centeredEigenvalue hW i ^ 2 + centeredEigenvalue hW j ^ 2 ≤
        edgeDensity W mu * (1 - edgeDensity W mu) := by
    have hfinite :
        centeredEigenvalue hW i ^ 2 + centeredEigenvalue hW j ^ 2 ≤
          kernelSqNorm mu (centeredKernel W mu) := by
      simpa [hij, add_comm] using hbudget
    have hkernel' :
        kernelSqNorm mu (centeredKernel W mu) ≤
          edgeDensity W mu * (1 - edgeDensity W mu) := by
      nlinarith [sq_nonneg ‖centeredDegreeL2 hW‖]
    exact hfinite.trans hkernel'
  have hq0 : 0 ≤ 1 - edgeDensity W mu := by linarith
  have hiSq := mul_self_lt_mul_self hq0 hi
  have hjSq := mul_self_lt_mul_self hq0 hj
  dsimp [complementEigenvalue] at hiSq hjSq
  nlinarith

/-- Trace-power spectral expansion with the cycle length, rather than the
auxiliary offset, as its parameter. -/
theorem centered_trace_compPow_hasSum_eigen_pow_of_ge_three
    (hW : IsGraphon W mu) {m : Nat} (hm3 : 3 ≤ m) :
    HasSum (fun i : CenteredEigenIndex hW => centeredEigenvalue hW i ^ m)
      (trace mu (compPow mu (centeredKernel W mu) (m - 1))) := by
  have htwo : m - 3 + 2 = m - 1 := by omega
  have hthree : m - 3 + 3 = m := by omega
  simpa only [htwo, hthree] using
    centered_trace_compPow_hasSum_eigen_pow hW (m - 3)

/-- In the absence of a complement eigenvalue above `q`, the centered trace
cannot lose more than the Goodman baseline term. -/
theorem centered_trace_no_frontier_lower_bound
    (hW : IsGraphon W mu) {m : Nat}
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hfrontier : ∀ i : CenteredEigenIndex hW,
      complementEigenvalue hW i ≤ 1 - edgeDensity W mu) :
    -edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      trace mu (compPow mu (centeredKernel W mu) (m - 1)) := by
  let p := edgeDensity W mu
  let q := 1 - p
  have hp0 : 0 ≤ p := edgeDensity_nonneg hW
  have hq0 : 0 ≤ q := by
    dsimp [q, p]
    linarith [edgeDensity_le_one hW]
  have hseries :=
    centered_trace_compPow_hasSum_eigen_pow_of_ge_three hW hm3
  have hsquare := centeredEigenvalue_square_summable hW
  have hlower : Summable (fun i : CenteredEigenIndex hW =>
      -q ^ (m - 2) * centeredEigenvalue hW i ^ 2) :=
    hsquare.mul_left (-q ^ (m - 2))
  have hpoint : ∀ i : CenteredEigenIndex hW,
      -q ^ (m - 2) * centeredEigenvalue hW i ^ 2 ≤
        centeredEigenvalue hW i ^ m := by
    intro i
    have hv := odd_pow_le_q_pow_mul_sq hq0 (hfrontier i) hm hm3
    dsimp [complementEigenvalue, q, p] at hv
    rw [hm.neg_pow] at hv
    have hsqneg : (-centeredEigenvalue hW i) ^ 2 =
        centeredEigenvalue hW i ^ 2 := by ring
    rw [hsqneg] at hv
    dsimp [q, p]
    linarith
  have hcompare :
      (∑' i : CenteredEigenIndex hW,
          -q ^ (m - 2) * centeredEigenvalue hW i ^ 2) ≤
        ∑' i : CenteredEigenIndex hW, centeredEigenvalue hW i ^ m :=
    Summable.tsum_le_tsum hpoint hlower hseries.summable
  rw [tsum_mul_left] at hcompare
  change -q ^ (m - 2) * centeredTraceSq hW ≤
      ∑' i : CenteredEigenIndex hW, centeredEigenvalue hW i ^ m at hcompare
  have hsqbudget : centeredTraceSq hW ≤ p * q := by
    have hbudget := centeredTraceSq_add_degree_budget hW
    dsimp [p, q]
    nlinarith [sq_nonneg ‖centeredDegreeL2 hW‖]
  have hmul := mul_le_mul_of_nonneg_left hsqbudget (pow_nonneg hq0 (m - 2))
  have hpower : q ^ (m - 2) * (p * q) = p * q ^ (m - 1) := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
    ring
  have hbaseline : -p * q ^ (m - 1) ≤
      -q ^ (m - 2) * centeredTraceSq hW := by
    calc
      -p * q ^ (m - 1) = -(p * q ^ (m - 1)) := by ring
      _ = -(q ^ (m - 2) * (p * q)) := by rw [hpower]
      _ ≤ -(q ^ (m - 2) * centeredTraceSq hW) := neg_le_neg hmul
      _ = -q ^ (m - 2) * centeredTraceSq hW := by ring
  calc
    -edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) =
        -p * q ^ (m - 1) := by rfl
    _ ≤ -q ^ (m - 2) * centeredTraceSq hW := hbaseline
    _ ≤ ∑' i : CenteredEigenIndex hW, centeredEigenvalue hW i ^ m := hcompare
    _ = trace mu (compPow mu (centeredKernel W mu) (m - 1)) := hseries.tsum_eq

/-- Completed no-frontier branch of the Region II odd-cycle bound. -/
theorem no_frontier_odd_cycle_bound
    (hW : IsGraphon W mu) {m : Nat}
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hp : (1 : Real) / 2 < edgeDensity W mu)
    (hfrontier : ∀ i : CenteredEigenIndex hW,
      complementEigenvalue hW i ≤ 1 - edgeDensity W mu) :
    edgeDensity W mu ^ m -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      cycleDensity mu W m := by
  have hm0 : 0 < m := by omega
  rw [graphon_oneSidedShift_identity hW hm0]
  have htrace := centered_trace_no_frontier_lower_bound hW hm hm3 hfrontier
  have hshift := graphonOneSidedShift_nonneg hW hp m
  linarith

/-- The mean-zero projection annihilates the normalized constant vector. -/
lemma centerProjection_oneL2 :
    centerProjection (Omega := Omega) (mu := mu)
        (oneL2 (Omega := Omega) mu) = 0 := by
  unfold centerProjection
  simp only [sub_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply]
  rw [inner_oneL2_oneL2, one_smul, sub_self]

/-- Every canonical centered eigenmode is orthogonal to the constants. -/
theorem inner_oneL2_centeredEigenmode_eq_zero
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    inner Real (oneL2 (Omega := Omega) mu) (centeredEigenmode hW i) = 0 := by
  let P := centerProjection (Omega := Omega) (mu := mu)
  have hPone : P (oneL2 (Omega := Omega) mu) = 0 :=
    centerProjection_oneL2
  have hzero :
      inner Real (oneL2 (Omega := Omega) mu)
        (centeredGraphonOp hW (centeredEigenmode hW i)) = 0 := by
    unfold centeredGraphonOp
    change inner Real (oneL2 (Omega := Omega) mu)
      (P (kernelOpCLM (mu := mu) hW (P (centeredEigenmode hW i)))) = 0
    rw [← (centerProjection_isSymmetric
      (Omega := Omega) (mu := mu)).apply_clm, hPone, inner_zero_left]
  rw [centeredEigenmode_diagonal hW i, inner_smul_right] at hzero
  have hne : centeredEigenvalue hW i ≠ 0 := by
    exact nonzeroEigenvalue_ne (centeredGraphonOp hW) i
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- A centered eigenmode has a bounded strongly measurable representative.
This is obtained by dividing its bounded centered-kernel image by its nonzero
eigenvalue. -/
theorem centeredEigenmode_hasGoodRepresentative
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    OddCycleBound.LowBand.InfiniteSpectral.HasGoodRepresentative (mu := mu)
      (centeredEigenmode hW i) := by
  let hK := centeredKernel_goodK hW
  let hf : Good (kernelOp (centeredKernel W mu) mu
      (fun y : Omega => centeredEigenmode hW i y)) :=
    good_kernelOp_goodK_l2 (mu := mu) hK
      (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
      (centeredEigenmode hW i)
  have himage :
      centeredKernelOp hW (centeredEigenmode hW i) =
        goodL2 (mu := mu) hf := by
    unfold centeredKernelOp
    rw [kernelOpGoodKCLM_eq_kernelOpGoodKL2OfL2_apply
      (mu := mu) hK (by norm_num : (0 : Real) ≤ 4)
      (abs_centeredKernel_le_four hW) (centeredKernel_symm hW)]
    rfl
  have hdiag :
      centeredKernelOp hW (centeredEigenmode hW i) =
        centeredEigenvalue hW i • centeredEigenmode hW i := by
    rw [centeredKernelOp_eq_centeredGraphonOp hW]
    exact centeredEigenmode_diagonal hW i
  have hne : centeredEigenvalue hW i ≠ 0 :=
    nonzeroEigenvalue_ne (centeredGraphonOp hW) i
  exact
    OddCycleBound.LowBand.InfiniteSpectral.hasGoodRepresentative_of_nonzero_eigenmode_and_good_operator_image
      hf himage hdiag hne

/-- Concrete normalized, mean-zero representative of every centered
eigenmode. -/
theorem exists_good_centeredEigenfunction
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    ∃ (phi : Omega → Real), ∃ hphi : Good phi,
      centeredEigenmode hW i = goodL2 (mu := mu) hphi ∧
      mean mu phi = 0 ∧
      (∫ x, phi x * phi x ∂mu) = 1 := by
  rcases centeredEigenmode_hasGoodRepresentative hW i with
    ⟨phi, hphi, hrep⟩
  have hmean := inner_oneL2_centeredEigenmode_eq_zero hW i
  rw [hrep, inner_oneL2_goodL2_eq_mean hphi] at hmean
  have hnorm : ‖centeredEigenmode hW i‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have hnormSq : ‖goodL2 (mu := mu) hphi‖ ^ 2 = 1 := by
    rw [← hrep, hnorm]
    norm_num
  rw [norm_goodL2_sq_eq_integral_mul hphi] at hnormSq
  exact ⟨phi, hphi, hrep, hmean, hnormSq⟩

end OddCycleBound.RegionII
