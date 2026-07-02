import OddCycleBound.LowBand.C9Spectral
import OddCycleBound.LowBand.C11Scalar

/-!
# Infinite spectral data for the low-band C11 argument

This file starts the C11 analogue of `LowBand.C9Spectral`.  The compact
graphon-operator side is already cycle-length independent, so the graphon
bridge below reuses the C9 padded compact-action spectral package and records
the eleventh trace moment needed for C11.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound
namespace LowBand
namespace InfiniteSpectral

universe u

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/-- The negative eleventh-power mass of all non-principal modes in a countable
spectral expansion whose principal mode is indexed by `0`. -/
def negativeEleventhTailMass (eigen : Nat -> Real) : Real :=
  ∑' n : Nat, max (-(eigen (n + 1) ^ 11)) 0

private lemma single_le_tsum_of_nonneg {f : Nat -> Real}
    (hf : Summable f) (hnonneg : ∀ n, 0 <= f n) (n : Nat) :
    f n <= ∑' n, f n := by
  have h := hf.sum_le_tsum ({n} : Finset Nat) (fun i _ => hnonneg i)
  simpa using h

private lemma neg_max_neg_zero_le_self (a : Real) : -max (-a) 0 <= a := by
  by_cases ha : 0 <= a
  · have hmax : max (-a) 0 = 0 := max_eq_right (by linarith)
    rw [hmax]
    linarith
  · have hmax : max (-a) 0 = -a := max_eq_left (by linarith)
    rw [hmax]
    linarith

/-- Infinite-series form of the negative-tail lower bound for the eleventh
trace. -/
lemma principal_sub_negativeEleventhTailMass_le_tsum
    (eigen : Nat -> Real)
    (hsum : Summable fun n : Nat => eigen n ^ 11)
    (hneg : Summable fun n : Nat => max (-(eigen (n + 1) ^ 11)) 0) :
    eigen 0 ^ 11 - negativeEleventhTailMass eigen <=
      ∑' n : Nat, eigen n ^ 11 := by
  have hshift : Summable fun n : Nat => eigen (n + 1) ^ 11 :=
    (summable_nat_add_iff 1).2 hsum
  have hneg' : Summable fun n : Nat => -(max (-(eigen (n + 1) ^ 11)) 0) :=
    hneg.neg
  have hle_tail :
      (∑' n : Nat, -(max (-(eigen (n + 1) ^ 11)) 0))
        <= ∑' n : Nat, eigen (n + 1) ^ 11 := by
    exact Summable.tsum_le_tsum
      (fun n => neg_max_neg_zero_le_self (eigen (n + 1) ^ 11)) hneg' hshift
  calc
    eigen 0 ^ 11 - negativeEleventhTailMass eigen
        = eigen 0 ^ 11 + ∑' n : Nat, -(max (-(eigen (n + 1) ^ 11)) 0) := by
          rw [negativeEleventhTailMass, tsum_neg]
          ring
    _ <= eigen 0 ^ 11 + ∑' n : Nat, eigen (n + 1) ^ 11 := by
          linarith
    _ = ∑' n : Nat, eigen n ^ 11 := by
          rw [hsum.tsum_eq_zero_add]

/-- Countable spectral expansion data for the eleventh trace of a graphon
kernel. -/
structure C11SpectralExpansion
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  eigen : Nat -> Real
  summable_eleventh : Summable fun n : Nat => eigen n ^ 11
  summable_negative_eleventh_tail :
    Summable fun n : Nat => max (-(eigen (n + 1) ^ 11)) 0
  trace_eleventh :
    trace mu (compPow mu W 10) = ∑' n : Nat, eigen n ^ 11

namespace C11SpectralExpansion

/-- Principal eigenvalue in the chosen countable spectral ordering. -/
def principal (S : C11SpectralExpansion W mu) : Real := S.eigen 0

/-- Negative eleventh-power mass of the non-principal tail. -/
def negativeMass (S : C11SpectralExpansion W mu) : Real :=
  negativeEleventhTailMass S.eigen

/-- The grounded infinite-spectral trace lower bound used by the C11 low-band
argument. -/
theorem principal_pow_sub_negativeMass_le_trace
    (S : C11SpectralExpansion W mu) :
    S.principal ^ 11 - S.negativeMass <= trace mu (compPow mu W 10) := by
  rw [S.trace_eleventh, principal, negativeMass]
  exact principal_sub_negativeEleventhTailMass_le_tsum S.eigen
    S.summable_eleventh S.summable_negative_eleventh_tail

/-- C11 follows from an infinite spectral expansion plus the analytic
negative-mass estimate. -/
theorem c11_cycle_bound_of_mass_bound
    (S : C11SpectralExpansion W mu)
    {q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (hmass :
      S.negativeMass <=
        S.principal ^ 11 - edgeDensity W mu ^ 11 + edgeDensity W mu * q ^ 10) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  exact LowBand.C11.cycle_bound_of_negative_mass_bound
    hq S.principal_pow_sub_negativeMass_le_trace hmass

end C11SpectralExpansion

private lemma abs_eleventh_le_sq_of_sq_le_one {a : Real} (ha : a ^ 2 <= 1) :
    |a ^ 11| <= a ^ 2 := by
  rw [abs_pow]
  have habs_sq : |a| ^ 2 <= 1 := by
    simpa [sq_abs] using ha
  have habs_le : |a| <= 1 := by
    have h0 : 0 <= |a| := abs_nonneg a
    nlinarith [sq_nonneg (|a| - 1)]
  have hpow9 : |a| ^ 9 <= 1 := by
    exact (pow_le_one₀ (abs_nonneg a) habs_le : |a| ^ 9 <= 1)
  calc
    |a| ^ 11 = |a| ^ 9 * |a| ^ 2 := by ring
    _ <= 1 * |a| ^ 2 := by
      exact mul_le_mul_of_nonneg_right hpow9 (sq_nonneg |a|)
    _ = |a| ^ 2 := one_mul _
    _ = a ^ 2 := by rw [sq_abs]

private lemma abs_cube_le_sq_of_sq_le_one {a : Real} (ha : a ^ 2 <= 1) :
    |a ^ 3| <= a ^ 2 := by
  rw [abs_pow]
  have habs_sq : |a| ^ 2 <= 1 := by
    simpa [sq_abs] using ha
  have habs_le : |a| <= 1 := by
    have h0 : 0 <= |a| := abs_nonneg a
    nlinarith [sq_nonneg (|a| - 1)]
  calc
    |a| ^ 3 = |a| * |a| ^ 2 := by ring
    _ <= 1 * |a| ^ 2 := by
      exact mul_le_mul_of_nonneg_right habs_le (sq_nonneg |a|)
    _ = |a| ^ 2 := one_mul _
    _ = a ^ 2 := by rw [sq_abs]

private lemma summable_cube_of_summable_square_of_tsum_le_one
    {eigen : Nat -> Real}
    (hsq : Summable fun n : Nat => eigen n ^ 2)
    (hle : (∑' n : Nat, eigen n ^ 2) <= 1) :
    Summable fun n : Nat => eigen n ^ 3 := by
  refine hsq.of_norm_bounded ?_
  intro n
  exact abs_cube_le_sq_of_sq_le_one
    ((single_le_tsum_of_nonneg hsq (fun n => sq_nonneg _) n).trans hle)

private lemma max_neg_eleventh_le_sq_of_sq_le_one {a : Real} (ha : a ^ 2 <= 1) :
    max (-(a ^ 11)) 0 <= a ^ 2 := by
  have h_abs := abs_eleventh_le_sq_of_sq_le_one ha
  exact max_le (by linarith [neg_le_abs (a ^ 11)]) (sq_nonneg a)

private lemma summable_eleventh_of_summable_square_of_tsum_le_one
    {eigen : Nat -> Real}
    (hsq : Summable fun n : Nat => eigen n ^ 2)
    (hle : (∑' n : Nat, eigen n ^ 2) <= 1) :
    Summable fun n : Nat => eigen n ^ 11 := by
  refine hsq.of_norm_bounded ?_
  intro n
  exact abs_eleventh_le_sq_of_sq_le_one
    ((single_le_tsum_of_nonneg hsq (fun n => sq_nonneg _) n).trans hle)

private lemma summable_negative_eleventh_tail_of_summable_square_of_tsum_le_one
    {eigen : Nat -> Real}
    (hsq : Summable fun n : Nat => eigen n ^ 2)
    (hle : (∑' n : Nat, eigen n ^ 2) <= 1) :
    Summable fun n : Nat => max (-(eigen (n + 1) ^ 11)) 0 := by
  have hshift : Summable fun n : Nat => eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 hsq
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_ hshift
  intro n
  exact max_neg_eleventh_le_sq_of_sq_le_one
    ((single_le_tsum_of_nonneg hsq (fun n => sq_nonneg _) (n + 1)).trans hle)

private lemma exists_nonneg_eleventh_root {x : Real} (hx : 0 <= x) :
    ∃ z : Real, 0 <= z ∧ z ^ 11 = x := by
  obtain ⟨r, hr⟩ :=
    NNReal.rpow_left_surjective
      (by norm_num : (11 : Real) ≠ 0) x.toNNReal
  refine ⟨(r : Real), NNReal.coe_nonneg r, ?_⟩
  have hcoe : ((r ^ (11 : Real) : NNReal) : Real) = x := by
    simp [hr, Real.coe_toNNReal x hx]
  simpa [NNReal.coe_rpow, Real.rpow_natCast] using hcoe

/-- Countable trace data with the square information stated as the budget
consumed by the C11 low-band argument. -/
structure C11BudgetTraceSpectralData
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  eigen : Nat -> Real
  summable_square : Summable fun n : Nat => eigen n ^ 2
  square_budget :
    (∑' n : Nat, eigen n ^ 2) <= edgeDensity W mu
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_eleventh :
    trace mu (compPow mu W 10) = ∑' n : Nat, eigen n ^ 11
  principal_ge_edge :
    edgeDensity W mu <= eigen 0

/-- C11 spectral data used by the low-band scalar argument. -/
structure C11SpectralData
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  expansion : C11SpectralExpansion W mu
  summable_square : Summable fun n : Nat => expansion.eigen n ^ 2
  summable_cube : Summable fun n : Nat => expansion.eigen n ^ 3
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, expansion.eigen n ^ 3
  square_budget :
    (∑' n : Nat, expansion.eigen n ^ 2) <= edgeDensity W mu
  principal_ge_edge :
    edgeDensity W mu <= expansion.eigen 0

namespace C11BudgetTraceSpectralData

/-- Budget trace data are exactly enough to build the spectral package used by
the C11 low-band scalar argument. -/
def toC11SpectralData
    [IsProbabilityMeasure mu]
    (S : C11BudgetTraceSpectralData W mu) (hW : IsGraphon W mu) :
    C11SpectralData W mu :=
  let hsq_le_one : (∑' n : Nat, S.eigen n ^ 2) <= 1 :=
    S.square_budget.trans (edgeDensity_le_one hW)
  {
    expansion := {
      eigen := S.eigen
      summable_eleventh :=
        summable_eleventh_of_summable_square_of_tsum_le_one
          S.summable_square hsq_le_one
      summable_negative_eleventh_tail :=
        summable_negative_eleventh_tail_of_summable_square_of_tsum_le_one
          S.summable_square hsq_le_one
      trace_eleventh := S.trace_eleventh
    }
    summable_square := S.summable_square
    summable_cube :=
      summable_cube_of_summable_square_of_tsum_le_one
        S.summable_square hsq_le_one
    trace_cube := S.trace_cube
    square_budget := S.square_budget
    principal_ge_edge := S.principal_ge_edge
  }

end C11BudgetTraceSpectralData

namespace C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag

/-- Direct-principal padded compact-action data give the graphon-facing C11
budget trace package. -/
def toC11BudgetTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    C11BudgetTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.summable_square (mu := mu) (hW := hW)
  square_budget := S.square_budget (mu := mu) (hW := hW)
  trace_cube :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 0).tsum_eq.symm
  trace_eleventh :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 8).tsum_eq.symm
  principal_ge_edge := S.principal_ge_edge

end C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag

/-- Pointwise low-band C11 budget trace data for a graphon.

The compactness and eigenmode construction are density-independent; the
low-band hypotheses are present because this is the interface consumed by the
C11 conditional low-band bridge. -/
theorem c11GraphonBudgetTraceSpectralData_lowBand
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu)
    (hgt : 1 / 2 < edgeDensity W mu)
    (_hle : edgeDensity W mu <= 103 / 200) :
    Nonempty (C11BudgetTraceSpectralData W mu) := by
  have hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) :=
    CompactSpectral.canonicalGraphonCompact_of_hilbertSchmidtFiniteRankApproxFor
      (mu := mu) hW
      (CompactSpectral.graphonHilbertSchmidtFiniteRankApproxFor
        (mu := mu) hW)
  have hp : 0 < edgeDensity W mu := by linarith
  have hendpoint :
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW :
          Module.End Real (Lp Real 2 mu))
        ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ :=
    CompactSpectral.canonicalGraphonCompact_hasEigenvalue_norm_of_edgeDensity_pos
      (mu := mu) hW hcompact hp
  let S0 :=
    C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag.ofCompactGraphonPositiveNormEndpoint
        (mu := mu) (hW := hW) hcompact hp hendpoint
  exact ⟨S0.toPaddedCorePrincipalBoundSpectralDataNoDiag.toC11BudgetTraceSpectralData⟩

namespace C11SpectralData

/-- Principal eigenvalue in the chosen countable spectral ordering. -/
def principal (S : C11SpectralData W mu) : Real := S.expansion.principal

/-- Negative eleventh-power mass of the non-principal tail. -/
def negativeMass (S : C11SpectralData W mu) : Real := S.expansion.negativeMass

theorem negativeMass_nonneg (S : C11SpectralData W mu) :
    0 <= S.negativeMass := by
  rw [negativeMass, C11SpectralExpansion.negativeMass,
    negativeEleventhTailMass]
  exact tsum_nonneg fun n => le_max_right _ _

theorem principal_pow_sub_negativeMass_le_trace (S : C11SpectralData W mu) :
    S.principal ^ 11 - S.negativeMass <= trace mu (compPow mu W 10) := by
  exact S.expansion.principal_pow_sub_negativeMass_le_trace

/-- C11 follows from countable spectral data plus the analytic negative-mass
estimate. -/
theorem c11_cycle_bound_of_mass_bound
    (S : C11SpectralData W mu)
    {q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (hmass :
      S.negativeMass <=
        S.principal ^ 11 - edgeDensity W mu ^ 11 + edgeDensity W mu * q ^ 10) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  exact LowBand.C11.cycle_bound_of_negative_mass_bound
    hq S.principal_pow_sub_negativeMass_le_trace hmass

/-- The non-principal square mass. -/
def tailSquareMass (S : C11SpectralData W mu) : Real :=
  ∑' n : Nat, S.expansion.eigen (n + 1) ^ 2

/-- Positive non-principal square mass. -/
def positiveTailSquareMass (S : C11SpectralData W mu) : Real :=
  ∑' n : Nat, max (S.expansion.eigen (n + 1)) 0 ^ 2

/-- Negative non-principal square mass. -/
def negativeTailSquareMass (S : C11SpectralData W mu) : Real :=
  ∑' n : Nat, max (-(S.expansion.eigen (n + 1))) 0 ^ 2

private lemma tail_square_le_total_square
    (eigen : Nat -> Real)
    (hsum : Summable fun n : Nat => eigen n ^ 2) :
    (∑' n : Nat, eigen (n + 1) ^ 2) <= ∑' n : Nat, eigen n ^ 2 := by
  rw [hsum.tsum_eq_zero_add]
  nlinarith [sq_nonneg (eigen 0)]

theorem tailSquareMass_le_edge (S : C11SpectralData W mu) :
    S.tailSquareMass <= edgeDensity W mu :=
  (tail_square_le_total_square S.expansion.eigen S.summable_square).trans
    S.square_budget

theorem tailSquareMass_le_edge_sub_principal_sq
    (S : C11SpectralData W mu) :
    S.tailSquareMass <= edgeDensity W mu - S.principal ^ 2 := by
  have hbudget := S.square_budget
  rw [S.summable_square.tsum_eq_zero_add] at hbudget
  rw [tailSquareMass, principal, C11SpectralExpansion.principal]
  nlinarith

theorem tail_eigen_sq_le_edge (S : C11SpectralData W mu) (n : Nat) :
    S.expansion.eigen (n + 1) ^ 2 <= edgeDensity W mu := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  exact (single_le_tsum_of_nonneg hshift (fun n => sq_nonneg _) n).trans
    S.tailSquareMass_le_edge

private lemma max_self_zero_sq_le_sq (a : Real) :
    max a 0 ^ 2 <= a ^ 2 := by
  by_cases ha : 0 <= a
  · rw [max_eq_left ha]
  · have hmax : max a 0 = 0 := max_eq_right (by linarith)
    rw [hmax]
    simpa using sq_nonneg a

private lemma max_neg_zero_sq_le_sq (a : Real) :
    max (-a) 0 ^ 2 <= a ^ 2 := by
  have h := max_self_zero_sq_le_sq (-a)
  simpa using h

private lemma positive_tail_square_summable
    (S : C11SpectralData W mu) :
    Summable fun n : Nat => max (S.expansion.eigen (n + 1)) 0 ^ 2 := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le
    (fun n => sq_nonneg (max (S.expansion.eigen (n + 1)) 0)) ?_ hshift
  intro n
  exact max_self_zero_sq_le_sq (S.expansion.eigen (n + 1))

private lemma negative_tail_square_summable
    (S : C11SpectralData W mu) :
    Summable fun n : Nat => max (-(S.expansion.eigen (n + 1))) 0 ^ 2 := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le
    (fun n => sq_nonneg (max (-(S.expansion.eigen (n + 1))) 0)) ?_ hshift
  intro n
  exact max_neg_zero_sq_le_sq (S.expansion.eigen (n + 1))

private lemma sq_eq_pos_sq_add_neg_sq (a : Real) :
    a ^ 2 = max a 0 ^ 2 + max (-a) 0 ^ 2 := by
  by_cases ha : 0 <= a
  · have hp : max a 0 = a := max_eq_left ha
    have hn : max (-a) 0 = 0 := max_eq_right (by linarith)
    rw [hp, hn]
    ring
  · have hp : max a 0 = 0 := max_eq_right (by linarith)
    have hn : max (-a) 0 = -a := max_eq_left (by linarith)
    rw [hp, hn]
    ring

theorem tailSquareMass_eq_positive_add_negative
    (S : C11SpectralData W mu) :
    S.tailSquareMass =
      S.positiveTailSquareMass + S.negativeTailSquareMass := by
  have hpos := S.positive_tail_square_summable
  have hneg := S.negative_tail_square_summable
  calc
    S.tailSquareMass
        = ∑' n : Nat,
            (max (S.expansion.eigen (n + 1)) 0 ^ 2 +
              max (-(S.expansion.eigen (n + 1))) 0 ^ 2) := by
          rw [tailSquareMass]
          apply tsum_congr
          intro n
          exact sq_eq_pos_sq_add_neg_sq (S.expansion.eigen (n + 1))
    _ = S.positiveTailSquareMass + S.negativeTailSquareMass := by
          rw [hpos.tsum_add hneg]
          rfl

theorem positiveTailSquareMass_nonneg (S : C11SpectralData W mu) :
    0 <= S.positiveTailSquareMass := by
  exact tsum_nonneg fun n => sq_nonneg _

theorem negativeTailSquareMass_nonneg (S : C11SpectralData W mu) :
    0 <= S.negativeTailSquareMass := by
  exact tsum_nonneg fun n => sq_nonneg _

theorem positiveTailSquareMass_le_edge_sub_principal_sq_sub_sq
    (S : C11SpectralData W mu) {z : Real}
    (hz : z ^ 2 <= S.negativeTailSquareMass) :
    S.positiveTailSquareMass <=
      edgeDensity W mu - S.principal ^ 2 - z ^ 2 := by
  have hbudget := S.tailSquareMass_le_edge_sub_principal_sq
  rw [S.tailSquareMass_eq_positive_add_negative] at hbudget
  linarith

/-- Positive cubic mass in the non-principal tail. -/
def positiveTailCubeMass (S : C11SpectralData W mu) : Real :=
  ∑' n : Nat, max (S.expansion.eigen (n + 1) ^ 3) 0

/-- Negative cubic mass in the non-principal tail. -/
def negativeTailCubeMass (S : C11SpectralData W mu) : Real :=
  ∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 3)) 0

/-- Signed cubic non-principal tail. -/
def tailCubeSum (S : C11SpectralData W mu) : Real :=
  ∑' n : Nat, S.expansion.eigen (n + 1) ^ 3

theorem positiveTailCubeMass_nonneg (S : C11SpectralData W mu) :
    0 <= S.positiveTailCubeMass := by
  exact tsum_nonneg fun n => le_max_right _ _

theorem negativeTailCubeMass_nonneg (S : C11SpectralData W mu) :
    0 <= S.negativeTailCubeMass := by
  exact tsum_nonneg fun n => le_max_right _ _

private lemma max_cube_zero_le_sqrt_mul_sq {a M : Real}
    (ha : a ^ 2 <= M) :
    max (a ^ 3) 0 <= Real.sqrt M * a ^ 2 := by
  by_cases ha0 : 0 <= a
  · have ha_sqrt : a <= Real.sqrt M := Real.le_sqrt_of_sq_le ha
    have hcube : a ^ 3 <= Real.sqrt M * a ^ 2 := by
      calc
        a ^ 3 = a * a ^ 2 := by ring
        _ <= Real.sqrt M * a ^ 2 := by
          exact mul_le_mul_of_nonneg_right ha_sqrt (sq_nonneg a)
    have h0 : 0 <= Real.sqrt M * a ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg M) (sq_nonneg a)
    exact max_le hcube h0
  · have hcubenonpos : a ^ 3 <= 0 := by nlinarith
    have h0 : 0 <= Real.sqrt M * a ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg M) (sq_nonneg a)
    exact max_le (le_trans hcubenonpos h0) h0

private lemma max_neg_cube_zero_le_sqrt_mul_sq {a M : Real}
    (ha : a ^ 2 <= M) :
    max (-(a ^ 3)) 0 <= Real.sqrt M * a ^ 2 := by
  by_cases ha0 : 0 <= a
  · have hcubenonneg : 0 <= a ^ 3 := by nlinarith
    have hneg : -(a ^ 3) <= 0 := by linarith
    have h0 : 0 <= Real.sqrt M * a ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg M) (sq_nonneg a)
    exact max_le (le_trans hneg h0) h0
  · have hnega0 : 0 <= -a := by linarith
    have hneg_sqrt : -a <= Real.sqrt M := by
      have hsq : (-a) ^ 2 <= M := by nlinarith
      exact Real.le_sqrt_of_sq_le hsq
    have hcube : -(a ^ 3) <= Real.sqrt M * a ^ 2 := by
      calc
        -(a ^ 3) = (-a) * a ^ 2 := by ring
        _ <= Real.sqrt M * a ^ 2 := by
          exact mul_le_mul_of_nonneg_right hneg_sqrt (sq_nonneg a)
    have h0 : 0 <= Real.sqrt M * a ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg M) (sq_nonneg a)
    exact max_le hcube h0

private lemma positive_tail_cube_summable
    (S : C11SpectralData W mu) :
    Summable fun n : Nat => max (S.expansion.eigen (n + 1) ^ 3) 0 := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_
    (hshift.mul_left (Real.sqrt (edgeDensity W mu)))
  intro n
  exact max_cube_zero_le_sqrt_mul_sq (S.tail_eigen_sq_le_edge n)

private lemma max_cube_zero_eq_pos_part_cube (a : Real) :
    max (a ^ 3) 0 = max a 0 ^ 3 := by
  by_cases ha : 0 <= a
  · have hcube : 0 <= a ^ 3 := pow_nonneg ha 3
    rw [max_eq_left hcube, max_eq_left ha]
  · have hcube : a ^ 3 <= 0 := by nlinarith [sq_nonneg a]
    have hpos : max a 0 = 0 := max_eq_right (by linarith)
    rw [max_eq_right hcube, hpos]
    norm_num

private lemma max_neg_cube_zero_eq_neg_part_cube (a : Real) :
    max (-(a ^ 3)) 0 = max (-a) 0 ^ 3 := by
  by_cases ha : 0 <= a
  · have hcube : 0 <= a ^ 3 := pow_nonneg ha 3
    have hleft : max (-(a ^ 3)) 0 = 0 := max_eq_right (by linarith)
    have hright : max (-a) 0 = 0 := max_eq_right (by linarith)
    rw [hleft, hright]
    norm_num
  · have hcube : a ^ 3 <= 0 := by nlinarith [sq_nonneg a]
    have hleft : max (-(a ^ 3)) 0 = -(a ^ 3) := max_eq_left (by linarith)
    have hright : max (-a) 0 = -a := max_eq_left (by linarith)
    rw [hleft, hright]
    ring

private lemma max_neg_eleventh_zero_eq_neg_part_eleventh (a : Real) :
    max (-(a ^ 11)) 0 = max (-a) 0 ^ 11 := by
  by_cases ha : 0 <= a
  · have hpow : 0 <= a ^ 11 := pow_nonneg ha 11
    have hleft : max (-(a ^ 11)) 0 = 0 := max_eq_right (by linarith)
    have hright : max (-a) 0 = 0 := max_eq_right (by linarith)
    rw [hleft, hright]
    norm_num
  · have ha_nonpos : a <= 0 := le_of_not_ge ha
    have h10nonneg : 0 <= a ^ 10 := by
      have h : 0 <= (a ^ 5) ^ 2 := sq_nonneg (a ^ 5)
      convert h using 1
      ring
    have hpow : a ^ 11 <= 0 := by
      have h : a ^ 11 = a * a ^ 10 := by ring
      rw [h]
      exact mul_nonpos_of_nonpos_of_nonneg ha_nonpos h10nonneg
    have hleft : max (-(a ^ 11)) 0 = -(a ^ 11) := max_eq_left (by linarith)
    have hright : max (-a) 0 = -a := max_eq_left (by linarith)
    rw [hleft, hright]
    ring

private lemma positive_tail_part_sq_le_mass
    (S : C11SpectralData W mu) (n : Nat) :
    max (S.expansion.eigen (n + 1)) 0 ^ 2 <=
      S.positiveTailSquareMass := by
  exact single_le_tsum_of_nonneg S.positive_tail_square_summable
    (fun n => sq_nonneg _) n

private lemma negative_tail_part_sq_le_mass
    (S : C11SpectralData W mu) (n : Nat) :
    max (-(S.expansion.eigen (n + 1))) 0 ^ 2 <=
      S.negativeTailSquareMass := by
  exact single_le_tsum_of_nonneg S.negative_tail_square_summable
    (fun n => sq_nonneg _) n

theorem positiveTailCubeMass_le_sqrt_positiveSquare_mul_positiveSquare
    (S : C11SpectralData W mu) :
    S.positiveTailCubeMass <=
      Real.sqrt S.positiveTailSquareMass * S.positiveTailSquareMass := by
  have hbound :
      (∑' n : Nat, max (S.expansion.eigen (n + 1) ^ 3) 0) <=
        ∑' n : Nat,
          Real.sqrt S.positiveTailSquareMass *
            max (S.expansion.eigen (n + 1)) 0 ^ 2 := by
    refine Summable.tsum_le_tsum ?_ S.positive_tail_cube_summable
      (S.positive_tail_square_summable.mul_left
        (Real.sqrt S.positiveTailSquareMass))
    intro n
    let a := S.expansion.eigen (n + 1)
    have hterm := max_cube_zero_le_sqrt_mul_sq
      (a := max a 0) (M := S.positiveTailSquareMass)
      (S.positive_tail_part_sq_le_mass n)
    have hc0 : 0 <= max a 0 := le_max_right _ _
    have hc3 : 0 <= max a 0 ^ 3 := pow_nonneg hc0 3
    rw [max_eq_left hc3] at hterm
    simpa [a, max_cube_zero_eq_pos_part_cube] using hterm
  calc
    S.positiveTailCubeMass
        <= ∑' n : Nat,
          Real.sqrt S.positiveTailSquareMass *
            max (S.expansion.eigen (n + 1)) 0 ^ 2 := hbound
    _ = Real.sqrt S.positiveTailSquareMass *
          S.positiveTailSquareMass := by
          rw [positiveTailSquareMass, tsum_mul_left]

theorem positiveTailCubeMass_le_sqrt_bound_mul_bound
    (S : C11SpectralData W mu) {B : Real}
    (_hB0 : 0 <= B) (hB : S.positiveTailSquareMass <= B) :
    S.positiveTailCubeMass <= Real.sqrt B * B := by
  have hmain :=
    S.positiveTailCubeMass_le_sqrt_positiveSquare_mul_positiveSquare
  have hmono :
      Real.sqrt S.positiveTailSquareMass * S.positiveTailSquareMass <=
        Real.sqrt B * B := by
    exact mul_le_mul (Real.sqrt_le_sqrt hB) hB
      S.positiveTailSquareMass_nonneg (Real.sqrt_nonneg B)
  exact hmain.trans hmono

private lemma negative_tail_cube_summable
    (S : C11SpectralData W mu) :
    Summable fun n : Nat => max (-(S.expansion.eigen (n + 1) ^ 3)) 0 := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_
    (hshift.mul_left (Real.sqrt (edgeDensity W mu)))
  intro n
  exact max_neg_cube_zero_le_sqrt_mul_sq (S.tail_eigen_sq_le_edge n)

private lemma cube_eq_pos_sub_neg (a : Real) :
    a ^ 3 = max (a ^ 3) 0 - max (-(a ^ 3)) 0 := by
  by_cases h : 0 <= a ^ 3
  · have hp : max (a ^ 3) 0 = a ^ 3 := max_eq_left h
    have hn : max (-(a ^ 3)) 0 = 0 := max_eq_right (by linarith)
    rw [hp, hn]
    ring
  · have hp : max (a ^ 3) 0 = 0 := max_eq_right (by linarith)
    have hn : max (-(a ^ 3)) 0 = -(a ^ 3) := max_eq_left (by linarith)
    rw [hp, hn]
    ring

theorem tailCubeSum_eq_positive_sub_negative (S : C11SpectralData W mu) :
    S.tailCubeSum = S.positiveTailCubeMass - S.negativeTailCubeMass := by
  have hpos := S.positive_tail_cube_summable
  have hnegcube := S.negative_tail_cube_summable
  calc
    S.tailCubeSum
        = ∑' n : Nat,
            (max (S.expansion.eigen (n + 1) ^ 3) 0 -
              max (-(S.expansion.eigen (n + 1) ^ 3)) 0) := by
          rw [tailCubeSum]
          apply tsum_congr
          intro n
          exact cube_eq_pos_sub_neg (S.expansion.eigen (n + 1))
    _ = S.positiveTailCubeMass - S.negativeTailCubeMass := by
          rw [hpos.tsum_sub hnegcube]
          rfl

theorem tailCubeSum_eq_trace_cube_sub_principal_cube
    (S : C11SpectralData W mu) :
    S.tailCubeSum = trace mu (compPow mu W 2) - S.principal ^ 3 := by
  calc
    S.tailCubeSum
        = (∑' n : Nat, S.expansion.eigen n ^ 3) -
            S.expansion.eigen 0 ^ 3 := by
          rw [tailCubeSum, S.summable_cube.tsum_eq_zero_add]
          ring
    _ = trace mu (compPow mu W 2) - S.principal ^ 3 := by
          rw [S.trace_cube, principal, C11SpectralExpansion.principal]

theorem tailCubeSum_lower_of_triangle
    (S : C11SpectralData W mu) {theta : Real}
    (htri : theta <= trace mu (compPow mu W 2)) :
    theta - S.principal ^ 3 <= S.tailCubeSum := by
  rw [S.tailCubeSum_eq_trace_cube_sub_principal_cube]
  linarith

theorem tailCubeSum_le_of_positiveSquare_and_negativeCube
    (S : C11SpectralData W mu) {B z : Real}
    (hB0 : 0 <= B)
    (hpos : S.positiveTailSquareMass <= B)
    (hneg : z ^ 3 <= S.negativeTailCubeMass) :
    S.tailCubeSum <= Real.sqrt B * B - z ^ 3 := by
  rw [S.tailCubeSum_eq_positive_sub_negative]
  have hposcube := S.positiveTailCubeMass_le_sqrt_bound_mul_bound hB0 hpos
  linarith

theorem triangle_le_cubic_capacity
    (S : C11SpectralData W mu) {theta B z : Real}
    (htri : theta <= trace mu (compPow mu W 2))
    (hB0 : 0 <= B)
    (hpos : S.positiveTailSquareMass <= B)
    (hneg : z ^ 3 <= S.negativeTailCubeMass) :
    theta - S.principal ^ 3 <= Real.sqrt B * B - z ^ 3 := by
  exact (S.tailCubeSum_lower_of_triangle htri).trans
    (S.tailCubeSum_le_of_positiveSquare_and_negativeCube hB0 hpos hneg)

theorem negativeTailCubeMass_lower_of_negativeMass_lower
    (S : C11SpectralData W mu) {z : Real}
    (hz0 : 0 <= z) (hz : z ^ 11 <= S.negativeMass) :
    z ^ 3 <= S.negativeTailCubeMass := by
  by_contra hnot
  have hlt : S.negativeTailCubeMass < z ^ 3 := not_le.mp hnot
  have hzpos : 0 < z := by
    by_contra hznot
    have hzle : z <= 0 := le_of_not_gt hznot
    have hz0' : z = 0 := by linarith
    rw [hz0'] at hlt
    norm_num at hlt
    linarith [S.negativeTailCubeMass_nonneg]
  have hN_le :
      S.negativeMass <= z ^ 8 * S.negativeTailCubeMass := by
    rw [negativeMass, C11SpectralExpansion.negativeMass,
      negativeEleventhTailMass, negativeTailCubeMass]
    have hbound :
        (∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 11)) 0) <=
          ∑' n : Nat,
            z ^ 8 * max (-(S.expansion.eigen (n + 1) ^ 3)) 0 := by
      refine Summable.tsum_le_tsum ?_
        S.expansion.summable_negative_eleventh_tail
        (S.negative_tail_cube_summable.mul_left (z ^ 8))
      intro n
      let b : Real := max (-(S.expansion.eigen (n + 1))) 0
      have hb0 : 0 <= b := le_max_right _ _
      have hb3_le :
          b ^ 3 <= S.negativeTailCubeMass := by
        simpa [b, negativeTailCubeMass, max_neg_cube_zero_eq_neg_part_cube]
          using single_le_tsum_of_nonneg S.negative_tail_cube_summable
            (fun n => le_max_right _ _) n
      have hb3_lt : b ^ 3 < z ^ 3 := hb3_le.trans_lt hlt
      have hb_le : b <= z := le_of_lt
        ((show Odd (3 : Nat) by norm_num).pow_lt_pow.mp hb3_lt)
      have hb8 : b ^ 8 <= z ^ 8 := pow_le_pow_left₀ hb0 hb_le 8
      calc
        max (-(S.expansion.eigen (n + 1) ^ 11)) 0
            = b ^ 11 := by
              simp [b, max_neg_eleventh_zero_eq_neg_part_eleventh]
        _ = b ^ 8 * b ^ 3 := by ring
        _ <= z ^ 8 * b ^ 3 := by
              exact mul_le_mul_of_nonneg_right hb8 (pow_nonneg hb0 3)
        _ = z ^ 8 * max (-(S.expansion.eigen (n + 1) ^ 3)) 0 := by
              simp [b, max_neg_cube_zero_eq_neg_part_cube]
    calc
      (∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 11)) 0)
          <= ∑' n : Nat,
            z ^ 8 * max (-(S.expansion.eigen (n + 1) ^ 3)) 0 := hbound
      _ = z ^ 8 * (∑' n : Nat,
            max (-(S.expansion.eigen (n + 1) ^ 3)) 0) := by
            rw [tsum_mul_left]
  have hstrict : z ^ 8 * S.negativeTailCubeMass < z ^ 11 := by
    have hm := mul_lt_mul_of_pos_left hlt (pow_pos hzpos 8)
    nlinarith
  linarith

private lemma nonneg_lt_of_sq_lt_sq {b z : Real}
    (hb0 : 0 <= b) (hz0 : 0 <= z) (h : b ^ 2 < z ^ 2) :
    b < z := by
  by_contra hnot
  have hzb : z <= b := le_of_not_gt hnot
  have hdiff : 0 <= b - z := by linarith
  have hsum : 0 <= b + z := by linarith
  have hprod := mul_nonneg hdiff hsum
  nlinarith

theorem negativeTailSquareMass_lower_of_negativeMass_lower
    (S : C11SpectralData W mu) {z : Real}
    (hz0 : 0 <= z) (hz : z ^ 11 <= S.negativeMass) :
    z ^ 2 <= S.negativeTailSquareMass := by
  by_contra hnot
  have hlt : S.negativeTailSquareMass < z ^ 2 := not_le.mp hnot
  have hzpos : 0 < z := by
    by_contra hznot
    have hzle : z <= 0 := le_of_not_gt hznot
    have hz0' : z = 0 := by linarith
    rw [hz0'] at hlt
    norm_num at hlt
    linarith [S.negativeTailSquareMass_nonneg]
  have hN_le :
      S.negativeMass <= z ^ 9 * S.negativeTailSquareMass := by
    rw [negativeMass, C11SpectralExpansion.negativeMass,
      negativeEleventhTailMass, negativeTailSquareMass]
    have hbound :
        (∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 11)) 0) <=
          ∑' n : Nat,
            z ^ 9 * max (-(S.expansion.eigen (n + 1))) 0 ^ 2 := by
      refine Summable.tsum_le_tsum ?_
        S.expansion.summable_negative_eleventh_tail
        (S.negative_tail_square_summable.mul_left (z ^ 9))
      intro n
      let b : Real := max (-(S.expansion.eigen (n + 1))) 0
      have hb0 : 0 <= b := le_max_right _ _
      have hb2_le :
          b ^ 2 <= S.negativeTailSquareMass := by
        simpa [b, negativeTailSquareMass]
          using single_le_tsum_of_nonneg S.negative_tail_square_summable
            (fun n => sq_nonneg _) n
      have hb2_lt : b ^ 2 < z ^ 2 := hb2_le.trans_lt hlt
      have hb_le : b <= z := le_of_lt (nonneg_lt_of_sq_lt_sq hb0 hz0 hb2_lt)
      have hb9 : b ^ 9 <= z ^ 9 := pow_le_pow_left₀ hb0 hb_le 9
      calc
        max (-(S.expansion.eigen (n + 1) ^ 11)) 0
            = b ^ 11 := by
              simp [b, max_neg_eleventh_zero_eq_neg_part_eleventh]
        _ = b ^ 9 * b ^ 2 := by ring
        _ <= z ^ 9 * b ^ 2 := by
              exact mul_le_mul_of_nonneg_right hb9 (sq_nonneg b)
        _ = z ^ 9 * max (-(S.expansion.eigen (n + 1))) 0 ^ 2 := by
              simp [b]
    calc
      (∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 11)) 0)
          <= ∑' n : Nat,
            z ^ 9 * max (-(S.expansion.eigen (n + 1))) 0 ^ 2 := hbound
      _ = z ^ 9 * (∑' n : Nat,
            max (-(S.expansion.eigen (n + 1))) 0 ^ 2) := by
            rw [tsum_mul_left]
  have hstrict : z ^ 9 * S.negativeTailSquareMass < z ^ 11 := by
    have hm := mul_lt_mul_of_pos_left hlt (pow_pos hzpos 9)
    nlinarith
  linarith

def ScalarCapacityExclusion (S : C11SpectralData W mu) : Prop :=
  ∀ {c z : Real},
    0 <= c ->
    c <= 1 / 3 ->
    edgeDensity W mu = 1 / 2 + c - (3 / 2) * c ^ 2 ->
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 103 / 200 ->
    0 <= z ->
    S.principal ^ 11 - edgeDensity W mu ^ 11 +
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 < z ^ 11 ->
    0 <= edgeDensity W mu - S.principal ^ 2 - z ^ 2 ->
    Real.sqrt (edgeDensity W mu - S.principal ^ 2 - z ^ 2) *
        (edgeDensity W mu - S.principal ^ 2 - z ^ 2) - z ^ 3 <
      (3 / 2) * c * (1 - c) ^ 2 - S.principal ^ 3

/-- The pure C11 scalar capacity exclusion.  The proof combines the
Razborov-parameter lower bound, the C11 endpoint certificates, and the
algebraic reduction from the principal eigenvalue to `ell = p`. -/
theorem scalarCapacityExclusion
    (S : C11SpectralData W mu) :
    S.ScalarCapacityExclusion := by
  intro c z hc0 hc13 hp hgt hle hz0 hztarget hbudget
  let p : Real := edgeDensity W mu
  let q : Real := 1 - p
  let eps : Real := p - 1 / 2
  let theta : Real := (3 / 2) * c * (1 - c) ^ 2
  have hp0 : 0 <= p := by dsimp [p]; linarith
  have hp_half : 1 / 2 <= p := by dsimp [p]; linarith
  have hpell : p <= S.principal := by
    dsimp [p, principal]
    exact S.principal_ge_edge
  have hq0 : 0 <= q := by
    dsimp [q, p]
    nlinarith
  have hqle : q <= p := by
    dsimp [q, p]
    linarith
  have heps0 : 0 <= eps := by
    dsimp [eps, p]
    linarith
  have heps1 : eps <= 3 / 200 := by
    dsimp [eps, p]
    linarith
  have hp_eps : p = 1 / 2 + eps := by
    dsimp [eps]
    ring
  have hq_eps : q = 1 / 2 - eps := by
    dsimp [q, eps]
    ring
  have hpell11 : p ^ 11 <= S.principal ^ 11 :=
    pow_le_pow_left₀ hp0 hpell 11
  have hpq10_nonneg : 0 <= p * q ^ 10 :=
    mul_nonneg hp0 (pow_nonneg hq0 10)
  have hAlphaArg0 :
      0 <= S.principal ^ 11 - p ^ 11 + p * q ^ 10 := by
    nlinarith
  obtain ⟨alpha, halpha0, halpha11⟩ :=
    exists_nonneg_eleventh_root hAlphaArg0
  have hAlpha0Arg0 : 0 <= p * q ^ 10 := hpq10_nonneg
  obtain ⟨alpha0, halpha00, halpha011⟩ :=
    exists_nonneg_eleventh_root hAlpha0Arg0
  have halpha_lt_z_eleventh : alpha ^ 11 < z ^ 11 := by
    rw [halpha11]
    simpa [p, q] using hztarget
  have halpha_le_z : alpha <= z :=
    (show Odd (11 : Nat) by norm_num).pow_le_pow.mp
      (le_of_lt halpha_lt_z_eleventh)
  have hDeltaAlpha : 0 <= p - S.principal ^ 2 - alpha ^ 2 := by
    have hsq : alpha ^ 2 <= z ^ 2 := pow_le_pow_left₀ halpha0 halpha_le_z 2
    nlinarith
  have hcapacity_lt :=
    LowBand.C11.cubic_capacity_strict_decreases_of_eleventh
      (S := p - S.principal ^ 2) halpha0 hz0 halpha_lt_z_eleventh hbudget
  have htheta_lower :
      (3 / 2) * ((64 / 65) ^ 2) * (eps + (3 / 2) * eps ^ 2) <= theta := by
    have heps_param : eps = c - (3 / 2) * c ^ 2 := by
      dsimp [eps, p]
      rw [hp]
      ring
    exact LowBand.C11.theta_quadratic_lower_of_razborov
      hc0 hc13 heps_param heps1 rfl
  have hell :=
    LowBand.C11.ell_reduction_bound
      (p := p) (q := q) (ell := S.principal)
      (alpha0 := alpha0) (alpha := alpha)
      hp0 hp_half halpha00 hpell halpha011 halpha11 hDeltaAlpha
  have hend :=
    LowBand.C11.endpoint_scalar_bound
      heps0 heps1 hp_eps hq_eps halpha011 htheta_lower
  have hpq_eq : p * q = p - p ^ 2 := by
    dsimp [q]
    ring
  have hell' :
      S.principal ^ 3 - alpha ^ 3 +
          Real.sqrt (p - S.principal ^ 2 - alpha ^ 2) *
            (p - S.principal ^ 2 - alpha ^ 2) <=
        p ^ 3 - alpha0 ^ 3 +
          Real.sqrt (p * q - alpha0 ^ 2) *
            (p * q - alpha0 ^ 2) := by
    rw [hpq_eq]
    exact hell
  have hend' :
      p ^ 3 - alpha0 ^ 3 +
          Real.sqrt (p * q - alpha0 ^ 2) *
            (p * q - alpha0 ^ 2) <= theta := hend
  have halpha_capacity_le :
      Real.sqrt (p - S.principal ^ 2 - alpha ^ 2) *
          (p - S.principal ^ 2 - alpha ^ 2) - alpha ^ 3 <=
        theta - S.principal ^ 3 := by
    nlinarith
  have hstrict :=
    hcapacity_lt.trans_le halpha_capacity_le
  simpa [p, theta] using hstrict

def ClosureEstimate (S : C11SpectralData W mu) : Prop :=
  LowBand.InfiniteSpectral.RazborovTriangleLower W mu ->
  S.ScalarCapacityExclusion ->
  1 / 2 < edgeDensity W mu ->
  edgeDensity W mu <= 103 / 200 ->
  S.negativeMass <=
    S.principal ^ 11 - edgeDensity W mu ^ 11 +
      edgeDensity W mu * (1 - edgeDensity W mu) ^ 10

theorem closureEstimate
    (S : C11SpectralData W mu) :
    S.ClosureEstimate := by
  intro htri hscalar hgt hle
  rcases htri with ⟨c, hc0, hc13, hp, htheta⟩
  by_contra htarget
  have hlt :
      S.principal ^ 11 - edgeDensity W mu ^ 11 +
          edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 <
        S.negativeMass := not_le.mp htarget
  obtain ⟨z, hz0, hzpow⟩ := exists_nonneg_eleventh_root S.negativeMass_nonneg
  have hzle : z ^ 11 <= S.negativeMass := by rw [hzpow]
  have hnegcube := S.negativeTailCubeMass_lower_of_negativeMass_lower hz0 hzle
  have hnegsq := S.negativeTailSquareMass_lower_of_negativeMass_lower hz0 hzle
  have hB0 : 0 <= edgeDensity W mu - S.principal ^ 2 - z ^ 2 := by
    have hpos := S.positiveTailSquareMass_nonneg
    have hbudget := S.tailSquareMass_le_edge_sub_principal_sq
    rw [S.tailSquareMass_eq_positive_add_negative] at hbudget
    linarith
  have hpos :=
    S.positiveTailSquareMass_le_edge_sub_principal_sq_sub_sq hnegsq
  let theta : Real := (3 / 2) * c * (1 - c) ^ 2
  have hcapacity :
      theta - S.principal ^ 3 <=
        Real.sqrt (edgeDensity W mu - S.principal ^ 2 - z ^ 2) *
          (edgeDensity W mu - S.principal ^ 2 - z ^ 2) - z ^ 3 := by
    exact S.triangle_le_cubic_capacity htheta hB0 hpos hnegcube
  have hstrict :
      Real.sqrt (edgeDensity W mu - S.principal ^ 2 - z ^ 2) *
          (edgeDensity W mu - S.principal ^ 2 - z ^ 2) - z ^ 3 <
        theta - S.principal ^ 3 := by
    have hltz :
        S.principal ^ 11 - edgeDensity W mu ^ 11 +
            edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 < z ^ 11 := by
      rwa [← hzpow] at hlt
    exact hscalar hc0 hc13 hp hgt hle hz0 hltz hB0
  linarith

theorem c11_cycle_bound_of_closure
    (S : C11SpectralData W mu)
    (htri : LowBand.InfiniteSpectral.RazborovTriangleLower W mu)
    (hscalar : S.ScalarCapacityExclusion)
    (hgt : 1 / 2 < edgeDensity W mu)
    (hle : edgeDensity W mu <= 103 / 200) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  exact S.c11_cycle_bound_of_mass_bound rfl
    (S.closureEstimate htri hscalar hgt hle)

/-- C11 in the low band from Razborov and countable spectral data. -/
theorem c11_cycle_bound_of_razborov
    (S : C11SpectralData W mu)
    (htri : LowBand.InfiniteSpectral.RazborovTriangleLower W mu)
    (hgt : 1 / 2 < edgeDensity W mu)
    (hle : edgeDensity W mu <= 103 / 200) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  exact S.c11_cycle_bound_of_closure htri S.scalarCapacityExclusion hgt hle

end C11SpectralData

end InfiniteSpectral
end LowBand
end OddCycleBound
