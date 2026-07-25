import OddCycleBound.Necklace
import OddCycleBound.Spectral.C9Scalar
import OddCycleBound.Spectral.CompactGraphonOperator
import OddCycleBound.Spectral.GraphonL2Operator
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Infinite spectral data for the low-band C9 argument

The graphon operator need not have finitely many non-zero eigenvalues.  This
module therefore records the spectral step in the shape needed for compact
self-adjoint graphon operators: a countable eigenvalue sequence, summability of
the ninth moment, and a trace identity expressed with `tsum`.

This still does **not** assert Razborov's triangle-density theorem, nor does it
assert the trace-class/Lidskii bridge for graphons.  Those are exposed as
ordinary hypotheses.  The theorem proved here is the infinite-series operator
bookkeeping: once the graphon trace moments are represented by a countable
eigenvalue series, the ninth trace is bounded below by the principal ninth
power minus the negative ninth mass of the non-principal tail.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound
namespace Spectral
namespace InfiniteSpectral

universe u

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/-- The negative ninth-power mass of all non-principal modes in a countable
spectral expansion whose principal mode is indexed by `0`. -/
def negativeNinthTailMass (eigen : Nat -> Real) : Real :=
  ∑' n : Nat, max (-(eigen (n + 1) ^ 9)) 0

private lemma neg_max_neg_zero_le_self (a : Real) : -max (-a) 0 <= a := by
  by_cases ha : 0 <= a
  · have hmax : max (-a) 0 = 0 := max_eq_right (by linarith)
    rw [hmax]
    linarith
  · have hmax : max (-a) 0 = -a := max_eq_left (by linarith)
    rw [hmax]
    linarith

/-- Infinite-series form of the negative-tail lower bound.

This is the countable analogue of splitting off the largest eigenvalue in the
finite-dimensional spectral sum. -/
lemma principal_sub_negativeNinthTailMass_le_tsum
    (eigen : Nat -> Real)
    (hsum : Summable fun n : Nat => eigen n ^ 9)
    (hneg : Summable fun n : Nat => max (-(eigen (n + 1) ^ 9)) 0) :
    eigen 0 ^ 9 - negativeNinthTailMass eigen <= ∑' n : Nat, eigen n ^ 9 := by
  have hshift : Summable fun n : Nat => eigen (n + 1) ^ 9 :=
    (summable_nat_add_iff 1).2 hsum
  have hneg' : Summable fun n : Nat => -(max (-(eigen (n + 1) ^ 9)) 0) :=
    hneg.neg
  have hle_tail :
      (∑' n : Nat, -(max (-(eigen (n + 1) ^ 9)) 0))
        <= ∑' n : Nat, eigen (n + 1) ^ 9 := by
    exact Summable.tsum_le_tsum
      (fun n => neg_max_neg_zero_le_self (eigen (n + 1) ^ 9)) hneg' hshift
  calc
    eigen 0 ^ 9 - negativeNinthTailMass eigen
        = eigen 0 ^ 9 + ∑' n : Nat, -(max (-(eigen (n + 1) ^ 9)) 0) := by
          rw [negativeNinthTailMass, tsum_neg]
          ring
    _ <= eigen 0 ^ 9 + ∑' n : Nat, eigen (n + 1) ^ 9 := by
          linarith
    _ = ∑' n : Nat, eigen n ^ 9 := by
          rw [hsum.tsum_eq_zero_add]

/-- Countable spectral expansion data for the ninth trace of a graphon kernel.

For a genuine graphon proof, this is the place where the compact
self-adjoint/Hilbert-Schmidt theory and the trace formula should enter.  The
important point is that the interface is countably infinite, not finite-rank. -/
structure C9SpectralExpansion
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  eigen : Nat -> Real
  summable_ninth : Summable fun n : Nat => eigen n ^ 9
  summable_negative_ninth_tail :
    Summable fun n : Nat => max (-(eigen (n + 1) ^ 9)) 0
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

namespace C9SpectralExpansion

/-- Principal eigenvalue in the chosen countable spectral ordering. -/
def principal (S : C9SpectralExpansion W mu) : Real := S.eigen 0

/-- Negative ninth-power mass of the non-principal tail. -/
def negativeMass (S : C9SpectralExpansion W mu) : Real :=
  negativeNinthTailMass S.eigen

/-- The grounded infinite-spectral trace lower bound used by the C9 low-band
argument. -/
theorem principal_pow_sub_negativeMass_le_trace
    (S : C9SpectralExpansion W mu) :
    S.principal ^ 9 - S.negativeMass <= trace mu (compPow mu W 8) := by
  rw [S.trace_ninth, principal, negativeMass]
  exact principal_sub_negativeNinthTailMass_le_tsum S.eigen
    S.summable_ninth S.summable_negative_ninth_tail

/-- C9 follows from an infinite spectral expansion plus the genuine analytic
negative-mass estimate.

The remaining hard estimate is intentionally exposed as `hmass`.  It is the
part to be obtained from the triangle-density lower bound and the Hilbert
operator inequalities; the trace/eigenvalue bookkeeping itself is proved above
for countably many eigenvalues. -/
theorem c9_cycle_bound_of_mass_bound
    (S : C9SpectralExpansion W mu)
    {q : Real}
    (hq : q = 1 - edgeDensity W mu)
    (hmass :
      S.negativeMass <=
        S.principal ^ 9 - edgeDensity W mu ^ 9 + edgeDensity W mu * q ^ 8) :
    trace mu (compPow mu W 8) >=
      edgeDensity W mu ^ 9 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 := by
  exact Spectral.C9.cycle_bound_of_negative_mass_bound
    hq S.principal_pow_sub_negativeMass_le_trace hmass

end C9SpectralExpansion

/-- Razborov/Reiher triangle-density lower bound in the near-bipartite
parameterization used by the paper.

This is a proposition, not an axiom.  The low-band argument may assume this
proposition for `W`, or a later file may prove it. -/
def RazborovTriangleLower
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  ∃ c : Real,
    0 <= c ∧ c <= 1 / 3 ∧
    edgeDensity W mu = 1 / 2 + c - (3 / 2) * c ^ 2 ∧
    (3 / 2) * c * (1 - c) ^ 2 <= trace mu (compPow mu W 2)

/-- Direct low-band Razborov/Reiher triangle-density statement for C9.

This is the graphon-facing form: it states the lower bound as a function of
the edge density alone, using the standard parameter
`c(p) = (1 - sqrt (4 - 6p)) / 3` on the branch `1 / 2 <= p <= 2 / 3`. -/
def C9RazborovTriangleDensityDirectTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    let c := (1 - Real.sqrt (4 - 6 * edgeDensity W mu)) / 3
    (3 / 2) * c * (1 - c) ^ 2 <= trace mu (compPow mu W 2)

private lemma razborov_direct_param_nonneg {p : Real}
    (hgt : 1 / 2 < p)
    (hle : p <= 1003 / 2000) :
    0 <= (1 - Real.sqrt (4 - 6 * p)) / 3 := by
  have harg0 : 0 <= 4 - 6 * p := by
    nlinarith [hle, (show (1003 : Real) / 2000 < 2 / 3 by norm_num)]
  have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p := by
    exact Real.sq_sqrt harg0
  have hs_sq_le_one : (Real.sqrt (4 - 6 * p)) ^ 2 <= (1 : Real) ^ 2 := by
    rw [hs_sq]
    nlinarith
  have hs_le_one : Real.sqrt (4 - 6 * p) <= 1 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : Real) <= 1)).mp hs_sq_le_one
  nlinarith

private lemma razborov_direct_param_le_third {p : Real} :
    (1 - Real.sqrt (4 - 6 * p)) / 3 <= 1 / 3 := by
  have hs0 : 0 <= Real.sqrt (4 - 6 * p) := Real.sqrt_nonneg _
  nlinarith

private lemma razborov_direct_param_edge_eq {p : Real}
    (hle : p <= 1003 / 2000) :
    p = 1 / 2 + (1 - Real.sqrt (4 - 6 * p)) / 3 -
        (3 / 2) * ((1 - Real.sqrt (4 - 6 * p)) / 3) ^ 2 := by
  have harg0 : 0 <= 4 - 6 * p := by
    nlinarith [hle, (show (1003 : Real) / 2000 < 2 / 3 by norm_num)]
  have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p := by
    exact Real.sq_sqrt harg0
  nlinarith

/-- The low-band instance of Razborov/Reiher needed by the C9 proof.

This is deliberately a named `Prop`, not an axiom.  A final C9 theorem may
assume this proposition, or a future file may prove it. -/
def C9RazborovTriangleDensityTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    RazborovTriangleLower W mu

/-- The direct edge-density form of the low-band Razborov/Reiher statement
implies the parameterized form consumed by the C9 spectral closure argument. -/
theorem C9RazborovTriangleDensityTheorem.of_direct
    (htri : C9RazborovTriangleDensityDirectTheorem.{u}) :
    C9RazborovTriangleDensityTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  let p := edgeDensity W mu
  let c := (1 - Real.sqrt (4 - 6 * p)) / 3
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · exact razborov_direct_param_nonneg hgt hle
  · exact razborov_direct_param_le_third
  · dsimp [c, p]
    exact razborov_direct_param_edge_eq hle
  · dsimp [c, p]
    exact htri hW hgt hle

/-- The C9 low-band Razborov/Reiher input for one fixed graphon. -/
def C9RazborovTriangleDensityFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  IsGraphon W mu ->
  1 / 2 < edgeDensity W mu ->
  edgeDensity W mu <= 1003 / 2000 ->
  RazborovTriangleLower W mu

/-- The named global Razborov/Reiher proposition gives the fixed-graphon
low-band input.  This is only a conditional bridge; it introduces no axiom. -/
theorem C9RazborovTriangleDensityFor.of_theorem
    {Omega' : Type u} [MeasurableSpace Omega']
    {mu' : Measure Omega'} [IsProbabilityMeasure mu']
    {W' : Omega' -> Omega' -> Real}
    (htri : C9RazborovTriangleDensityTheorem.{u}) :
    C9RazborovTriangleDensityFor W' mu' := by
  intro hW hgt hle
  exact htri (Omega := Omega') (mu := mu') (W := W') hW hgt hle

/-- The remaining pure real-variable C9 low-band exclusion.

This is exactly the scalar contradiction left after the countable spectral
bookkeeping: if a putative negative-tail root `z` lies above the target
threshold and still leaves nonnegative square bound, then the cubic capacity
is strictly below the linear triangle slack. -/
def C9LinearScalarCapacityExclusion : Prop :=
  ∀ {p ell z : Real},
    1 / 2 < p ->
    p <= 1003 / 2000 ->
    p <= ell ->
    0 <= z ->
    ell ^ 9 - p ^ 9 + p * (1 - p) ^ 8 < z ^ 9 ->
    0 <= p - ell ^ 2 - z ^ 2 ->
    Real.sqrt (p - ell ^ 2 - z ^ 2) *
        (p - ell ^ 2 - z ^ 2) - z ^ 3 <
      (149 / 100) * (p - 1 / 2) - ell ^ 3

private lemma exists_nonneg_ninth_root {x : Real} (hx : 0 <= x) :
    ∃ z : Real, 0 <= z ∧ z ^ 9 = x := by
  obtain ⟨r, hr⟩ :=
    NNReal.rpow_left_surjective
      (by norm_num : (9 : Real) ≠ 0) x.toNNReal
  refine ⟨(r : Real), NNReal.coe_nonneg r, ?_⟩
  have hcoe : ((r ^ (9 : Real) : NNReal) : Real) = x := by
    simp [hr, Real.coe_toNNReal x hx]
  simpa [NNReal.coe_rpow, Real.rpow_natCast] using hcoe

/-- The pure scalar C9 capacity exclusion.  The proof uses the endpoint
polynomial estimates and the algebraic `ell`-reduction in `Spectral.C9`. -/
theorem c9LinearScalarCapacityExclusion :
    C9LinearScalarCapacityExclusion := by
  intro p ell z hgt hle hpell hz0 hztarget hbound
  let q : Real := 1 - p
  let eps : Real := p - 1 / 2
  have hp0 : 0 <= p := by linarith
  have hq0 : 0 <= q := by
    dsimp [q]
    nlinarith
  have hqle : q <= p := by
    dsimp [q]
    linarith
  have heps0 : 0 <= eps := by
    dsimp [eps]
    linarith
  have heps1 : eps <= 3 / 2000 := by
    dsimp [eps]
    linarith
  have hp_eps : p = 1 / 2 + eps := by
    dsimp [eps]
    ring
  have hq_eps : q = 1 / 2 - eps := by
    dsimp [q, eps]
    ring
  have hpell9 : p ^ 9 <= ell ^ 9 := pow_le_pow_left₀ hp0 hpell 9
  have hpq8_nonneg : 0 <= p * q ^ 8 :=
    mul_nonneg hp0 (pow_nonneg hq0 8)
  have hAlphaArg0 : 0 <= ell ^ 9 - p ^ 9 + p * q ^ 8 := by
    nlinarith
  obtain ⟨alpha, halpha0, halpha9⟩ :=
    exists_nonneg_ninth_root hAlphaArg0
  have hAlpha0Arg0 : 0 <= p * q ^ 8 := hpq8_nonneg
  obtain ⟨alpha0, halpha00, halpha09⟩ :=
    exists_nonneg_ninth_root hAlpha0Arg0
  have halpha0_le_p : alpha0 <= p := by
    have hq8le : q ^ 8 <= p ^ 8 := pow_le_pow_left₀ hq0 hqle 8
    have hpq8le : p * q ^ 8 <= p ^ 9 := by
      have hm := mul_le_mul_of_nonneg_left hq8le hp0
      nlinarith
    have hpow : alpha0 ^ 9 <= p ^ 9 := by
      rw [halpha09]
      exact hpq8le
    exact (show Odd (9 : Nat) by norm_num).pow_le_pow.mp hpow
  have halpha_lt_z_ninth : alpha ^ 9 < z ^ 9 := by
    rw [halpha9]
    simpa [q] using hztarget
  have halpha_le_z : alpha <= z :=
    (show Odd (9 : Nat) by norm_num).pow_le_pow.mp (le_of_lt halpha_lt_z_ninth)
  have hDeltaAlpha : 0 <= p - ell ^ 2 - alpha ^ 2 := by
    have hsq : alpha ^ 2 <= z ^ 2 := pow_le_pow_left₀ halpha0 halpha_le_z 2
    nlinarith
  have hcapacity_lt :=
    Spectral.C9.cubic_capacity_strict_decreases_of_ninth
      (S := p - ell ^ 2) halpha0 hz0 halpha_lt_z_ninth hbound
  have hell :=
    Spectral.C9.ell_reduction_bound
      (p := p) (q := q) (ell := ell) (alpha0 := alpha0) (alpha := alpha)
      hp0 halpha00 halpha0_le_p hpell halpha09 halpha9 hDeltaAlpha
  have hend :=
    Spectral.C9.endpoint_scalar_bound
      heps0 heps1 hp_eps hq_eps halpha00 halpha09
  have hpq_eq : p * q = p - p ^ 2 := by
    dsimp [q]
    ring
  have hell' :
      ell ^ 3 - alpha ^ 3 +
          Real.sqrt (p - ell ^ 2 - alpha ^ 2) *
            (p - ell ^ 2 - alpha ^ 2) <=
        p ^ 3 - alpha0 ^ 3 +
          Real.sqrt (p * q - alpha0 ^ 2) *
            (p * q - alpha0 ^ 2) := by
    rwa [hpq_eq]
  have hend' :
      p ^ 3 - alpha0 ^ 3 +
          Real.sqrt (p * q - alpha0 ^ 2) *
            (p * q - alpha0 ^ 2) <=
        (149 / 100) * (p - 1 / 2) := by
    simpa [eps] using hend
  have halpha_capacity_le :
      Real.sqrt (p - ell ^ 2 - alpha ^ 2) *
          (p - ell ^ 2 - alpha ^ 2) - alpha ^ 3 <=
        (149 / 100) * (p - 1 / 2) - ell ^ 3 := by
    nlinarith
  exact hcapacity_lt.trans_le halpha_capacity_le

/-- Countable spectral data used by the C9 near-bipartite argument.

Compared with `C9SpectralExpansion`, this records the additional spectral
facts used in the proof of the negative-mass estimate: the square bound, the
cube trace identity, and the Rayleigh lower bound on the principal eigenvalue.
These are the Hilbert-operator inputs that should eventually be proved for the
graphon integral operator. -/
structure C9SpectralData
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  expansion : C9SpectralExpansion W mu
  summable_square : Summable fun n : Nat => expansion.eigen n ^ 2
  summable_cube : Summable fun n : Nat => expansion.eigen n ^ 3
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, expansion.eigen n ^ 3
  square_bound :
    (∑' n : Nat, expansion.eigen n ^ 2) <= edgeDensity W mu
  principal_ge_edge :
    edgeDensity W mu <= expansion.eigen 0

/-- The two-cycle trace of a graphon is bounded by its edge density.

This is the integral `0 <= W <= 1` part of the Hilbert-Schmidt square-bound
argument.  It is not a spectral assumption: it follows from the existing
edge-deletion lemma with `k = 0`. -/
theorem trace_compPow_one_le_edge
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) :
    trace mu (compPow mu W 1) <= edgeDensity W mu := by
  have h := edge_deletion_general (U := W) hW 0
  rw [pathDensity_one hW] at h
  simpa [cycleDensity] using h

/-- The Hilbert-Schmidt square mass of a graphon kernel is bounded by its edge
density.

This is the square-bound estimate in kernel-norm form.  The identity
`trace(W ∘ W) = ‖W‖²_HS` is proved in `L2Kernel`; the inequality itself is the
existing integral edge-deletion bound. -/
theorem kernelSqNorm_le_edge
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) :
    L2Kernel.kernelSqNorm mu W <= edgeDensity W mu := by
  rw [← L2Kernel.trace_compPow_one_eq_kernelSqNorm (mu := mu) hW]
  exact trace_compPow_one_le_edge hW

/-- Finite partial square estimates imply the infinite square summability and
bound.

This is the series bridge needed after a Hilbert-Schmidt/Bessel argument
proves `∑_{n<N} λ_n^2 <= B` for every finite initial segment. -/
theorem summable_square_and_tsum_le_of_sum_range_square_le
    (eigen : Nat -> Real) {B : Real}
    (hpartial : ∀ N : Nat, (Finset.range N).sum (fun n => eigen n ^ 2) <= B) :
    Summable (fun n : Nat => eigen n ^ 2) ∧
      (∑' n : Nat, eigen n ^ 2) <= B := by
  exact
    ⟨summable_of_sum_range_le (fun n => sq_nonneg (eigen n)) hpartial,
      Real.tsum_le_of_sum_range_le (fun n => sq_nonneg (eigen n)) hpartial⟩

private lemma single_le_tsum_of_nonneg {f : Nat -> Real}
    (hf : Summable f) (hnonneg : ∀ n, 0 <= f n) (n : Nat) :
    f n <= ∑' n, f n := by
  have h := hf.sum_le_tsum ({n} : Finset Nat) (fun i _ => hnonneg i)
  simpa using h

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

private lemma abs_ninth_le_sq_of_sq_le_one {a : Real} (ha : a ^ 2 <= 1) :
    |a ^ 9| <= a ^ 2 := by
  rw [abs_pow]
  have habs_sq : |a| ^ 2 <= 1 := by
    simpa [sq_abs] using ha
  have habs_le : |a| <= 1 := by
    have h0 : 0 <= |a| := abs_nonneg a
    nlinarith [sq_nonneg (|a| - 1)]
  have hpow7 : |a| ^ 7 <= 1 := by
    exact (pow_le_one₀ (abs_nonneg a) habs_le : |a| ^ 7 <= 1)
  calc
    |a| ^ 9 = |a| ^ 7 * |a| ^ 2 := by ring
    _ <= 1 * |a| ^ 2 := by
      exact mul_le_mul_of_nonneg_right hpow7 (sq_nonneg |a|)
    _ = |a| ^ 2 := one_mul _
    _ = a ^ 2 := by rw [sq_abs]

private lemma max_neg_ninth_le_sq_of_sq_le_one {a : Real} (ha : a ^ 2 <= 1) :
    max (-(a ^ 9)) 0 <= a ^ 2 := by
  have h_abs := abs_ninth_le_sq_of_sq_le_one ha
  exact max_le (by linarith [neg_le_abs (a ^ 9)]) (sq_nonneg a)

private lemma summable_cube_of_summable_square_of_tsum_le_one
    {eigen : Nat -> Real}
    (hsq : Summable fun n : Nat => eigen n ^ 2)
    (hle : (∑' n : Nat, eigen n ^ 2) <= 1) :
    Summable fun n : Nat => eigen n ^ 3 := by
  refine hsq.of_norm_bounded ?_
  intro n
  exact abs_cube_le_sq_of_sq_le_one
    ((single_le_tsum_of_nonneg hsq (fun n => sq_nonneg _) n).trans hle)

private lemma summable_ninth_of_summable_square_of_tsum_le_one
    {eigen : Nat -> Real}
    (hsq : Summable fun n : Nat => eigen n ^ 2)
    (hle : (∑' n : Nat, eigen n ^ 2) <= 1) :
    Summable fun n : Nat => eigen n ^ 9 := by
  refine hsq.of_norm_bounded ?_
  intro n
  exact abs_ninth_le_sq_of_sq_le_one
    ((single_le_tsum_of_nonneg hsq (fun n => sq_nonneg _) n).trans hle)

private lemma summable_negative_ninth_tail_of_summable_square_of_tsum_le_one
    {eigen : Nat -> Real}
    (hsq : Summable fun n : Nat => eigen n ^ 2)
    (hle : (∑' n : Nat, eigen n ^ 2) <= 1) :
    Summable fun n : Nat => max (-(eigen (n + 1) ^ 9)) 0 := by
  have hshift : Summable fun n : Nat => eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 hsq
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_ hshift
  intro n
  exact max_neg_ninth_le_sq_of_sq_le_one
    ((single_le_tsum_of_nonneg hsq (fun n => sq_nonneg _) (n + 1)).trans hle)

/-- Countable spectral trace data before the elementary graphon square-bound
inequality has been applied.

This is a more operator-faithful interface than `C9SpectralData`: the Hilbert
package supplies the square trace identity `trace(W^2) = ∑ λ_n^2`, while Lean
derives `∑ λ_n^2 <= p` from `0 <= W <= 1`. -/
structure C9TraceSpectralData
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  expansion : C9SpectralExpansion W mu
  summable_square : Summable fun n : Nat => expansion.eigen n ^ 2
  summable_cube : Summable fun n : Nat => expansion.eigen n ^ 3
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, expansion.eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, expansion.eigen n ^ 3
  principal_ge_edge :
    edgeDensity W mu <= expansion.eigen 0

/-- Raw countable trace data before summability of higher powers has been
derived from the square trace.

The operator-theoretic layer supplies the eigenvalue sequence, square
summability, the square/cube/ninth trace identities, and the principal Rayleigh
bound.  Lean derives the cubic and ninth summability assumptions needed by the
series bookkeeping from `∑ λ_n^2 <= edgeDensity W mu <= 1`. -/
structure C9RawTraceSpectralData
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  eigen : Nat -> Real
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9
  principal_ge_edge :
    edgeDensity W mu <= eigen 0

/-- Countable trace data with the square information stated as the bound
actually consumed by C9.

This removes the square Lidskii identity from the low-band hypothesis.  The
operator layer still supplies square summability and the cube/ninth trace
identities, but for the square moment it only has to prove
`∑ λ_n^2 <= edgeDensity W μ`.  That inequality is the Hilbert-Schmidt/Bessel
estimate one expects before proving the full trace formula. -/
structure C9BoundTraceSpectralData
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  eigen : Nat -> Real
  summable_square : Summable fun n : Nat => eigen n ^ 2
  square_bound :
    (∑' n : Nat, eigen n ^ 2) <= edgeDensity W mu
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9
  principal_ge_edge :
    edgeDensity W mu <= eigen 0

/-- Direct `HasSum` trace data before converting to the raw `tsum` package.

This is the minimal countable spectral interface consumed by the C9 low-band
proof: it records convergence and values of the square, cube, and ninth trace
series, together with the principal lower bound `edgeDensity W μ <= λ₀`.
It makes no finite-spectrum assertion and does not require a globally sorted
eigenvalue list. -/
structure C9HasSumTraceSpectralData
    (W : Omega -> Omega -> Real) (mu : Measure Omega) where
  eigen : Nat -> Real
  trace_square_hasSum :
    HasSum (fun n : Nat => eigen n ^ 2) (trace mu (compPow mu W 1))
  trace_cube_hasSum :
    HasSum (fun n : Nat => eigen n ^ 3) (trace mu (compPow mu W 2))
  trace_ninth_hasSum :
    HasSum (fun n : Nat => eigen n ^ 9) (trace mu (compPow mu W 8))
  principal_ge_edge :
    edgeDensity W mu <= eigen 0

/-- Operator-facing raw trace data on `L²`.

Compared with `C9RawTraceSpectralData`, this does not assume the principal
Rayleigh bound directly.  Instead it asks for an actual continuous linear
operator on `Lp ℝ 2 μ`, its action on the constant-one vector, and domination
of the quadratic form by the principal spectral value.  The graphon identity
`⟪1, T 1⟫ = edgeDensity W μ` is then proved in `L2Kernel` and used below to
derive `edgeDensity W μ <= eigen 0`.

The remaining hard operator theorem is to construct this operator from the
graphon kernel and prove compactness/trace identities; no finite-rank or
finite-spectrum approximation is used here. -/
structure C9L2OperatorTraceSpectralData
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  operator : Lp Real 2 mu →L[Real] Lp Real 2 mu
  eigen : Nat -> Real
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9
  maps_one :
    operator (L2Kernel.oneL2 (Omega := Omega) mu) = L2Kernel.degreeL2 hW
  quadratic_le_principal :
    ∀ f : Lp Real 2 mu,
      inner Real f (operator f) <= eigen 0 * inner Real f f

/-- A Rayleigh-quotient upper bound implies the corresponding quadratic-form
bound.  This is the Hilbert-space bridge used to replace a raw scalar
principal bound by the standard operator-theoretic statement. -/
private theorem quadratic_le_principal_of_rayleigh_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E) {lambda : Real}
    (hray : ∀ f : E, f ≠ 0 -> T.rayleighQuotient f <= lambda) :
    ∀ f : E, inner Real f (T f) <= lambda * inner Real f f := by
  intro f
  by_cases hf : f = 0
  · simp [hf]
  · have hnormsq : 0 < ‖f‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr hf)
    have h := hray f hf
    have hmul : T.reApplyInnerSelf f <= lambda * ‖f‖ ^ 2 := by
      exact (div_le_iff₀ hnormsq).mp h
    have hre : T.reApplyInnerSelf f = inner Real f (T f) := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      simp [real_inner_comm]
    have hself : inner Real f f = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
    simpa [hre, hself] using hmul

/-- If a continuous linear operator is diagonalized by a countable Hilbert
basis, then its quadratic form is bounded above by the top listed eigenvalue.

This is the infinite-dimensional replacement for the finite eigenbasis sum:
the proof uses Hilbert-basis `HasSum` expansions and Parseval, not a
finite-spectrum assumption. -/
theorem quadratic_le_principal_of_hilbertBasis_diag
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (b : HilbertBasis Nat Real E)
    (eigen : Nat -> Real)
    (hdiag : ∀ n, T (b n) = eigen n • b n)
    (hle : ∀ n, eigen n <= eigen 0) :
    ∀ f : E, inner Real f (T f) <= eigen 0 * inner Real f f := by
  intro f
  have hdiagSum :
      HasSum (fun n : Nat => eigen n * ((b.repr f n : Real) ^ 2))
        (inner Real f (T f)) := by
    have hT := (b.hasSum_repr f).mapL T
    have hinner := hT.mapL ((innerSL Real) f)
    simpa [ContinuousLinearMap.map_smul, hdiag, HilbertBasis.repr_apply_apply,
      real_inner_comm, pow_two, mul_assoc, mul_comm, mul_left_comm] using hinner
  have hparseval :
      HasSum (fun n : Nat => ((b.repr f n : Real) ^ 2)) (inner Real f f) := by
    simpa [HilbertBasis.repr_apply_apply, real_inner_comm, pow_two] using
      (b.hasSum_inner_mul_inner f f)
  have htop :
      HasSum (fun n : Nat => eigen 0 * ((b.repr f n : Real) ^ 2))
        (eigen 0 * inner Real f f) :=
    hparseval.mul_left (eigen 0)
  exact hasSum_le
    (fun n => mul_le_mul_of_nonneg_right (hle n) (sq_nonneg _))
    hdiagSum htop

/-- Countable Hilbert-basis diagonalization gives the standard Rayleigh
quotient upper bound by the top listed eigenvalue. -/
theorem rayleigh_le_principal_of_hilbertBasis_diag
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (b : HilbertBasis Nat Real E)
    (eigen : Nat -> Real)
    (hdiag : ∀ n, T (b n) = eigen n • b n)
    (hle : ∀ n, eigen n <= eigen 0) :
    ∀ f : E, f ≠ 0 -> T.rayleighQuotient f <= eigen 0 := by
  have hquad :=
    quadratic_le_principal_of_hilbertBasis_diag T b eigen hdiag hle
  intro f hf
  have hnormsq : 0 < ‖f‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hf)
  rw [ContinuousLinearMap.rayleighQuotient]
  exact (div_le_iff₀ hnormsq).mpr (by
    have h := hquad f
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    simp [real_inner_comm] at h ⊢
    exact h)

/-- Orthogonality to every vector in a Hilbert basis of a closed subspace
implies orthogonality to the whole subspace.

This is the Hilbert-space bridge used when a compact spectral theorem chooses
orthonormal bases in each finite-dimensional nonzero eigenspace: checking
orthogonality on the chosen basis vectors is enough to check it on the whole
eigenspace. -/
theorem inner_eq_zero_of_forall_hilbertBasis_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {U : Submodule Real E} [CompleteSpace U]
    (b : HilbertBasis ι Real U) {x : E}
    (hbasis : ∀ i : ι, inner Real ((b i : U) : E) x = 0) :
    ∀ y : U, inner Real ((y : U) : E) x = 0 := by
  intro y
  let p : U := U.orthogonalProjectionOnto x
  have hbasis_proj : ∀ i : ι, inner Real (b i) p = 0 := by
    intro i
    simpa [p] using hbasis i
  have hseries :
      HasSum (fun _i : ι => (0 : Real)) (inner Real y p) := by
    refine (b.hasSum_inner_mul_inner y p).congr_fun ?_
    intro i
    simp [hbasis_proj i]
  have hinner_proj : inner Real y p = 0 := by
    have htsum := hseries.tsum_eq
    simpa using htsum.symm
  simpa [p] using hinner_proj

/-- Choosing a Hilbert basis in every member of a family of closed subspaces
does not change the orthogonal complement of their span.

The left hand side is the orthogonal complement of the algebraic span of all
chosen basis vectors.  The right hand side is the orthogonal complement of the
supremum of the original subspaces.  This is the density bridge needed for
assembling countably many finite-dimensional nonzero eigenspaces. -/
theorem orthogonal_span_sigma_hilbertBasis_eq_iSup_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {α : ι -> Type*}
    (U : ι -> Submodule Real E) [∀ i, CompleteSpace (U i)]
    (b : ∀ i, HilbertBasis (α i) Real (U i)) :
    (Submodule.span Real
      (Set.range fun a : Sigma α => ((b a.1 a.2 : U a.1) : E)))ᗮ =
      (⨆ i, U i)ᗮ := by
  let M : Submodule Real E :=
    Submodule.span Real
      (Set.range fun a : Sigma α => ((b a.1 a.2 : U a.1) : E))
  let S : Submodule Real E := ⨆ i, U i
  have hMS : M ≤ S := by
    change
      Submodule.span Real
        (Set.range fun a : Sigma α => ((b a.1 a.2 : U a.1) : E)) ≤
        ⨆ i, U i
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (le_iSup U a.1) (b a.1 a.2).property
  apply le_antisymm
  · intro x hxM
    rw [Submodule.mem_orthogonal] at hxM ⊢
    intro y hy
    refine Submodule.iSup_induction' U
      (motive := fun y _hy => inner Real y x = 0) ?mem ?zero ?add hy
    · intro i y hyi
      exact
        inner_eq_zero_of_forall_hilbertBasis_inner_eq_zero
          (b i) (x := x) (by
            intro a
            exact hxM ((b i a : U i) : E)
              (Submodule.subset_span ⟨⟨i, a⟩, rfl⟩)) ⟨y, hyi⟩
    · simp
    · intro u v _hu _hv hu hv
      simp [inner_add_left, hu, hv]
  · exact Submodule.orthogonal_le hMS

/-- If the ambient span of vectors in a closed subspace is dense inside that
subspace, then the same vectors have dense span when viewed as vectors of the
subspace itself.

This removes a recurring coercion issue in the compact spectral construction:
Mathlib's compact spectral theorem naturally gives ambient eigenspaces, while
the C9 package wants a dense family inside `(eigenspace T 0)ᗮ`. -/
theorem submodule_span_orthogonal_eq_bot_of_ambient_orthogonal_inf_eq_bot
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {U : Submodule Real E} (v : ι -> U)
    (h :
      ((Submodule.span Real (Set.range fun i : ι => ((v i : U) : E)))ᗮ ⊓ U) =
        ⊥) :
    (Submodule.span Real (Set.range v))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  let A : Submodule Real E :=
    Submodule.span Real (Set.range fun i : ι => ((v i : U) : E))
  have hxA : (x : E) ∈ Aᗮ := by
    change (x : E) ∈
      (Submodule.span Real (Set.range fun i : ι => ((v i : U) : E)))ᗮ
    rw [Submodule.mem_orthogonal]
    intro y hy
    refine Submodule.span_induction
      (s := Set.range fun i : ι => ((v i : U) : E))
      ?gen ?zero ?add ?smul hy
    · rintro z ⟨i, rfl⟩
      have hx' :=
        (Submodule.mem_orthogonal (Submodule.span Real (Set.range v)) x).1
          hx (v i) (Submodule.subset_span ⟨i, rfl⟩)
      simpa using hx'
    · simp
    · intro y z hy hz hiy hiz
      simp [inner_add_left, hiy, hiz]
    · intro a y hy hiy
      simp [inner_smul_left, hiy]
  have hxinf : (x : E) ∈ Aᗮ ⊓ U := ⟨hxA, x.property⟩
  have hxbot : (x : E) ∈ (⊥ : Submodule Real E) := by
    simpa [A, h] using hxinf
  ext
  simpa using hxbot

/-- Choose a Hilbert basis in every nonzero eigenspace of a compact
self-adjoint operator.  Viewed inside the orthogonal complement of the zero
eigenspace, the resulting sigma-indexed family has dense span.

This is the Hilbert-space core of the infinite spectral enumeration step:
there may be infinitely many nonzero eigenvalues, and each finite-dimensional
eigenspace may contribute several basis vectors, but their combined span is
dense in `(eigenspace T 0)ᗮ`. -/
theorem compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_dense_in_zero_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E]
    (T : E →L[Real] E)
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    {α : {lambda : Real // lambda ≠ 0} -> Type*}
    (b : ∀ lambda : {lambda : Real // lambda ≠ 0},
      HilbertBasis (α lambda) Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1)) :
    (Submodule.span Real
      (Set.range fun a : Sigma α =>
        (⟨((b a.1 a.2 :
            Module.End.eigenspace (T : Module.End Real E) a.1.1) : E),
          by
            rw [Submodule.mem_orthogonal]
            intro y hy
            have horth :
                Module.End.eigenspace (T : Module.End Real E) a.1.1 ⟂
                  Module.End.eigenspace (T : Module.End Real E) 0 :=
              (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
                (T := (T : Module.End Real E)) hsymm).isOrtho a.1.2
            exact horth.symm.inner_eq hy (b a.1 a.2).property⟩ :
          (Module.End.eigenspace (T : Module.End Real E) 0)ᗮ)))ᗮ = ⊥ := by
  let Z : Submodule Real E :=
    (Module.End.eigenspace (T : Module.End Real E) 0)ᗮ
  let v : Sigma α -> Z := fun a =>
    ⟨((b a.1 a.2 :
        Module.End.eigenspace (T : Module.End Real E) a.1.1) : E),
      by
        rw [Submodule.mem_orthogonal]
        intro y hy
        have horth :
            Module.End.eigenspace (T : Module.End Real E) a.1.1 ⟂
              Module.End.eigenspace (T : Module.End Real E) 0 :=
          (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
            (T := (T : Module.End Real E)) hsymm).isOrtho a.1.2
        exact horth.symm.inner_eq hy (b a.1 a.2).property⟩
  change (Submodule.span Real (Set.range v))ᗮ = ⊥
  refine submodule_span_orthogonal_eq_bot_of_ambient_orthogonal_inf_eq_bot
    v ?_
  have hspan :
      (Submodule.span Real
        (Set.range fun a : Sigma α =>
          ((b a.1 a.2 :
            Module.End.eigenspace (T : Module.End Real E) a.1.1) : E)))ᗮ =
        (⨆ lambda : {lambda : Real // lambda ≠ 0},
          Module.End.eigenspace (T : Module.End Real E) lambda.1)ᗮ :=
    orthogonal_span_sigma_hilbertBasis_eq_iSup_orthogonal
      (fun lambda : {lambda : Real // lambda ≠ 0} =>
        Module.End.eigenspace (T : Module.End Real E) lambda.1)
      b
  have hdense :
      ((⨆ lambda : {lambda : Real // lambda ≠ 0},
          Module.End.eigenspace (T : Module.End Real E) lambda.1)ᗮ ⊓ Z) =
        ⊥ := by
    simpa [Z] using
      CompactSpectral.compactSelfAdjoint_nonzero_iSup_orthogonal_inf_zero_eigenspace_orthogonal_eq_bot
        (T := T) hcompact hsymm
  simpa [v, Z, hspan] using hdense

/-- The sigma-indexed family obtained by choosing a Hilbert basis in every
nonzero eigenspace of a symmetric operator is orthonormal in the ambient
Hilbert space. -/
theorem compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (hsymm : T.IsSymmetric)
    {α : {lambda : Real // lambda ≠ 0} -> Type*}
    (b : ∀ lambda : {lambda : Real // lambda ≠ 0},
      HilbertBasis (α lambda) Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1)) :
    Orthonormal Real
      (fun a : Sigma α =>
        ((b a.1 a.2 :
          Module.End.eigenspace (T : Module.End Real E) a.1.1) : E)) := by
  exact
    ((LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : Module.End Real E)) hsymm).comp
        Subtype.coe_injective).orthonormal_sigma_orthonormal
      (fun lambda => (b lambda).orthonormal)

/-- The natural index type obtained by taking, for every nonzero real
`lambda`, the finite index set `Fin (finrank eigenspace lambda)` is countable
for a compact self-adjoint operator.

The outer type of nonzero real numbers is uncountable, but all non-eigenvalue
fibers are empty, and compactness makes the genuine nonzero eigenvalues
countable. -/
theorem compactSelfAdjoint_countable_nonzero_eigenspace_finIndex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E]
    (T : E →L[Real] E)
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Countable
      (Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace (T : Module.End Real E) lambda.1))) := by
  let eigs : Set Real :=
    {lambda : Real |
      Module.End.HasEigenvalue (T : Module.End Real E) lambda ∧ lambda ≠ 0}
  have hcount_eigs : eigs.Countable := by
    simpa [eigs] using
      CompactSpectral.compactSelfAdjoint_countable_nonzero_eigenvalues
        (T := T) hcompact hsymm
  let F :
      (Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace (T : Module.End Real E) lambda.1))) ->
        eigs × Nat :=
    fun a =>
      (⟨a.1.1,
        by
          have hfinpos :
              0 < Module.finrank Real
                (Module.End.eigenspace (T : Module.End Real E) a.1.1) :=
            Nat.pos_of_ne_zero (by
              intro hzero
              have hlt := a.2.2
              omega)
          have hnebot :
              Module.End.eigenspace (T : Module.End Real E) a.1.1 ≠ ⊥ := by
            intro hbot
            have hfinzero :
                Module.finrank Real
                  (Module.End.eigenspace (T : Module.End Real E) a.1.1) = 0 := by
              rw [hbot, finrank_bot]
            omega
          exact ⟨Module.End.hasEigenvalue_iff.mpr hnebot, a.1.2⟩⟩,
        a.2.1)
  have hF_inj : Function.Injective F := by
    intro a b hab
    cases a with
    | mk lambda i =>
      cases b with
      | mk nu j =>
        simp [F] at hab
        rcases hab with ⟨hlambda, hidx⟩
        have hsub : lambda = nu := Subtype.ext hlambda
        cases hsub
        congr
        exact Fin.ext hidx
  haveI : Countable eigs := hcount_eigs.to_subtype
  exact hF_inj.countable

/-- A `Nat` padding of an encodable index type with a distinguished principal
index at `0`.

Index `0` is always `some principal`.  Index `n + 1` decodes `n`; if this
decodes the principal index again, we return `none`, so the principal mode is
not duplicated in the nonzero part of the padded sequence. -/
noncomputable def principalPaddedIndex
    {ι : Type*} [Encodable ι] [DecidableEq ι] (principal : ι) :
    Nat -> Option ι
  | 0 => some principal
  | n + 1 =>
      match Encodable.decode₂ ι n with
      | some i => if i = principal then none else some i
      | none => none

/-- Padded modes attached to `principalPaddedIndex`. -/
noncomputable def principalPaddedMode
    {ι E : Type*} [Zero E] [Encodable ι] [DecidableEq ι]
    (principal : ι) (mode : ι -> E) (n : Nat) : E :=
  match principalPaddedIndex principal n with
  | some i => mode i
  | none => 0

/-- Padded eigenvalues attached to `principalPaddedIndex`. -/
noncomputable def principalPaddedEigen
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    (principal : ι) (eigen : ι -> Real) (n : Nat) : Real :=
  match principalPaddedIndex principal n with
  | some i => eigen i
  | none => 0

@[simp]
theorem principalPaddedIndex_zero
    {ι : Type*} [Encodable ι] [DecidableEq ι] (principal : ι) :
    principalPaddedIndex principal 0 = some principal := rfl

@[simp]
theorem principalPaddedMode_zero
    {ι E : Type*} [Zero E] [Encodable ι] [DecidableEq ι]
    (principal : ι) (mode : ι -> E) :
    principalPaddedMode principal mode 0 = mode principal := rfl

@[simp]
theorem principalPaddedEigen_zero
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    (principal : ι) (eigen : ι -> Real) :
    principalPaddedEigen principal eigen 0 = eigen principal := rfl

theorem principalPaddedIndex_encode_succ_of_ne
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    {principal i : ι} (hi : i ≠ principal) :
    principalPaddedIndex principal (Encodable.encode i + 1) = some i := by
  simp [principalPaddedIndex, Encodable.decode₂_encode, hi]

theorem principalPaddedMode_encode_succ_of_ne
    {ι E : Type*} [Zero E] [Encodable ι] [DecidableEq ι]
    {principal i : ι} (mode : ι -> E) (hi : i ≠ principal) :
    principalPaddedMode principal mode (Encodable.encode i + 1) = mode i := by
  simp [principalPaddedMode, principalPaddedIndex_encode_succ_of_ne hi]

theorem principalPaddedEigen_encode_succ_of_ne
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    {principal i : ι} (eigen : ι -> Real) (hi : i ≠ principal) :
    principalPaddedEigen principal eigen (Encodable.encode i + 1) = eigen i := by
  simp [principalPaddedEigen, principalPaddedIndex_encode_succ_of_ne hi]

theorem principalPaddedIndex_succ_eq_some_iff
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    {principal i : ι} {n : Nat} :
    principalPaddedIndex principal (n + 1) = some i ↔
      i ≠ principal ∧ Encodable.decode₂ ι n = some i := by
  cases hdec : Encodable.decode₂ ι n with
  | none =>
      simp [principalPaddedIndex, hdec]
  | some j =>
      by_cases hj : j = principal
      · subst j
        simp [principalPaddedIndex, hdec]
        intro hi hpi
        exact hi hpi.symm
      · simp [principalPaddedIndex, hdec, hj, eq_comm]
        intro hij hpi
        exact hj (hij.symm.trans hpi.symm)

theorem principalPaddedIndex_eq_some_injective
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    {principal : ι} {n m : Nat} {i : ι}
    (hn : principalPaddedIndex principal n = some i)
    (hm : principalPaddedIndex principal m = some i) :
    n = m := by
  cases n with
  | zero =>
      simp [principalPaddedIndex] at hn
      subst i
      cases m with
      | zero => rfl
      | succ m =>
          simp [principalPaddedIndex] at hm
          split at hm <;> simp_all
  | succ n =>
      cases m with
      | zero =>
          simp [principalPaddedIndex] at hm
          subst i
          have hn' := principalPaddedIndex_succ_eq_some_iff.mp hn
          exact False.elim (hn'.1 rfl)
      | succ m =>
          have hn' := principalPaddedIndex_succ_eq_some_iff.mp hn
          have hm' := principalPaddedIndex_succ_eq_some_iff.mp hm
          have hni : Encodable.encode i = n :=
            Encodable.decode₂_eq_some.mp hn'.2
          have hmi : Encodable.encode i = m :=
            Encodable.decode₂_eq_some.mp hm'.2
          omega

theorem principalPaddedIndex_eq_some_inj
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    {principal : ι} {n : Nat} {i j : ι}
    (hi : principalPaddedIndex principal n = some i)
    (hj : principalPaddedIndex principal n = some j) :
    i = j := by
  exact Option.some.inj (hi.symm.trans hj)

theorem principalPaddedEigen_ne_zero_iff_index
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    {principal : ι} {eigen : ι -> Real}
    (hne : ∀ i, eigen i ≠ 0) (n : Nat) :
    principalPaddedEigen principal eigen n ≠ 0 ↔
      ∃ i, principalPaddedIndex principal n = some i := by
  cases hidx : principalPaddedIndex principal n with
  | none =>
      simp [principalPaddedEigen, hidx]
  | some i =>
      simp [principalPaddedEigen, hidx, hne i]

/-- The nonzero part of the principal-padded encoding of an orthonormal
family is still orthonormal. -/
theorem principalPaddedMode_nonzero_orthonormal
    {ι E : Type*} [Encodable ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    {principal : ι} {mode : ι -> E} {eigen : ι -> Real}
    (hne : ∀ i, eigen i ≠ 0)
    (horth : Orthonormal Real mode) :
    Orthonormal Real
      (fun n : {n : Nat // principalPaddedEigen principal eigen n ≠ 0} =>
        principalPaddedMode principal mode n.1) := by
  rw [orthonormal_iff_ite]
  intro a b
  obtain ⟨i, hi⟩ :=
    (principalPaddedEigen_ne_zero_iff_index (principal := principal)
      (eigen := eigen) hne a.1).mp a.property
  obtain ⟨j, hj⟩ :=
    (principalPaddedEigen_ne_zero_iff_index (principal := principal)
      (eigen := eigen) hne b.1).mp b.property
  have hmodea :
      principalPaddedMode principal mode a.1 = mode i := by
    simp [principalPaddedMode, hi]
  have hmodeb :
      principalPaddedMode principal mode b.1 = mode j := by
    simp [principalPaddedMode, hj]
  have horthij := orthonormal_iff_ite.mp horth i j
  by_cases hij : i = j
  · subst j
    have hab : a = b := by
      apply Subtype.ext
      exact principalPaddedIndex_eq_some_injective hi hj
    simpa [hmodea, hmodeb, hab] using horthij
  · have hab : a ≠ b := by
      intro hab
      have hval : a.1 = b.1 := congrArg Subtype.val hab
      have hi' :
          principalPaddedIndex principal b.1 = some i := by
        simpa [hval] using hi
      exact hij (principalPaddedIndex_eq_some_inj hi' hj)
    simpa [hmodea, hmodeb, hij, hab] using horthij

/-- If an encodable family has dense span, then its principal-padded nonzero
`Nat` family also has dense span. -/
theorem principalPaddedMode_dense
    {ι E : Type*} [Encodable ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    {principal : ι} {v : ι -> E} {eigen : ι -> Real}
    (hne : ∀ i, eigen i ≠ 0)
    (hdense : (Submodule.span Real (Set.range v))ᗮ = ⊥) :
    (Submodule.span Real
      (Set.range fun n : {n : Nat //
          principalPaddedEigen principal eigen n ≠ 0} =>
        principalPaddedMode principal v n.1))ᗮ = ⊥ := by
  let A : Submodule Real E := Submodule.span Real (Set.range v)
  let B : Submodule Real E :=
    Submodule.span Real
      (Set.range fun n : {n : Nat //
          principalPaddedEigen principal eigen n ≠ 0} =>
        principalPaddedMode principal v n.1)
  have hAB : A ≤ B := by
    change Submodule.span Real (Set.range v) ≤
      Submodule.span Real
        (Set.range fun n : {n : Nat //
            principalPaddedEigen principal eigen n ≠ 0} =>
          principalPaddedMode principal v n.1)
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = principal
    · subst i
      refine Submodule.subset_span ?_
      refine ⟨⟨0, ?_⟩, ?_⟩
      · simp [principalPaddedEigen, hne principal]
      · simp [principalPaddedMode]
    · refine Submodule.subset_span ?_
      refine ⟨⟨Encodable.encode i + 1, ?_⟩, ?_⟩
      · simp [principalPaddedEigen_encode_succ_of_ne (eigen := eigen) hi,
          hne i]
      · simp [principalPaddedMode_encode_succ_of_ne (mode := v) hi]
  rw [eq_bot_iff]
  intro x hx
  have hxA : x ∈ Aᗮ := Submodule.orthogonal_le hAB hx
  simpa [A, hdense] using hxA

/-- A countable compact-spectral expansion bounds the quadratic form by the
top eigenvalue.

Unlike `quadratic_le_principal_of_hilbertBasis_diag`, this theorem does not
ask for a countable Hilbert basis of the whole Hilbert space.  It only asks
for the countable nonzero-mode expansion of `T f` and the corresponding
Bessel bound for the listed modes.  This is the shape compatible with
compact self-adjoint operators on possibly nonseparable Hilbert spaces: the
orthogonal residual lives in the zero eigenspace and is controlled by the
separate hypothesis `0 <= eigen 0`. -/
theorem quadratic_le_principal_of_compact_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hquad_expansion :
      ∀ f : E, HasSum
        (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2))
        (inner Real f (T f)))
    (hcoord_summable :
      ∀ f : E, Summable fun n : Nat => inner Real f (mode n) ^ 2)
    (hcoord_le :
      ∀ f : E,
        (∑' n : Nat, inner Real f (mode n) ^ 2) <= inner Real f f)
    (hle : ∀ n, eigen n <= eigen 0)
    (h0 : 0 <= eigen 0) :
    ∀ f : E, inner Real f (T f) <= eigen 0 * inner Real f f := by
  intro f
  have hweighted_le_top :
      inner Real f (T f) <=
        ∑' n : Nat, eigen 0 * (inner Real f (mode n) ^ 2) := by
    have htopSummable :
        Summable fun n : Nat => eigen 0 * (inner Real f (mode n) ^ 2) :=
      Summable.mul_left (eigen 0) (hcoord_summable f)
    exact hasSum_le
      (fun n => mul_le_mul_of_nonneg_right (hle n) (sq_nonneg _))
      (hquad_expansion f) htopSummable.hasSum
  have htop_eq :
      (∑' n : Nat, eigen 0 * (inner Real f (mode n) ^ 2)) =
        eigen 0 * (∑' n : Nat, inner Real f (mode n) ^ 2) :=
    (hcoord_summable f).tsum_mul_left (eigen 0)
  have htop_le :
      eigen 0 * (∑' n : Nat, inner Real f (mode n) ^ 2) <=
        eigen 0 * inner Real f f :=
    mul_le_mul_of_nonneg_left (hcoord_le f) h0
  linarith

/-- A countable compact-spectral expansion gives the Rayleigh quotient bound
by the top eigenvalue, without assuming the entire Hilbert space has a
countable basis. -/
theorem rayleigh_le_principal_of_compact_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hquad_expansion :
      ∀ f : E, HasSum
        (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2))
        (inner Real f (T f)))
    (hcoord_summable :
      ∀ f : E, Summable fun n : Nat => inner Real f (mode n) ^ 2)
    (hcoord_le :
      ∀ f : E,
        (∑' n : Nat, inner Real f (mode n) ^ 2) <= inner Real f f)
    (hle : ∀ n, eigen n <= eigen 0)
    (h0 : 0 <= eigen 0) :
    ∀ f : E, f ≠ 0 -> T.rayleighQuotient f <= eigen 0 := by
  have hquad :=
    quadratic_le_principal_of_compact_eigen_expansion T mode eigen
      hquad_expansion hcoord_summable hcoord_le hle h0
  intro f hf
  have hnormsq : 0 < ‖f‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hf)
  rw [ContinuousLinearMap.rayleighQuotient]
  exact (div_le_iff₀ hnormsq).mpr (by
    have h := hquad f
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    simp [real_inner_comm] at h ⊢
    exact h)

/-- Real-coordinate square summability from Bessel's inequality for an
orthonormal family. -/
theorem summable_inner_sq_of_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {mode : ι -> E} (hmode : Orthonormal Real mode) (f : E) :
    Summable fun n : ι => inner Real f (mode n) ^ 2 := by
  simpa [real_inner_comm, Real.norm_eq_abs, sq_abs] using
    hmode.inner_products_summable f

/-- Bessel's inequality in the real coordinate form used by the compact C9
spectral interface. -/
theorem tsum_inner_sq_le_self_of_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {mode : ι -> E} (hmode : Orthonormal Real mode) (f : E) :
    (∑' n : ι, inner Real f (mode n) ^ 2) <= inner Real f f := by
  simpa [real_inner_comm, Real.norm_eq_abs, sq_abs, real_inner_self_eq_norm_sq] using
    hmode.tsum_inner_products_le f

/-- Finite Bessel inequality in the real coordinate form used by row-wise
Hilbert-Schmidt energy estimates. -/
theorem sum_inner_sq_le_self_of_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {mode : ι -> E} (hmode : Orthonormal Real mode) (f : E)
    (s : Finset ι) :
    s.sum (fun n : ι => inner Real f (mode n) ^ 2) <= inner Real f f := by
  have hsumm : Summable fun n : ι => inner Real f (mode n) ^ 2 :=
    summable_inner_sq_of_orthonormal hmode f
  have hsum_le :
      s.sum (fun n : ι => inner Real f (mode n) ^ 2) <=
        ∑' n : ι, inner Real f (mode n) ^ 2 := by
    exact hsumm.sum_le_tsum s (fun n _hn => sq_nonneg _)
  exact hsum_le.trans (tsum_inner_sq_le_self_of_orthonormal hmode f)

/-- Initial-segment form of finite Bessel inequality. -/
theorem sum_range_inner_sq_le_self_of_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {mode : Nat -> E} (hmode : Orthonormal Real mode) (f : E)
    (N : Nat) :
    (Finset.range N).sum (fun n : Nat => inner Real f (mode n) ^ 2) <=
      inner Real f f :=
  sum_inner_sq_le_self_of_orthonormal hmode f (Finset.range N)

/-- Finite Bessel inequality for a zero-padded eigenmode list.

Only indices with nonzero listed eigenvalue are used, and those modes are
orthonormal after reindexing by the nonzero subtype. -/
theorem sum_filter_ne_zero_inner_sq_le_self_of_padded_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {mode : Nat -> E} {eigen : Nat -> Real}
    (hmode :
      Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1))
    (f : E) (s : Finset Nat) :
    (s.filter (fun n : Nat => eigen n ≠ 0)).sum
        (fun n : Nat => inner Real f (mode n) ^ 2) <=
      inner Real f f := by
  classical
  let emb :
      {n : Nat // n ∈ s.filter (fun n : Nat => eigen n ≠ 0)} ↪
        {n : Nat // eigen n ≠ 0} := {
    toFun := fun n => ⟨n.1, (Finset.mem_filter.mp n.2).2⟩
    inj' := by
      intro a b h
      have hval :
          ((fun n : {n : Nat // eigen n ≠ 0} => n.1)
            ((fun n : {n : Nat // n ∈ s.filter (fun n : Nat => eigen n ≠ 0)} =>
              (⟨n.1, (Finset.mem_filter.mp n.2).2⟩ :
                {n : Nat // eigen n ≠ 0})) a)) =
            ((fun n : {n : Nat // eigen n ≠ 0} => n.1)
              ((fun n : {n : Nat // n ∈ s.filter (fun n : Nat => eigen n ≠ 0)} =>
                (⟨n.1, (Finset.mem_filter.mp n.2).2⟩ :
                  {n : Nat // eigen n ≠ 0})) b)) :=
        congrArg (fun n : {n : Nat // eigen n ≠ 0} => n.1) h
      exact Subtype.ext hval }
  let t : Finset {n : Nat // eigen n ≠ 0} :=
    (s.filter (fun n : Nat => eigen n ≠ 0)).attach.map emb
  have hsum :
      (s.filter (fun n : Nat => eigen n ≠ 0)).sum
          (fun n : Nat => inner Real f (mode n) ^ 2) =
        t.sum (fun n : {n : Nat // eigen n ≠ 0} =>
          inner Real f (mode n.1) ^ 2) := by
    simp [t, emb, Finset.sum_map]
    exact
      (Finset.sum_attach
        (s.filter (fun n : Nat => eigen n ≠ 0))
        (fun n : Nat => inner Real f (mode n) ^ 2)).symm
  rw [hsum]
  exact sum_inner_sq_le_self_of_orthonormal hmode f t

/-- A zero-padded countable compact-spectral expansion bounds the quadratic
form by the top eigenvalue.

This is the finite-rank-safe variant of
`quadratic_le_principal_of_compact_eigen_expansion`: the listed zero
eigenvalues may be padded arbitrarily, so we do not ask for summability of all
coordinate squares over `Nat`.  Instead the proof bounds each finite partial
sum after filtering to the nonzero eigenvalues and then passes to the
`HasSum` limit. -/
theorem quadratic_le_principal_of_padded_compact_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode :
      Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1))
    (hquad_expansion :
      ∀ f : E, HasSum
        (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2))
        (inner Real f (T f)))
    (hle : ∀ n, eigen n <= eigen 0)
    (h0 : 0 <= eigen 0) :
    ∀ f : E, inner Real f (T f) <= eigen 0 * inner Real f f := by
  intro f
  have hpartial :
      ∀ N : Nat,
        (Finset.range N).sum
            (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2)) <=
          eigen 0 * inner Real f f := by
    intro N
    classical
    let s : Finset Nat := (Finset.range N).filter (fun n : Nat => eigen n ≠ 0)
    have hfilter :
        (Finset.range N).sum
            (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2)) =
          s.sum (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2)) := by
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro n _hn
      by_cases hn : eigen n = 0
      · simp [hn]
      · simp [hn]
    have hterm_le :
        s.sum (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2)) <=
          s.sum (fun n : Nat => eigen 0 * (inner Real f (mode n) ^ 2)) := by
      refine Finset.sum_le_sum ?_
      intro n _hn
      exact mul_le_mul_of_nonneg_right (hle n) (sq_nonneg _)
    have hbessel :
        s.sum (fun n : Nat => inner Real f (mode n) ^ 2) <=
          inner Real f f := by
      simpa [s] using
        sum_filter_ne_zero_inner_sq_le_self_of_padded_orthonormal
          (mode := mode) (eigen := eigen) hmode f (Finset.range N)
    have htop_le :
        s.sum (fun n : Nat => eigen 0 * (inner Real f (mode n) ^ 2)) <=
          eigen 0 * inner Real f f := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hbessel h0
    exact hfilter.trans_le (hterm_le.trans htop_le)
  exact le_of_tendsto (hquad_expansion f).tendsto_sum_nat
    (by filter_upwards with N; exact hpartial N)

/-- Row-wise Hilbert-Schmidt energy bridge.

This is the abstract integral step behind the graphon square-energy estimate:
if finite operator energies are represented by integrating squared row
coordinates, then Bessel's inequality bounds them by the integrated row norm. -/
theorem finite_energy_bound_of_row_energy_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {row : Omega -> E}
    {mode : Nat -> E}
    (hmode : Orthonormal Real mode)
    {T : E -> E}
    {B : Real}
    (hrowFiniteIntegrable :
      ∀ N : Nat,
        Integrable
          (fun x : Omega =>
            (Finset.range N).sum
              (fun n : Nat => inner Real (row x) (mode n) ^ 2)) mu)
    (hrowNormIntegrable :
      Integrable (fun x : Omega => inner Real (row x) (row x)) mu)
    (hrowEnergy :
      ∀ N : Nat,
        (Finset.range N).sum (fun n : Nat => ‖T (mode n)‖ ^ 2) =
          ∫ x, (Finset.range N).sum
            (fun n : Nat => inner Real (row x) (mode n) ^ 2) ∂mu)
    (hrowNormBound :
      (∫ x, inner Real (row x) (row x) ∂mu) <= B) :
    ∀ N : Nat,
      (Finset.range N).sum (fun n : Nat => ‖T (mode n)‖ ^ 2) <= B := by
  intro N
  have hpoint :
      ∀ x : Omega,
        (Finset.range N).sum
            (fun n : Nat => inner Real (row x) (mode n) ^ 2) <=
          inner Real (row x) (row x) := by
    intro x
    exact sum_range_inner_sq_le_self_of_orthonormal hmode (row x) N
  have hint_le :
      (∫ x, (Finset.range N).sum
          (fun n : Nat => inner Real (row x) (mode n) ^ 2) ∂mu) <=
        ∫ x, inner Real (row x) (row x) ∂mu := by
    exact integral_mono (hrowFiniteIntegrable N) hrowNormIntegrable hpoint
  calc
    (Finset.range N).sum (fun n : Nat => ‖T (mode n)‖ ^ 2)
        = ∫ x, (Finset.range N).sum
            (fun n : Nat => inner Real (row x) (mode n) ^ 2) ∂mu := hrowEnergy N
    _ <= ∫ x, inner Real (row x) (row x) ∂mu := hint_le
    _ <= B := hrowNormBound

/-- A complete orthonormal eigenmode expansion gives the vector-valued
spectral action expansion.

This is the Hilbert-space step that turns a structural spectral theorem
(`f = sum <f,e_n> e_n` and `T e_n = lambda_n e_n`) into the action-expansion
field used by the C9 low-band package. -/
theorem action_expansion_of_complete_eigenmode_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hdiag : ∀ n, T (mode n) = eigen n • mode n)
    (hcomplete :
      ∀ f : E, HasSum (fun n : Nat => inner Real f (mode n) • mode n) f) :
    ∀ f : E, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      (T f) := by
  intro f
  have hmap := (hcomplete f).mapL T
  convert hmap using 1
  ext n
  simp [hdiag n, smul_smul, mul_comm]

/-- A nonzero-eigenspace expansion of the range of a symmetric operator gives
the padded action expansion used by the graphon C9 package.

This is the form needed for compact operators: the zero eigenspace need not be
listed, and finite spectra can be padded by arbitrary zero-eigenvalue entries.
The only expansion hypothesis is for `T f`, over the nonzero listed modes. -/
theorem padded_action_expansion_of_nonzero_eigenmode_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hsymm : (T : E →ₗ[Real] E).IsSymmetric)
    (hdiag : ∀ n, eigen n ≠ 0 -> T (mode n) = eigen n • mode n)
    (hnonzero :
      ∀ f : E, HasSum
        (fun n : {n : Nat // eigen n ≠ 0} =>
          inner Real (T f) (mode n.1) • mode n.1)
        (T f)) :
    ∀ f : E, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      (T f) := by
  intro f
  let s : Set Nat := {n | eigen n ≠ 0}
  let nonzeroTerm : Nat -> E :=
    fun n => inner Real (T f) (mode n) • mode n
  have hsub :
      HasSum (nonzeroTerm ∘ (Subtype.val : s -> Nat)) (T f) := by
    simpa [s, nonzeroTerm, Function.comp_def] using hnonzero f
  have hindicator : HasSum (s.indicator nonzeroTerm) (T f) :=
    hasSum_subtype_iff_indicator.mp hsub
  refine hindicator.congr_fun ?_
  intro n
  by_cases hn : eigen n ≠ 0
  · have hinner :
        inner Real (T f) (mode n) = eigen n * inner Real f (mode n) := by
      calc
        inner Real (T f) (mode n) = inner Real f (T (mode n)) := hsymm f (mode n)
        _ = eigen n * inner Real f (mode n) := by
          rw [hdiag n hn]
          simp [inner_smul_right]
    simp [s, nonzeroTerm, hn, hinner]
  · have hzero : eigen n = 0 := not_not.mp hn
    simp [s, nonzeroTerm, hzero]

/-- A Hilbert basis of a closed nonzero spectral subspace gives the padded
action expansion, provided the range of the operator lies in that subspace.

This is the compact-spectral target in a Hilbert-space-native form: the future
compact theorem should construct `U` as the closed span/direct Hilbert sum of
the nonzero eigenspaces and prove `T f ∈ U`. -/
theorem padded_action_expansion_of_nonzero_hilbertBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (U : Submodule Real E) [CompleteSpace U]
    (b : HilbertBasis {n : Nat // eigen n ≠ 0} Real U)
    (hsymm : (T : E →ₗ[Real] E).IsSymmetric)
    (hdiag : ∀ n, eigen n ≠ 0 -> T (mode n) = eigen n • mode n)
    (hbmode : ∀ n : {n : Nat // eigen n ≠ 0}, ((b n : U) : E) = mode n.1)
    (hrange : ∀ f : E, T f ∈ U) :
    ∀ f : E, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      (T f) := by
  refine padded_action_expansion_of_nonzero_eigenmode_expansion
    T mode eigen hsymm hdiag ?_
  intro f
  have hprojE :=
    (b.hasSum_orthogonalProjectionOnto (T f)).mapL U.subtypeL
  have hprojSelf :
      ((U.orthogonalProjectionOnto (T f) : U) : E) = T f := by
    let v : U := ⟨T f, hrange f⟩
    have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (K := U) v
    simpa [v] using congrArg (fun x : U => (x : E)) h
  have hprojE' :
      HasSum
        (fun n : {n : Nat // eigen n ≠ 0} =>
          inner Real (T f) (mode n.1) • mode n.1)
        ((U.orthogonalProjectionOnto (T f) : U) : E) := by
    refine hprojE.congr_fun ?_
    intro n
    simp [hbmode n, real_inner_comm]
  simpa [hprojSelf] using hprojE'

/-- Finite iterates of a continuous linear operator.  This is kept abstract
from `L2Kernel.clmIter` so the Hilbert-space spectral algebra below can be
used before specializing to graphon `L²` operators. -/
noncomputable def opIter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (T : E →L[Real] E) : Nat -> E -> E
  | 0, f => f
  | n + 1, f => T (opIter T n f)

/-- On graphon `L²`, the abstract iterator agrees with the concrete iterator
used in `L2Kernel`. -/
theorem opIter_eq_l2_clmIter
    (T : Lp Real 2 mu →L[Real] Lp Real 2 mu) :
    ∀ n f, opIter T n f = L2Kernel.clmIter (mu := mu) T n f := by
  intro n
  induction n with
  | zero =>
      intro f
      rfl
  | succ n ih =>
      intro f
      change T (opIter T n f) =
        T (L2Kernel.clmIter (mu := mu) T n f)
      rw [ih f]

/-- In an orthonormal eigenmode action expansion, diagonal action is not an
extra assumption: evaluate the expansion at one of the modes. -/
theorem diagonal_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ k, T (mode k) = eigen k • mode k := by
  intro k
  let term : Nat -> E :=
    fun n => (eigen n * inner Real (mode k) (mode n)) • mode n
  have hterm : HasSum term (T (mode k)) := haction (mode k)
  have hsingle :
      HasSum (fun n : Nat => if n = k then eigen k • mode k else 0)
        (eigen k • mode k) := by
    simpa using hasSum_ite_eq k (eigen k • mode k)
  have hcongr :
      ∀ n, term n = (if n = k then eigen k • mode k else 0) := by
    intro n
    by_cases hn : n = k
    · subst n
      have hnorm : ‖mode k‖ ^ 2 = 1 := by
        simp [hmode.norm_eq_one k]
      simp [term, hnorm]
    · have hkn : k ≠ n := fun h => hn h.symm
      have hinner : inner Real (mode k) (mode n) = 0 := by
        simpa [hkn] using (orthonormal_iff_ite.mp hmode k n)
      simp [term, hinner, hn]
  have hsingle' : HasSum term (eigen k • mode k) :=
    hsingle.congr_fun hcongr
  exact hterm.tsum_eq.symm.trans hsingle'.tsum_eq

/-- In a padded action expansion, every listed nonzero mode is genuinely
diagonal.  Zero-eigenvalue indices may be padding and are not required to be
orthonormal or diagonal. -/
theorem diagonal_of_padded_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode :
      Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1))
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ k, eigen k ≠ 0 -> T (mode k) = eigen k • mode k := by
  intro k hk
  let term : Nat -> E :=
    fun n => (eigen n * inner Real (mode k) (mode n)) • mode n
  have hterm : HasSum term (T (mode k)) := haction (mode k)
  have hsingle :
      HasSum (fun n : Nat => if n = k then eigen k • mode k else 0)
        (eigen k • mode k) := by
    simpa using hasSum_ite_eq k (eigen k • mode k)
  have hcongr :
      ∀ n, term n = (if n = k then eigen k • mode k else 0) := by
    intro n
    by_cases hnzero : eigen n = 0
    · have hnk : n ≠ k := by
        intro hnk
        exact hk (by simpa [hnk] using hnzero)
      simp [term, hnzero, hnk]
    · have hnzero' : eigen n ≠ 0 := hnzero
      let kn : {n : Nat // eigen n ≠ 0} := ⟨k, hk⟩
      let nn : {n : Nat // eigen n ≠ 0} := ⟨n, hnzero'⟩
      by_cases hnk : n = k
      · subst n
        have hnorm1 : ‖mode k‖ = 1 := by
          simpa [kn] using hmode.norm_eq_one kn
        have hnorm : ‖mode k‖ ^ 2 = 1 := by
          simp [hnorm1]
        simp [term, hnorm]
      · have hkn : kn ≠ nn := by
          intro h
          exact hnk (Subtype.ext_iff.mp h).symm
        have hinner : inner Real (mode k) (mode n) = 0 := by
          simpa [kn, nn, hkn] using (orthonormal_iff_ite.mp hmode kn nn)
        simp [term, hinner, hnk]
  have hsingle' : HasSum term (eigen k • mode k) :=
    hsingle.congr_fun hcongr
  exact hterm.tsum_eq.symm.trans hsingle'.tsum_eq

/-- A vector-valued eigenmode action expansion propagates through all positive
operator iterates.

This is the infinite-series analogue of the matrix identity
`T^m f = ∑ λ_n^m ⟪f,e_n⟫ e_n`; no finite-spectrum assumption is used. -/
theorem action_expansion_iter_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ k f, HasSum
      (fun n : Nat => (eigen n ^ (k + 1) * inner Real f (mode n)) • mode n)
      (opIter T (k + 1) f) := by
  have hdiag :
      ∀ n, T (mode n) = eigen n • mode n :=
    diagonal_of_action_eigen_expansion T mode eigen hmode haction
  intro k
  induction k with
  | zero =>
      intro f
      simpa [opIter] using haction f
  | succ k ih =>
      intro f
      have hmap := (ih f).mapL T
      simpa [opIter, hdiag, smul_smul, pow_succ, mul_assoc, mul_comm,
        mul_left_comm] using hmap

/-- Quadratic-form version of the positive-iterate action expansion.

For graphon trace identities this is the series that appears after pairing a
kernel row with `T^m` applied to the same row. -/
theorem quadratic_expansion_iter_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ k f, HasSum
      (fun n : Nat => eigen n ^ (k + 1) * (inner Real f (mode n) ^ 2))
      (inner Real f (opIter T (k + 1) f)) := by
  intro k f
  have hvec :=
    action_expansion_iter_of_action_eigen_expansion
      T mode eigen hmode haction k f
  have hinner := hvec.mapL ((innerSL Real) f)
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hinner

/-- A zero-padded vector-valued action expansion propagates through all
positive operator iterates.

For indices with zero listed eigenvalue, the coefficient in every positive
iterate is already zero; for nonzero indices the diagonal action is recovered
from the padded action expansion. -/
theorem action_expansion_iter_of_padded_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode :
      Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1))
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ k f, HasSum
      (fun n : Nat => (eigen n ^ (k + 1) * inner Real f (mode n)) • mode n)
      (opIter T (k + 1) f) := by
  intro k
  induction k with
  | zero =>
      intro f
      simpa [opIter] using haction f
  | succ k ih =>
      intro f
      have hmap := (ih f).mapL T
      have hterm :
          ∀ n : Nat,
            T ((eigen n ^ (k + 1) * inner Real f (mode n)) • mode n) =
              (eigen n ^ (Nat.succ k + 1) * inner Real f (mode n)) •
                mode n := by
        intro n
        by_cases hn : eigen n = 0
        · have hpow_left : eigen n ^ (k + 1) = 0 := by
            simp [hn]
          have hpow_right : eigen n ^ (Nat.succ k + 1) = 0 := by
            simp [hn]
          simp [hpow_left, hpow_right]
        · have hdiag :
              T (mode n) = eigen n • mode n :=
            diagonal_of_padded_action_eigen_expansion
              T mode eigen hmode haction n hn
          simp [hdiag, smul_smul, pow_succ, mul_assoc, mul_comm]
      have hmap' := hmap.congr_fun (fun n => (hterm n).symm)
      simpa [opIter] using hmap'

/-- Quadratic-form version of the padded positive-iterate action expansion. -/
theorem quadratic_expansion_iter_of_padded_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode :
      Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1))
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ k f, HasSum
      (fun n : Nat => eigen n ^ (k + 1) * (inner Real f (mode n) ^ 2))
      (inner Real f (opIter T (k + 1) f)) := by
  intro k f
  have hvec :=
    action_expansion_iter_of_padded_action_eigen_expansion
      T mode eigen hmode haction k f
  have hinner := hvec.mapL ((innerSL Real) f)
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hinner

/-- In an orthonormal action expansion, each listed mode coordinate of `T f`
is multiplication by the corresponding listed eigenvalue. -/
theorem inner_mode_action_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ f k, inner Real (mode k) (T f) = eigen k * inner Real f (mode k) := by
  intro f k
  let term : Nat -> Real := fun n =>
    inner Real (mode k)
      ((eigen n * inner Real f (mode n)) • mode n)
  have hterm : HasSum term (inner Real (mode k) (T f)) :=
    (haction f).mapL ((innerSL Real) (mode k))
  have hsingle :
      HasSum (fun n : Nat =>
        if n = k then eigen k * inner Real f (mode k) else 0)
        (eigen k * inner Real f (mode k)) := by
    simpa using hasSum_ite_eq k (eigen k * inner Real f (mode k))
  have hcongr :
      ∀ n, term n =
        (if n = k then eigen k * inner Real f (mode k) else 0) := by
    intro n
    by_cases hn : n = k
    · subst n
      have hnorm : ‖mode k‖ ^ 2 = 1 := by
        simp [hmode.norm_eq_one k]
      rw [if_pos rfl]
      dsimp [term]
      change
        inner Real (mode k)
          ((eigen k * inner Real f (mode k)) • mode k) =
        eigen k * inner Real f (mode k)
      rw [inner_smul_right, real_inner_self_eq_norm_sq, hnorm, mul_one]
    · have hkn : k ≠ n := fun h => hn h.symm
      have hinner : inner Real (mode k) (mode n) = 0 := by
        simpa [hkn] using (orthonormal_iff_ite.mp hmode k n)
      rw [if_neg hn]
      dsimp [term]
      change
        inner Real (mode k)
          ((eigen n * inner Real f (mode n)) • mode n) = 0
      rw [inner_smul_right, hinner, mul_zero]
  have hsingle' : HasSum term (eigen k * inner Real f (mode k)) :=
    hsingle.congr_fun hcongr
  exact hterm.tsum_eq.symm.trans hsingle'.tsum_eq

/-- A vector-valued orthonormal action expansion covers every nonzero
eigenvalue of the represented operator.

This is the key reason the compact-action interface does not need a separate
finite-spectrum assumption: if `T f` is represented by the listed modes for
every `f`, then any nonzero eigenvector has a nonzero coordinate in one of
those modes, forcing its eigenvalue to be one of the listed coefficients. -/
theorem mem_range_eigen_of_hasEigenvalue_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f))
    {lambda : Real}
    (hlambda : Module.End.HasEigenvalue T.toLinearMap lambda)
    (hlambda0 : lambda ≠ 0) :
    lambda ∈ Set.range eigen := by
  by_contra hnot
  obtain ⟨v, hv⟩ := hlambda.exists_hasEigenvector
  have hv_apply : T v = lambda • v := by
    simpa using hv.apply_eq_smul
  have hcoeff_zero : ∀ k, inner Real v (mode k) = 0 := by
    intro k
    have hcoord :=
      inner_mode_action_of_action_eigen_expansion
        T mode eigen hmode haction v k
    have hcoord_eig :
        inner Real (mode k) (T v) = lambda * inner Real v (mode k) := by
      rw [hv_apply, inner_smul_right, real_inner_comm (mode k) v]
    have heq :
        lambda * inner Real v (mode k) =
          eigen k * inner Real v (mode k) := by
      linarith
    have hmul :
        (lambda - eigen k) * inner Real v (mode k) = 0 := by
      nlinarith [heq]
    have hne_eigen : lambda ≠ eigen k := by
      intro h
      exact hnot ⟨k, h.symm⟩
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne_eigen)
  let term : Nat -> E :=
    fun n => (eigen n * inner Real v (mode n)) • mode n
  have hsum : HasSum term (T v) := haction v
  have hzero_terms : ∀ n, term n = 0 := by
    intro n
    dsimp [term]
    rw [hcoeff_zero n, mul_zero, zero_smul]
  have hzero_sum : HasSum term 0 := hasSum_zero.congr_fun hzero_terms
  have hTv_zero : T v = 0 := hsum.tsum_eq.symm.trans hzero_sum.tsum_eq
  have hv_zero : v = 0 := by
    have hsmul_zero : lambda • v = 0 := by
      rw [← hv_apply, hTv_zero]
    rcases smul_eq_zero.mp hsmul_zero with hlambda_zero | hv_zero
    · exact False.elim (hlambda0 hlambda_zero)
    · exact hv_zero
  exact hv.2 hv_zero

/-- An orthonormal diagonal mode is a genuine eigenvector, hence its listed
scalar is a genuine eigenvalue.

This is a small but important grounding lemma for the compact-action spectral
interfaces: listed spectral values are not merely formal series coefficients. -/
theorem hasEigenvalue_of_orthonormal_diagonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (hdiag : ∀ n, T (mode n) = eigen n • mode n) :
    ∀ n, Module.End.HasEigenvalue T.toLinearMap (eigen n) := by
  intro n
  have hmode_ne : mode n ≠ 0 := by
    intro hzero
    have hnorm_zero : ‖mode n‖ = 0 := by simp [hzero]
    have hnorm_one : ‖mode n‖ = 1 := hmode.norm_eq_one n
    linarith
  have hmem :
      mode n ∈ Module.End.eigenspace T.toLinearMap (eigen n) := by
    simpa [Module.End.mem_eigenspace_iff] using hdiag n
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, hmode_ne⟩

/-- An `L2` vector has a bounded strongly measurable pointwise representative. -/
def HasGoodRepresentative [IsProbabilityMeasure mu] (v : Lp Real 2 mu) : Prop :=
  ∃ (f : Omega -> Real), ∃ hf : Good f, v = L2Kernel.goodL2 (mu := mu) hf

/-- Scalar multiples of good representatives still have good representatives. -/
theorem hasGoodRepresentative_of_eq_smul_goodL2
    [IsProbabilityMeasure mu]
    {v : Lp Real 2 mu} {c : Real} {f : Omega -> Real} (hf : Good f)
    (hv : v = c • L2Kernel.goodL2 (mu := mu) hf) :
    HasGoodRepresentative (mu := mu) v := by
  refine ⟨c • f, good_smul c hf, ?_⟩
  rw [hv, L2Kernel.goodL2_smul]

/-- A nonzero eigenmode has a good representative as soon as its operator
image has one.

This is the representative-level replacement for any finite-rank shortcut:
from `T v = lambda • v` and `lambda ≠ 0`, divide by `lambda` in `L2`. -/
theorem hasGoodRepresentative_of_nonzero_eigenmode_and_good_operator_image
    [IsProbabilityMeasure mu]
    {T : Lp Real 2 mu →L[Real] Lp Real 2 mu}
    {mode : Lp Real 2 mu} {lambda : Real}
    {g : Omega -> Real} (hg : Good g)
    (himage : T mode = L2Kernel.goodL2 (mu := mu) hg)
    (hdiag : T mode = lambda • mode)
    (hlambda : lambda ≠ 0) :
    HasGoodRepresentative (mu := mu) mode := by
  refine hasGoodRepresentative_of_eq_smul_goodL2
    (mu := mu) (c := lambda⁻¹) hg ?_
  calc
    mode = (lambda⁻¹ * lambda) • mode := by
      rw [inv_mul_cancel₀ hlambda, one_smul]
    _ = lambda⁻¹ • (lambda • mode) := by
      rw [smul_smul]
    _ = lambda⁻¹ • L2Kernel.goodL2 (mu := mu) hg := by
      rw [← hdiag, himage]

/-- The concrete pointwise `L²` graphon transform has a good representative. -/
theorem hasGoodRepresentative_kernelOpL2OfL2
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (f : Lp Real 2 mu) :
    HasGoodRepresentative (mu := mu)
      (L2Kernel.kernelOpL2OfL2 (mu := mu) hW f) := by
  refine ⟨kernelOp W mu (fun y : Omega => f y),
    L2Kernel.good_kernelOp_l2 (mu := mu) hW f, ?_⟩
  rfl

/-- Eigenvalues appearing in an orthonormal action expansion are bounded by
the operator norm. -/
theorem abs_eigen_le_norm_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ n, |eigen n| <= ‖T‖ := by
  intro n
  have hdiag :=
    diagonal_of_action_eigen_expansion T mode eigen hmode haction n
  have hnorm_mode : ‖mode n‖ = 1 := hmode.norm_eq_one n
  calc
    |eigen n| = ‖eigen n • mode n‖ := by
          rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs]
    _ = ‖T (mode n)‖ := by rw [hdiag]
    _ <= ‖T‖ * ‖mode n‖ := ContinuousLinearMap.le_opNorm T (mode n)
    _ = ‖T‖ := by rw [hnorm_mode, mul_one]

/-- For an orthonormal action expansion, finite initial eigenvalue-square
sums are exactly the finite energy of the listed eigenmodes.

This is the abstract Hilbert-space bridge behind the graphon square bound:
once a separate Hilbert-Schmidt/kernel-energy theorem bounds
`∑ ‖T (mode n)‖²` on every finite initial segment, the same bound applies to
`∑ eigen n²`. -/
theorem sum_range_eigen_sq_eq_sum_range_norm_apply_sq_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ N : Nat,
      (Finset.range N).sum (fun n => eigen n ^ 2) =
        (Finset.range N).sum (fun n => ‖T (mode n)‖ ^ 2) := by
  intro N
  refine Finset.sum_congr rfl ?_
  intro n _hn
  have hdiag :=
    diagonal_of_action_eigen_expansion T mode eigen hmode haction n
  have hnorm_mode : ‖mode n‖ = 1 := hmode.norm_eq_one n
  calc
    eigen n ^ 2 = |eigen n| ^ 2 := by rw [sq_abs]
    _ = ‖eigen n • mode n‖ ^ 2 := by
          rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs]
    _ = ‖T (mode n)‖ ^ 2 := by rw [hdiag]

/-- A finite-energy bound on the listed modes gives the finite square-bound
bound for the eigenvalue sequence in an orthonormal action expansion. -/
theorem sum_range_eigen_sq_le_of_action_eigen_expansion_and_energy_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f))
    {B : Real}
    (henergy :
      ∀ N : Nat, (Finset.range N).sum (fun n => ‖T (mode n)‖ ^ 2) <= B) :
    ∀ N : Nat, (Finset.range N).sum (fun n => eigen n ^ 2) <= B := by
  intro N
  rw [sum_range_eigen_sq_eq_sum_range_norm_apply_sq_of_action_eigen_expansion
    T mode eigen hmode haction N]
  exact henergy N

/-- Eigenvalues in a graphon `L²` action expansion lie in `[-1, 1]`.

This uses the genuine graphon operator-norm bound rather than any
finite-spectrum approximation. -/
theorem abs_eigen_le_one_of_graphon_action_expansion
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (mode : Nat -> Lp Real 2 mu)
    (eigen : Nat -> Real)
    (hmode : Orthonormal Real mode)
    (haction :
      ∀ f : Lp Real 2 mu, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :
    ∀ n, |eigen n| <= 1 := by
  intro n
  exact
    (abs_eigen_le_norm_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) mode eigen hmode haction n).trans
      (L2Kernel.norm_kernelOpCLM_le_one (mu := mu) hW)

/-- A vector-valued countable eigenmode expansion implies the quadratic-form
expansion by applying the continuous linear functional `g ↦ ⟪f, g⟫`.

This is closer to the usual spectral theorem statement than asking for the
quadratic-form expansion directly. -/
theorem quadratic_expansion_of_action_eigen_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (haction :
      ∀ f : E, HasSum
        (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
        (T f)) :
    ∀ f : E, HasSum
      (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2))
      (inner Real f (T f)) := by
  intro f
  have hinner := (haction f).mapL ((innerSL Real) f)
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hinner

/-- If some quadratic value is positive, then the top listed eigenvalue in a
countable spectral expansion is nonnegative.

This removes an otherwise artificial sign assumption in the C9 low band:
there `f = 1` has `⟪1, T 1⟫ = edgeDensity W μ > 0`. -/
theorem principal_nonneg_of_positive_quadratic_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (mode : Nat -> E)
    (eigen : Nat -> Real)
    (hquad_expansion :
      ∀ f : E, HasSum
        (fun n : Nat => eigen n * (inner Real f (mode n) ^ 2))
        (inner Real f (T f)))
    (hle : ∀ n, eigen n <= eigen 0)
    {f : E}
    (hpos : 0 < inner Real f (T f)) :
    0 <= eigen 0 := by
  by_contra hnot
  have hneg : eigen 0 < 0 := lt_of_not_ge hnot
  have hle_zero :
      inner Real f (T f) <= 0 := by
    exact hasSum_le
      (fun n => by
        have hn0 : eigen n <= 0 := (hle n).trans (le_of_lt hneg)
        exact mul_nonpos_of_nonpos_of_nonneg hn0 (sq_nonneg _))
      (hquad_expansion f) hasSum_zero
  linarith

/-- Operator-facing raw trace data with the standard Rayleigh quotient bound
instead of a quadratic-form bound. -/
structure C9L2RayleighTraceSpectralData
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  operator : Lp Real 2 mu →L[Real] Lp Real 2 mu
  eigen : Nat -> Real
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9
  maps_one :
    operator (L2Kernel.oneL2 (Omega := Omega) mu) = L2Kernel.degreeL2 hW
  rayleigh_le_principal :
    ∀ f : Lp Real 2 mu, f ≠ 0 -> operator.rayleighQuotient f <= eigen 0

/-- Operator-facing raw trace data for the canonical graphon `L²` operator.

Compared with `C9L2RayleighTraceSpectralData`, the operator is no longer an
input and the `maps_one` field is no longer an assumption: both are supplied
by `L2Kernel.kernelOpCLM` and `L2Kernel.kernelOpCLM_one_eq_degreeL2`.  The
remaining analytic work is therefore exactly the compact/self-adjoint spectral
trace theorem and the principal Rayleigh bound for this constructed operator. -/
structure C9CanonicalL2RayleighTraceSpectralData
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  eigen : Nat -> Real
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9
  rayleigh_le_principal :
    ∀ f : Lp Real 2 mu, f ≠ 0 ->
      (L2Kernel.kernelOpCLM (mu := mu) hW).rayleighQuotient f <= eigen 0

/-- Canonical graphon `L²` spectral data stated as a countable Hilbert
eigenbasis.

This is stronger, but more structural, than
`C9CanonicalL2RayleighTraceSpectralData`: the principal Rayleigh bound is not
assumed as a scalar black box.  Lean proves it from Parseval and the ordered
diagonalization fields below.  The trace identities remain explicit analytic
inputs to be supplied by the compact self-adjoint trace theorem. -/
structure C9CanonicalL2HilbertTraceSpectralData
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  basis : HilbertBasis Nat Real (Lp Real 2 mu)
  eigen : Nat -> Real
  diagonal :
    ∀ n, (L2Kernel.kernelOpCLM (mu := mu) hW) (basis n) = eigen n • basis n
  principal_max : ∀ n, eigen n <= eigen 0
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- Canonical graphon `L²` spectral data in the compact-operator shape.

This avoids assuming a countable Hilbert basis for all of `Lp ℝ 2 μ`.  The
countable `mode` family represents the nonzero compact spectral part.  Its
orthonormality supplies coordinate summability and Bessel's inequality in
Lean; the only expansion field left here is the vector-valued spectral action
expansion.  Lean derives the quadratic-form expansion from it.  Any
nonseparable residual is absorbed in the zero eigenspace.  The trace
identities remain the separate trace-class/Lidskii input. -/
structure C9CanonicalL2CompactExpansionTraceSpectralData
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  diagonal :
    ∀ n, (L2Kernel.kernelOpCLM (mu := mu) hW) (mode n) = eigen n • mode n
  principal_nonneg : 0 <= eigen 0
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- Compact-action trace data without a separate top-eigenvalue sign field.

In the C9 low band the sign is derivable from positive edge density, so this
is the more faithful hypothesis for that part of the proof. -/
structure C9CanonicalL2CompactActionTraceSpectralData
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  diagonal :
    ∀ n, (L2Kernel.kernelOpCLM (mu := mu) hW) (mode n) = eigen n • mode n
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- Compact-action trace data with no explicit diagonal-action field.

For an orthonormal mode family, the vector-valued action expansion already
forces `T (mode n) = eigen n • mode n`; Lean proves that in
`toCompactActionTraceSpectralData`. -/
structure C9CanonicalL2CompactActionTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  summable_square : Summable fun n : Nat => eigen n ^ 2
  trace_square :
    trace mu (compPow mu W 1) = ∑' n : Nat, eigen n ^ 2
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- No-diagonal compact-action data with only the square bound, not the
square trace identity.

This is a closer target for the next graphon-operator step: the square side
should follow from the Hilbert-Schmidt/Bessel inequality, while the cube and
ninth identities remain the trace-class/Lidskii inputs. -/
structure C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  summable_square : Summable fun n : Nat => eigen n ^ 2
  square_bound :
    (∑' n : Nat, eigen n ^ 2) <= edgeDensity W mu
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- No-diagonal compact-action data with only the square bound and no
cube/ninth trace assumptions.

For this interface the cube and ninth trace identities are derived from the
Hilbert action expansion by integrating the row-coordinate series
term-by-term.  This is the grounded replacement for carrying Lidskii-style
trace identities as fields in the low-band C9 hypothesis. -/
structure C9CanonicalL2CompactActionBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  summable_square : Summable fun n : Nat => eigen n ^ 2
  square_bound :
    (∑' n : Nat, eigen n ^ 2) <= edgeDensity W mu

/-- No-diagonal compact-action data with finite square bounds and no
cube/ninth trace assumptions.

This is the finite-estimate version of
`C9CanonicalL2CompactActionBoundSpectralDataNoDiag`: Lean derives square
summability and the infinite bound from the initial-segment inequalities,
then derives cube/ninth trace identities from the action expansion. -/
structure C9CanonicalL2CompactActionFiniteBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  finite_square_bound :
    ∀ N : Nat, (Finset.range N).sum (fun n => eigen n ^ 2) <= edgeDensity W mu

/-- No-diagonal compact-action data with the square side stated as finite
initial-segment estimates.

This is the most local square-bound interface in this file: it does not
assume summability of `λ_n^2` or an infinite `tsum` bound.  Those are derived
from the finite estimates by `summable_square_and_tsum_le_of_sum_range_square_le`.
The remaining trace inputs are still the cube/ninth identities. -/
structure C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  finite_square_bound :
    ∀ N : Nat, (Finset.range N).sum (fun n => eigen n ^ 2) <= edgeDensity W mu
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- No-diagonal compact-action data where the square side is supplied as a
finite Hilbert-Schmidt energy bound on the actual graphon operator images.

This is closer to the kernel theorem than directly assuming
`∑ eigen n² <= edgeDensity`: the finite square bound is derived from
orthonormality plus the action expansion.  The remaining unproved graphon
operator theorem is the finite-energy estimate itself. -/
structure C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  finite_energy_bound :
    ∀ N : Nat,
      (Finset.range N).sum
          (fun n => ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (mode n)‖ ^ 2) <=
        edgeDensity W mu
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- No-diagonal compact-action data where the square side is supplied as
finite operator-energy estimates, with no cube/ninth trace assumptions. -/
structure C9CanonicalL2CompactActionEnergySpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  finite_energy_bound :
    ∀ N : Nat,
      (Finset.range N).sum
          (fun n => ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (mode n)‖^2) <=
        edgeDensity W mu

/-- No-diagonal compact-action data where the finite operator-energy estimate
is derived from a row-wise Hilbert-Schmidt representation.

The row fields are the concrete graphon theorem still to prove: rows of the
kernel, viewed in `L²`, have square bound and represent the finite energy of
the listed modes by their squared coordinates. -/
structure C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  row : Omega -> Lp Real 2 mu
  row_finite_integrable :
    ∀ N : Nat,
      Integrable
        (fun x : Omega =>
          (Finset.range N).sum
            (fun n : Nat => inner Real (row x) (mode n) ^ 2)) mu
  row_norm_integrable :
    Integrable (fun x : Omega => inner Real (row x) (row x)) mu
  row_energy :
    ∀ N : Nat,
      (Finset.range N).sum
          (fun n : Nat => ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (mode n)‖ ^ 2) =
        ∫ x, (Finset.range N).sum
          (fun n : Nat => inner Real (row x) (mode n) ^ 2) ∂mu
  row_norm_bound :
    (∫ x, inner Real (row x) (row x) ∂mu) <= edgeDensity W mu
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- No-diagonal compact-action data with row-wise Hilbert-Schmidt estimates
and no cube/ninth trace assumptions. -/
structure C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  row : Omega -> Lp Real 2 mu
  row_finite_integrable :
    ∀ N : Nat,
      Integrable
        (fun x : Omega =>
          (Finset.range N).sum
            (fun n : Nat => inner Real (row x) (mode n) ^ 2)) mu
  row_norm_integrable :
    Integrable (fun x : Omega => inner Real (row x) (row x)) mu
  row_energy :
    ∀ N : Nat,
      (Finset.range N).sum
          (fun n : Nat => ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (mode n)‖ ^ 2) =
        ∫ x, (Finset.range N).sum
          (fun n : Nat => inner Real (row x) (mode n) ^ 2) ∂mu
  row_norm_bound :
    (∫ x, inner Real (row x) (row x) ∂mu) <= edgeDensity W mu

/-- The pure Hilbert-space action-expansion package.

This is now the smallest graphon-facing spectral input needed by the no-trace
C9 pipeline.  It contains only the orthonormal modes, eigenvalue ordering, and
the operator expansion for the completed `L²` graphon operator.  The
Hilbert-Schmidt row-energy fields are derived below from the graphon row
lemmas in `L2Kernel`, so no bounded representatives for eigenmodes are needed
at this layer. -/
structure C9CanonicalL2CompactActionCoreSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)

/-- Padded pure Hilbert-space action-expansion data.

This is the mathematically correct countable interface for compact graphon
operators, including finite-rank or finite-dimensional cases.  The eigenvalue
sequence may contain zero padding; only the modes whose listed eigenvalue is
nonzero are required to be orthonormal.  Terms with zero eigenvalue vanish in
the action expansion, so this avoids the impossible demand for an infinite
orthonormal sequence in a finite-dimensional `L²` space. -/
structure C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  nonzero_orthonormal :
    Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1)
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)

/-- Padded compact-action data with the principal Rayleigh lower bound stated
directly.

This is closer to the operator-theoretic theorem we ultimately need for C9:
the compact spectral decomposition supplies the action expansion and trace
moments, while the principal mode only has to dominate the constant-one
Rayleigh quotient `edgeDensity W mu`.  It therefore avoids asking for a
globally sorted enumeration of all padded eigenvalues. -/
structure C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  nonzero_orthonormal :
    Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1)
  principal_ge_edge : edgeDensity W mu <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)

/-- Hilbert-basis form of the nonzero spectral subspace for the canonical
graphon `L²` operator.

This is the next compact-spectral target below the padded C9 interface.  The
operator-theoretic theorem should construct `U` as the closed Hilbert sum of
the nonzero eigenspaces, choose the Hilbert basis `basis`, and prove that every
`T f` lies in `U`.  The conversion below then derives the padded action
expansion used by C9. -/
structure C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  U : Submodule Real (Lp Real 2 mu)
  complete : CompleteSpace U
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  basis : HilbertBasis {n : Nat // eigen n ≠ 0} Real U
  principal_max : ∀ n, eigen n <= eigen 0
  diagonal :
    ∀ n, eigen n ≠ 0 ->
      (L2Kernel.kernelOpCLM (mu := mu) hW) (mode n) = eigen n • mode n
  basis_mode :
    ∀ n : {n : Nat // eigen n ≠ 0}, ((basis n : U) : Lp Real 2 mu) = mode n.1
  range_mem :
    ∀ f : Lp Real 2 mu, (L2Kernel.kernelOpCLM (mu := mu) hW) f ∈ U

/-- The canonical target subspace for the range of the graphon operator:
the orthogonal complement of the zero eigenspace. -/
abbrev canonicalL2ZeroOrthogonalSubspace
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) : Submodule Real (Lp Real 2 mu) :=
  (Module.End.eigenspace
    (L2Kernel.kernelOpCLM (mu := mu) hW :
      Module.End Real (Lp Real 2 mu))
    0)ᗮ

/-- The nonzero eigenspaces are dense in the canonical zero-orthogonal
subspace for a compact graphon operator.

This is the exact dense-span fact needed to turn an orthonormal collection of
nonzero eigenvectors into a Hilbert basis of
`canonicalL2ZeroOrthogonalSubspace hW`. -/
theorem canonicalL2ZeroOrthogonalSubspace_nonzero_iSup_orthogonal_inf_eq_bot
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    ((⨆ lambda : {lambda : Real // lambda ≠ 0},
        Module.End.eigenspace
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          lambda.1)ᗮ ⊓
      canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) = ⊥ :=
  CompactSpectral.canonicalGraphonCompact_nonzero_iSup_orthogonal_inf_zero_eigenspace_orthogonal_eq_bot
    (mu := mu) hW hcompact

/-- Graphon-specialized form of
`compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_dense_in_zero_orthogonal`.

After choosing a Hilbert basis in every nonzero eigenspace of the compact
canonical graphon operator, the sigma-indexed collection of those basis
vectors is dense in `canonicalL2ZeroOrthogonalSubspace hW`. -/
theorem canonicalL2ZeroOrthogonalSubspace_nonzero_eigenspace_hilbertBasis_dense
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    {α : {lambda : Real // lambda ≠ 0} -> Type*}
    (b : ∀ lambda : {lambda : Real // lambda ≠ 0},
      HilbertBasis (α lambda) Real
        (Module.End.eigenspace
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          lambda.1)) :
    (Submodule.span Real
      (Set.range fun a : Sigma α =>
        (⟨((b a.1 a.2 :
            Module.End.eigenspace
              (L2Kernel.kernelOpCLM (mu := mu) hW :
                Module.End Real (Lp Real 2 mu))
              a.1.1) : Lp Real 2 mu),
          by
            rw [Submodule.mem_orthogonal]
            intro y hy
            have horth :
                Module.End.eigenspace
                    (L2Kernel.kernelOpCLM (mu := mu) hW :
                      Module.End Real (Lp Real 2 mu))
                    a.1.1 ⟂
                  Module.End.eigenspace
                    (L2Kernel.kernelOpCLM (mu := mu) hW :
                      Module.End Real (Lp Real 2 mu))
                    0 :=
              (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
                (T :=
                  (L2Kernel.kernelOpCLM (mu := mu) hW :
                    Module.End Real (Lp Real 2 mu)))
                (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)).isOrtho
                a.1.2
            exact horth.symm.inner_eq hy (b a.1 a.2).property⟩ :
          canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)))ᗮ = ⊥ := by
  exact
    compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_dense_in_zero_orthogonal
      (T := L2Kernel.kernelOpCLM (mu := mu) hW)
      hcompact
      (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
      b

/-- The same chosen nonzero-eigenspace bases are orthonormal as ambient
`L²` vectors. -/
theorem canonicalL2ZeroOrthogonalSubspace_nonzero_eigenspace_hilbertBasis_orthonormal
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu)
    {α : {lambda : Real // lambda ≠ 0} -> Type*}
    (b : ∀ lambda : {lambda : Real // lambda ≠ 0},
      HilbertBasis (α lambda) Real
        (Module.End.eigenspace
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          lambda.1)) :
    Orthonormal Real
      (fun a : Sigma α =>
        ((b a.1 a.2 :
          Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            a.1.1) : Lp Real 2 mu)) := by
  exact
    compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_orthonormal
      (T := L2Kernel.kernelOpCLM (mu := mu) hW)
      (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
      b

/-- The finite-basis index type over all nonzero eigenspaces of a compact
canonical graphon operator is countable. -/
theorem canonicalL2ZeroOrthogonalSubspace_countable_nonzero_eigenspace_finIndex
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Countable
      (Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            lambda.1))) := by
  exact
    compactSelfAdjoint_countable_nonzero_eigenspace_finIndex
      (T := L2Kernel.kernelOpCLM (mu := mu) hW)
      hcompact
      (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)

/-- Hilbert-basis spectral data with the canonical subspace fixed to
`(eigenspace T 0)ᗮ`.

Compared with `C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag`,
this removes the arbitrary subspace and range-membership fields.  The range
membership is proved for graphon operators by
`CompactSpectral.canonicalGraphon_apply_mem_orthogonal_zero_eigenspace`. -/
structure C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  basis :
    HilbertBasis {n : Nat // eigen n ≠ 0} Real
      (canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)
  principal_max : ∀ n, eigen n <= eigen 0
  diagonal :
    ∀ n, eigen n ≠ 0 ->
      (L2Kernel.kernelOpCLM (mu := mu) hW) (mode n) = eigen n • mode n
  basis_mode :
    ∀ n : {n : Nat // eigen n ≠ 0},
      ((basis n : canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) :
        Lp Real 2 mu) = mode n.1

/-- Leaner canonical zero-orthogonal eigenbasis data.

Here the listed modes are not separate fields: nonzero modes are the Hilbert
basis vectors, and zero-eigenvalue indices are padded by `0`.  This is closer
to the object produced by compact spectral theory. -/
structure C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  eigen : Nat -> Real
  basis :
    HilbertBasis {n : Nat // eigen n ≠ 0} Real
      (canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)
  principal_max : ∀ n, eigen n <= eigen 0
  diagonal_basis :
    ∀ n : {n : Nat // eigen n ≠ 0},
      (L2Kernel.kernelOpCLM (mu := mu) hW)
          ((basis n : canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) :
            Lp Real 2 mu) =
        eigen n.1 •
          ((basis n : canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) :
            Lp Real 2 mu)

namespace C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag

/-- The ambient nonzero modes inherited from the Hilbert basis are
orthonormal. -/
theorem nonzero_orthonormal
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag hW) :
    Orthonormal Real (fun n : {n : Nat // S.eigen n ≠ 0} => S.mode n.1) := by
  letI := S.complete
  have hb :
      Orthonormal Real
        (fun n : {n : Nat // S.eigen n ≠ 0} =>
          ((S.basis n : S.U) : Lp Real 2 mu)) := by
    simpa [Function.comp_def] using
      S.basis.orthonormal.comp_linearIsometry S.U.subtypeₗᵢ
  rw [orthonormal_iff_ite]
  intro i j
  simpa [S.basis_mode i, S.basis_mode j] using
    (orthonormal_iff_ite.mp hb i j)

/-- Hilbert-basis nonzero spectral-subspace data gives the padded compact
action data consumed by the C9 pipeline. -/
def toPaddedCoreSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  nonzero_orthonormal := S.nonzero_orthonormal
  principal_max := S.principal_max
  action_expansion := by
    letI := S.complete
    exact padded_action_expansion_of_nonzero_hilbertBasis
      (L2Kernel.kernelOpCLM (mu := mu) hW)
      S.mode S.eigen S.U S.basis
      (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
      S.diagonal S.basis_mode S.range_mem

end C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag

namespace C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag

/-- Canonical zero-orthogonal Hilbert-basis data imply the more general
nonzero Hilbert-basis spectral package. -/
def toNonzeroHilbertBasisSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag hW where
  U := canonicalL2ZeroOrthogonalSubspace (mu := mu) hW
  complete := inferInstance
  mode := S.mode
  eigen := S.eigen
  basis := S.basis
  principal_max := S.principal_max
  diagonal := S.diagonal
  basis_mode := S.basis_mode
  range_mem :=
    CompactSpectral.canonicalGraphon_apply_mem_orthogonal_zero_eigenspace
      (mu := mu) hW

/-- Canonical zero-orthogonal Hilbert-basis data give the padded compact
action data consumed by the C9 pipeline. -/
def toPaddedCoreSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW :=
  S.toNonzeroHilbertBasisSpectralDataNoDiag.toPaddedCoreSpectralDataNoDiag

end C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag

namespace C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag

/-- The padded ambient mode associated to canonical zero-orthogonal eigenbasis
data: nonzero indices use the Hilbert-basis vector, while zero indices are
irrelevant padding and are set to `0`. -/
noncomputable def mode
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag hW)
    (n : Nat) : Lp Real 2 mu :=
  if hn : S.eigen n ≠ 0 then
    ((S.basis ⟨n, hn⟩ :
      canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) : Lp Real 2 mu)
  else 0

/-- Lean canonical eigenbasis data imply the canonical zero-orthogonal
Hilbert-basis package with explicit padded modes. -/
noncomputable def toZeroOrthogonalHilbertBasisSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag hW) :
    C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  basis := S.basis
  principal_max := S.principal_max
  diagonal := by
    intro n hn
    simpa [mode, hn] using S.diagonal_basis ⟨n, hn⟩
  basis_mode := by
    intro n
    simp [mode, n.property]

/-- Lean canonical eigenbasis data give the padded compact-action data
consumed by the C9 pipeline. -/
noncomputable def toPaddedCoreSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag hW) :
    C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW :=
  S.toZeroOrthogonalHilbertBasisSpectralDataNoDiag.toPaddedCoreSpectralDataNoDiag

end C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag

/-- Lean canonical zero-orthogonal eigenbasis data with the principal Rayleigh
lower bound stated directly.

This is the Hilbert-basis analogue of
`C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag`: the
remaining operator theorem should construct the nonzero eigenbasis on
`(eigenspace T 0)ᗮ` and prove `edgeDensity W μ <= eigen 0`, but it need not
sort every padded eigenvalue below `eigen 0`. -/
structure C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  eigen : Nat -> Real
  basis :
    HilbertBasis {n : Nat // eigen n ≠ 0} Real
      (canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)
  principal_ge_edge : edgeDensity W mu <= eigen 0
  diagonal_basis :
    ∀ n : {n : Nat // eigen n ≠ 0},
      (L2Kernel.kernelOpCLM (mu := mu) hW)
          ((basis n : canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) :
            Lp Real 2 mu) =
        eigen n.1 •
          ((basis n : canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) :
            Lp Real 2 mu)

namespace C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag

/-- If the principal listed value is the operator norm, then the direct
principal Rayleigh bound follows from the constant-one Rayleigh quotient. -/
theorem principal_ge_edge_of_eigen_zero_eq_opNorm
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    {eigen : Nat -> Real}
    (h0 :
      eigen 0 = ‖L2Kernel.kernelOpCLM (mu := mu) hW‖) :
    edgeDensity W mu <= eigen 0 := by
  rw [h0]
  exact CompactSpectral.canonicalGraphon_edgeDensity_le_opNorm
    (mu := mu) hW

/-- A Rayleigh domination theorem for the canonical graphon operator implies
the scalar principal bound needed by the C9 low-band package. -/
theorem principal_ge_edge_of_rayleigh_le_principal
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    {eigen : Nat -> Real}
    (hray :
      ∀ f : Lp Real 2 mu, f ≠ 0 ->
        (L2Kernel.kernelOpCLM (mu := mu) hW).rayleighQuotient f <=
          eigen 0) :
    edgeDensity W mu <= eigen 0 := by
  rw [← CompactSpectral.canonicalGraphon_rayleigh_oneL2_eq_edgeDensity
    (mu := mu) hW]
  exact hray (L2Kernel.oneL2 (Omega := Omega) mu)
    (L2Kernel.oneL2_ne_zero (Omega := Omega) (mu := mu))

end C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag

namespace C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag

/-- The padded ambient mode associated to direct-principal canonical
zero-orthogonal eigenbasis data. -/
noncomputable def mode
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
        hW)
    (n : Nat) : Lp Real 2 mu :=
  if hn : S.eigen n ≠ 0 then
    ((S.basis ⟨n, hn⟩ :
      canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) : Lp Real 2 mu)
  else 0

/-- Direct-principal canonical eigenbasis data give the padded compact-action
data with direct principal lower bound. -/
noncomputable def toPaddedCorePrincipalBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
        hW) :
    C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  nonzero_orthonormal := by
    have hb :
        Orthonormal Real
          (fun n : {n : Nat // S.eigen n ≠ 0} =>
            ((S.basis n :
              canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) :
                Lp Real 2 mu)) := by
      simpa [Function.comp_def] using
        S.basis.orthonormal.comp_linearIsometry
          (canonicalL2ZeroOrthogonalSubspace (mu := mu) hW).subtypeₗᵢ
    rw [orthonormal_iff_ite]
    intro i j
    simpa [mode, i.property, j.property] using
      (orthonormal_iff_ite.mp hb i j)
  principal_ge_edge := S.principal_ge_edge
  action_expansion := by
    exact padded_action_expansion_of_nonzero_hilbertBasis
      (L2Kernel.kernelOpCLM (mu := mu) hW)
      S.mode S.eigen
      (canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)
      S.basis
      (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)
      (by
        intro n hn
        simpa [mode, hn] using S.diagonal_basis ⟨n, hn⟩)
      (by
        intro n
        simp [mode, n.property])
      (CompactSpectral.canonicalGraphon_apply_mem_orthogonal_zero_eigenspace
        (mu := mu) hW)

end C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag

/-- Countable orthonormal eigenmodes in the canonical zero-orthogonal subspace,
with dense span and the direct principal Rayleigh lower bound.

This is a more construction-friendly target than a bundled `HilbertBasis`:
once the nonzero modes are orthonormal and have dense span inside
`(eigenspace T 0)ᗮ`, Lean builds the Hilbert basis by
`HilbertBasis.mkOfOrthogonalEqBot`. -/
structure C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  nonzero_orthonormal :
    Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1)
  nonzero_mem :
    ∀ n : {n : Nat // eigen n ≠ 0},
      mode n.1 ∈ canonicalL2ZeroOrthogonalSubspace (mu := mu) hW
  principal_ge_edge : edgeDensity W mu <= eigen 0
  diagonal :
    ∀ n, eigen n ≠ 0 ->
      (L2Kernel.kernelOpCLM (mu := mu) hW) (mode n) = eigen n • mode n
  dense :
    (Submodule.span Real
      (Set.range fun n : {n : Nat // eigen n ≠ 0} =>
        (⟨mode n.1, nonzero_mem n⟩ :
          canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)))ᗮ = ⊥

namespace C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag

/-- Reindex an encodable nonzero eigenmode family as the `Nat`-padded
principal-bound data expected by the C9 pipeline.

The distinguished `principal` mode is placed at index `0`; every other mode is
placed at `encode i + 1`, with zero padding elsewhere. -/
noncomputable def ofEncodableIndex
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    {ι : Type*} [Encodable ι] [DecidableEq ι]
    (principal : ι)
    (mode : ι -> Lp Real 2 mu)
    (eigen : ι -> Real)
    (hne : ∀ i, eigen i ≠ 0)
    (horth : Orthonormal Real mode)
    (hmem :
      ∀ i, mode i ∈ canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)
    (hprincipal : edgeDensity W mu <= eigen principal)
    (hdiag :
      ∀ i,
        (L2Kernel.kernelOpCLM (mu := mu) hW) (mode i) =
          eigen i • mode i)
    (hdense :
      (Submodule.span Real
        (Set.range fun i : ι =>
          (⟨mode i, hmem i⟩ :
            canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)))ᗮ = ⊥) :
    C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
      hW where
  mode := principalPaddedMode principal mode
  eigen := principalPaddedEigen principal eigen
  nonzero_orthonormal :=
    principalPaddedMode_nonzero_orthonormal
      (principal := principal) (mode := mode) (eigen := eigen) hne horth
  nonzero_mem := by
    intro n
    obtain ⟨i, hi⟩ :=
      (principalPaddedEigen_ne_zero_iff_index (principal := principal)
        (eigen := eigen) hne n.1).mp n.property
    simpa [principalPaddedMode, hi] using hmem i
  principal_ge_edge := by
    simpa [principalPaddedEigen] using hprincipal
  diagonal := by
    intro n hn
    obtain ⟨i, hi⟩ :=
      (principalPaddedEigen_ne_zero_iff_index (principal := principal)
        (eigen := eigen) hne n).mp hn
    simpa [principalPaddedMode, principalPaddedEigen, hi] using hdiag i
  dense := by
    let U := canonicalL2ZeroOrthogonalSubspace (mu := mu) hW
    let v : ι -> U := fun i => ⟨mode i, hmem i⟩
    have hdense' :
        (Submodule.span Real
          (Set.range fun n : {n : Nat //
              principalPaddedEigen principal eigen n ≠ 0} =>
            principalPaddedMode principal v n.1))ᗮ = ⊥ :=
      principalPaddedMode_dense
        (principal := principal) (v := v) (eigen := eigen) hne (by
          change
            (Submodule.span Real
              (Set.range fun i : ι =>
                (⟨mode i, hmem i⟩ : U)))ᗮ = ⊥
          exact hdense)
    let G : Submodule Real U :=
      Submodule.span Real
        (Set.range fun n : {n : Nat //
            principalPaddedEigen principal eigen n ≠ 0} =>
          principalPaddedMode principal v n.1)
    let T : Submodule Real U :=
      Submodule.span Real
        (Set.range fun n : {n : Nat //
            principalPaddedEigen principal eigen n ≠ 0} =>
          (⟨principalPaddedMode principal mode n.1, by
            obtain ⟨i, hi⟩ :=
              (principalPaddedEigen_ne_zero_iff_index (principal := principal)
                (eigen := eigen) hne n.1).mp n.property
            simpa [principalPaddedMode, hi] using hmem i⟩ : U))
    have hGT : G ≤ T := by
      change
        Submodule.span Real
          (Set.range fun n : {n : Nat //
              principalPaddedEigen principal eigen n ≠ 0} =>
            principalPaddedMode principal v n.1) ≤
        Submodule.span Real
          (Set.range fun n : {n : Nat //
              principalPaddedEigen principal eigen n ≠ 0} =>
            (⟨principalPaddedMode principal mode n.1, by
              obtain ⟨i, hi⟩ :=
                (principalPaddedEigen_ne_zero_iff_index (principal := principal)
                  (eigen := eigen) hne n.1).mp n.property
              simpa [principalPaddedMode, hi] using hmem i⟩ : U))
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      refine Submodule.subset_span ⟨n, ?_⟩
      obtain ⟨i, hi⟩ :=
        (principalPaddedEigen_ne_zero_iff_index (principal := principal)
          (eigen := eigen) hne n.1).mp n.property
      ext
      simp [principalPaddedMode, hi, v]
    rw [eq_bot_iff]
    intro x hx
    have hxG : x ∈ Gᗮ := by
      exact Submodule.orthogonal_le hGT hx
    have hxG' :
        x ∈
          (Submodule.span Real
            (Set.range fun n : {n : Nat //
                principalPaddedEigen principal eigen n ≠ 0} =>
              principalPaddedMode principal v n.1))ᗮ := by
      exact hxG
    rw [← hdense']
    exact hxG'

/-- The ambient orthonormal nonzero modes are orthonormal inside the canonical
zero-orthogonal subspace. -/
theorem nonzero_orthonormal_subspace
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
        hW) :
    Orthonormal Real
      (fun n : {n : Nat // S.eigen n ≠ 0} =>
        (⟨S.mode n.1, S.nonzero_mem n⟩ :
          canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa using (orthonormal_iff_ite.mp S.nonzero_orthonormal i j)

/-- Dense orthonormal eigenmodes give the bundled canonical zero-orthogonal
Hilbert-basis eigen data. -/
noncomputable def toZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
        hW) :
    C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
      hW where
  eigen := S.eigen
  basis :=
    HilbertBasis.mkOfOrthogonalEqBot
      S.nonzero_orthonormal_subspace S.dense
  principal_ge_edge := S.principal_ge_edge
  diagonal_basis := by
    intro n
    have hb :
        ((HilbertBasis.mkOfOrthogonalEqBot
            S.nonzero_orthonormal_subspace S.dense n :
          canonicalL2ZeroOrthogonalSubspace (mu := mu) hW) :
            Lp Real 2 mu) = S.mode n.1 := by
      have hfun :=
        HilbertBasis.coe_mkOfOrthogonalEqBot
          S.nonzero_orthonormal_subspace S.dense
      exact congrArg
        (fun x : canonicalL2ZeroOrthogonalSubspace (mu := mu) hW =>
          (x : Lp Real 2 mu))
        (congrFun hfun n)
    simpa [hb] using S.diagonal n.1 n.property

/-- Dense orthonormal eigenmodes give the direct-principal padded compact
action package. -/
noncomputable def toPaddedCorePrincipalBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
        hW) :
    C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW :=
  S.toZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
    |>.toPaddedCorePrincipalBoundSpectralDataNoDiag

/-- Compact graphon eigenspace bases give the `Nat`-padded dense orthonormal
principal-bound package, once a principal nonzero eigenspace basis vector has
been selected.

This theorem performs the infinite-dimensional enumeration step without
finite-rank assumptions: each nonzero eigenspace contributes its finite
standard orthonormal basis, the resulting sigma type is countable, and
`ofEncodableIndex` pads it into a `Nat` sequence with the selected principal
mode at index `0`. -/
noncomputable def ofCompactGraphonEigenspaceFinIndex
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (principal :
      Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            lambda.1)))
    (hprincipal : edgeDensity W mu <= principal.1.1) :
    C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
      hW := by
  let T : Lp Real 2 mu →L[Real] Lp Real 2 mu :=
    L2Kernel.kernelOpCLM (mu := mu) hW
  let Index : Type _ :=
    Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
      Fin (Module.finrank Real
        (Module.End.eigenspace
          (T : Module.End Real (Lp Real 2 mu))
          lambda.1))
  haveI hfin :
      ∀ lambda : {lambda : Real // lambda ≠ 0},
        FiniteDimensional Real
          (Module.End.eigenspace
            (T : Module.End Real (Lp Real 2 mu))
            lambda.1) := by
    intro lambda
    exact ContinuousLinearMap.finite_dimensional_eigenspace
      (T := T) hcompact lambda.1 lambda.2
  let b :
      ∀ lambda : {lambda : Real // lambda ≠ 0},
        HilbertBasis
          (Fin (Module.finrank Real
            (Module.End.eigenspace
              (T : Module.End Real (Lp Real 2 mu))
              lambda.1)))
          Real
          (Module.End.eigenspace
            (T : Module.End Real (Lp Real 2 mu))
            lambda.1) :=
    fun lambda =>
      (stdOrthonormalBasis Real
        (Module.End.eigenspace
          (T : Module.End Real (Lp Real 2 mu))
          lambda.1)).toHilbertBasis
  let mode : Index -> Lp Real 2 mu :=
    fun a => ((b a.1 a.2 :
      Module.End.eigenspace
        (T : Module.End Real (Lp Real 2 mu))
        a.1.1) : Lp Real 2 mu)
  let eigen : Index -> Real := fun a => a.1.1
  haveI hcount : Countable Index := by
    change Countable
      (Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            lambda.1)))
    exact canonicalL2ZeroOrthogonalSubspace_countable_nonzero_eigenspace_finIndex
      (mu := mu) hW hcompact
  letI : Encodable Index := Encodable.ofCountable Index
  refine ofEncodableIndex
    (hW := hW)
    (principal := (principal : Index))
    (mode := mode)
    (eigen := eigen)
    ?hne ?horth ?hmem ?hprincipal ?hdiag ?hdense
  · intro a
    exact a.1.2
  · change Orthonormal Real
      (fun a : Sigma (fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            lambda.1))) =>
        ((b a.1 a.2 :
          Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            a.1.1) : Lp Real 2 mu))
    exact
      canonicalL2ZeroOrthogonalSubspace_nonzero_eigenspace_hilbertBasis_orthonormal
        (mu := mu) hW b
  · intro a
    rw [Submodule.mem_orthogonal]
    intro y hy
    have horth :
        Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            a.1.1 ⟂
          Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            0 :=
      (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
        (T :=
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu)))
        (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)).isOrtho
        a.1.2
    exact horth.symm.inner_eq hy (b a.1 a.2).property
  · exact hprincipal
  · intro a
    change
      (L2Kernel.kernelOpCLM (mu := mu) hW)
          ((b a.1 a.2 :
            Module.End.eigenspace
              (L2Kernel.kernelOpCLM (mu := mu) hW :
                Module.End Real (Lp Real 2 mu))
              a.1.1) : Lp Real 2 mu) =
        a.1.1 •
          ((b a.1 a.2 :
            Module.End.eigenspace
              (L2Kernel.kernelOpCLM (mu := mu) hW :
                Module.End Real (Lp Real 2 mu))
              a.1.1) : Lp Real 2 mu)
    exact Module.End.mem_eigenspace_iff.mp
      (b a.1 a.2).property
  · change
      (Submodule.span Real
        (Set.range fun i : Sigma (fun lambda : {lambda : Real // lambda ≠ 0} =>
          Fin (Module.finrank Real
            (Module.End.eigenspace
              (L2Kernel.kernelOpCLM (mu := mu) hW :
                Module.End Real (Lp Real 2 mu))
              lambda.1))) =>
          (⟨((b i.1 i.2 :
            Module.End.eigenspace
              (L2Kernel.kernelOpCLM (mu := mu) hW :
                Module.End Real (Lp Real 2 mu))
              i.1.1) : Lp Real 2 mu), by
            rw [Submodule.mem_orthogonal]
            intro y hy
            have horth :
                Module.End.eigenspace
                    (L2Kernel.kernelOpCLM (mu := mu) hW :
                      Module.End Real (Lp Real 2 mu))
                    i.1.1 ⟂
                  Module.End.eigenspace
                    (L2Kernel.kernelOpCLM (mu := mu) hW :
                      Module.End Real (Lp Real 2 mu))
                    0 :=
              (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
                (T :=
                  (L2Kernel.kernelOpCLM (mu := mu) hW :
                    Module.End Real (Lp Real 2 mu)))
                (L2Kernel.kernelOpCLM_isSymmetric (mu := mu) hW)).isOrtho
                i.1.2
            exact horth.symm.inner_eq hy (b i.1 i.2).property⟩ :
            canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)))ᗮ = ⊥
    exact canonicalL2ZeroOrthogonalSubspace_nonzero_eigenspace_hilbertBasis_dense
      (mu := mu) hW hcompact b

/-- If the positive operator norm of the canonical compact graphon operator is
an eigenvalue, the nonzero compact eigenspaces give the dense principal-bound
spectral package used by the C9 low-band proof.

The only selection made here is the principal eigenspace at `‖T‖`.  All other
nonzero eigenspaces are enumerated by `ofCompactGraphonEigenspaceFinIndex`, so
there is no finite-spectrum assumption. -/
noncomputable def ofCompactGraphonPositiveNormEndpoint
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW))
    (hp : 0 < edgeDensity W mu)
    (hendpoint :
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW :
          Module.End Real (Lp Real 2 mu))
        ‖L2Kernel.kernelOpCLM (mu := mu) hW‖) :
    C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
      hW := by
  let T : Lp Real 2 mu →L[Real] Lp Real 2 mu :=
    L2Kernel.kernelOpCLM (mu := mu) hW
  have hnorm_pos : 0 < ‖T‖ :=
    lt_of_lt_of_le hp
      (CompactSpectral.canonicalGraphon_edgeDensity_le_opNorm
        (mu := mu) hW)
  have hnorm_ne : ‖T‖ ≠ 0 := ne_of_gt hnorm_pos
  haveI :
      FiniteDimensional Real
        (Module.End.eigenspace
          (T : Module.End Real (Lp Real 2 mu))
          ‖T‖) :=
    ContinuousLinearMap.finite_dimensional_eigenspace
      (T := T) hcompact ‖T‖ hnorm_ne
  have hne_bot :
      Module.End.eigenspace
          (T : Module.End Real (Lp Real 2 mu))
          ‖T‖ ≠ ⊥ :=
    Module.End.hasEigenvalue_iff.mp hendpoint
  have hfinrank_pos :
      0 <
        Module.finrank Real
          (Module.End.eigenspace
            (T : Module.End Real (Lp Real 2 mu))
            ‖T‖) := by
    have hle :
        1 ≤
          Module.finrank Real
            (Module.End.eigenspace
              (T : Module.End Real (Lp Real 2 mu))
              ‖T‖) :=
      (Submodule.one_le_finrank_iff).mpr hne_bot
    exact hle
  let principal :
      Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace
            (L2Kernel.kernelOpCLM (mu := mu) hW :
              Module.End Real (Lp Real 2 mu))
            lambda.1)) :=
    ⟨⟨‖T‖, hnorm_ne⟩, ⟨0, hfinrank_pos⟩⟩
  exact
    ofCompactGraphonEigenspaceFinIndex
      (mu := mu) (hW := hW) hcompact principal
      (by
        change edgeDensity W mu <= ‖T‖
        exact
          CompactSpectral.canonicalGraphon_edgeDensity_le_opNorm
            (mu := mu) hW)

end C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag

/-- Countable orthonormal eigenmodes in the canonical zero-orthogonal
subspace, with dense span and a Rayleigh domination theorem.

This is closer to the compact self-adjoint theorem than the direct-principal
package: the graphon-specific scalar inequality `edgeDensity W μ <= eigen 0`
is derived by evaluating the Rayleigh bound at the constant-one vector. -/
structure C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  nonzero_orthonormal :
    Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1)
  nonzero_mem :
    ∀ n : {n : Nat // eigen n ≠ 0},
      mode n.1 ∈ canonicalL2ZeroOrthogonalSubspace (mu := mu) hW
  rayleigh_le_principal :
    ∀ f : Lp Real 2 mu, f ≠ 0 ->
      (L2Kernel.kernelOpCLM (mu := mu) hW).rayleighQuotient f <= eigen 0
  diagonal :
    ∀ n, eigen n ≠ 0 ->
      (L2Kernel.kernelOpCLM (mu := mu) hW) (mode n) = eigen n • mode n
  dense :
    (Submodule.span Real
      (Set.range fun n : {n : Nat // eigen n ≠ 0} =>
        (⟨mode n.1, nonzero_mem n⟩ :
          canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)))ᗮ = ⊥

namespace C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag

/-- Rayleigh-form dense orthonormal eigenmode data imply the direct-principal
dense orthonormal package. -/
def toZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
        hW) :
    C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
      hW where
  mode := S.mode
  eigen := S.eigen
  nonzero_orthonormal := S.nonzero_orthonormal
  nonzero_mem := S.nonzero_mem
  principal_ge_edge :=
    C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag.principal_ge_edge_of_rayleigh_le_principal
      (mu := mu) (hW := hW) (eigen := S.eigen) S.rayleigh_le_principal
  diagonal := S.diagonal
  dense := S.dense

/-- Rayleigh-form dense orthonormal eigenmode data give the direct-principal
padded compact-action package. -/
noncomputable def toPaddedCorePrincipalBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
        hW) :
    C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW :=
  S.toZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
    |>.toPaddedCorePrincipalBoundSpectralDataNoDiag

end C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag

/-- Countable orthonormal eigenmodes in the canonical zero-orthogonal
subspace, with dense span and principal value equal to the operator norm.

This is an even more concrete compact-spectral target than the Rayleigh-form
package: Mathlib gives `|Rayleigh f| <= ‖T‖`, so `eigen 0 = ‖T‖` implies the
Rayleigh domination field used downstream. -/
structure C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  nonzero_orthonormal :
    Orthonormal Real (fun n : {n : Nat // eigen n ≠ 0} => mode n.1)
  nonzero_mem :
    ∀ n : {n : Nat // eigen n ≠ 0},
      mode n.1 ∈ canonicalL2ZeroOrthogonalSubspace (mu := mu) hW
  eigen_zero_eq_opNorm :
    eigen 0 = ‖L2Kernel.kernelOpCLM (mu := mu) hW‖
  diagonal :
    ∀ n, eigen n ≠ 0 ->
      (L2Kernel.kernelOpCLM (mu := mu) hW) (mode n) = eigen n • mode n
  dense :
    (Submodule.span Real
      (Set.range fun n : {n : Nat // eigen n ≠ 0} =>
        (⟨mode n.1, nonzero_mem n⟩ :
          canonicalL2ZeroOrthogonalSubspace (mu := mu) hW)))ᗮ = ⊥

namespace C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag

/-- Op-norm-principal dense orthonormal eigenmode data imply Rayleigh-form
dense orthonormal eigenmode data. -/
def toZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag
        hW) :
    C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
      hW where
  mode := S.mode
  eigen := S.eigen
  nonzero_orthonormal := S.nonzero_orthonormal
  nonzero_mem := S.nonzero_mem
  rayleigh_le_principal := by
    intro f _hf
    have h :=
      (L2Kernel.kernelOpCLM (mu := mu) hW).rayleighQuotient_le_norm f
    have hle_norm :
        (L2Kernel.kernelOpCLM (mu := mu) hW).rayleighQuotient f <=
          ‖L2Kernel.kernelOpCLM (mu := mu) hW‖ :=
      (le_abs_self _).trans h
    simpa [S.eigen_zero_eq_opNorm] using hle_norm
  diagonal := S.diagonal
  dense := S.dense

/-- Op-norm-principal dense orthonormal eigenmode data give the
direct-principal padded compact-action package. -/
noncomputable def toPaddedCorePrincipalBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S :
      C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag
        hW) :
    C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW :=
  S.toZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
    |>.toPaddedCorePrincipalBoundSpectralDataNoDiag

end C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag

/-- No-diagonal compact-action data with bounded representatives for the
listed modes.

For this package the row-wise Hilbert-Schmidt fields are no longer separate
assumptions: rows are the actual graphon rows and Lean derives the finite
row-energy identity from the bounded representative lemmas in `L2Kernel`. -/
structure C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  rep : Nat -> Omega -> Real
  eigen : Nat -> Real
  rep_good : ∀ n : Nat, Good (rep n)
  mode_orthonormal :
    Orthonormal Real (fun n : Nat => L2Kernel.goodL2 (mu := mu) (rep_good n))
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat =>
        (eigen n * inner Real f (L2Kernel.goodL2 (mu := mu) (rep_good n))) •
          L2Kernel.goodL2 (mu := mu) (rep_good n))
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  trace_cube :
    trace mu (compPow mu W 2) = ∑' n : Nat, eigen n ^ 3
  trace_ninth :
    trace mu (compPow mu W 8) = ∑' n : Nat, eigen n ^ 9

/-- No-diagonal compact-action data with bounded representatives for the
listed modes, and no cube/ninth trace assumptions. -/
structure C9CanonicalL2CompactActionGoodRowSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  rep : Nat -> Omega -> Real
  eigen : Nat -> Real
  rep_good : ∀ n : Nat, Good (rep n)
  mode_orthonormal :
    Orthonormal Real (fun n : Nat => L2Kernel.goodL2 (mu := mu) (rep_good n))
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat =>
        (eigen n * inner Real f (L2Kernel.goodL2 (mu := mu) (rep_good n))) •
          L2Kernel.goodL2 (mu := mu) (rep_good n))
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)

/-- Compact-action trace data with trace identities stated directly as
`HasSum`s.

This is a slightly more analytic interface than the `tsum` version: each trace
field simultaneously records convergence of the corresponding spectral series
and identifies its value.  It still makes no finite-spectrum assumption and it
does not require a separate diagonal-action field. -/
structure C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu) where
  mode : Nat -> Lp Real 2 mu
  eigen : Nat -> Real
  mode_orthonormal : Orthonormal Real mode
  principal_max : ∀ n, eigen n <= eigen 0
  action_expansion :
    ∀ f : Lp Real 2 mu, HasSum
      (fun n : Nat => (eigen n * inner Real f (mode n)) • mode n)
      ((L2Kernel.kernelOpCLM (mu := mu) hW) f)
  trace_square_hasSum :
    HasSum (fun n : Nat => eigen n ^ 2) (trace mu (compPow mu W 1))
  trace_cube_hasSum :
    HasSum (fun n : Nat => eigen n ^ 3) (trace mu (compPow mu W 2))
  trace_ninth_hasSum :
    HasSum (fun n : Nat => eigen n ^ 9) (trace mu (compPow mu W 8))

/-- Complete compact-action trace data with direct `HasSum` trace identities.

This strengthens `C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag` by
requiring that every nonzero eigenvalue of the canonical graphon operator is
covered by the listed sequence.  It still allows an infinite nonzero spectrum
accumulating at zero, and it still permits repetitions or zero-eigenvalue
modes. -/
structure C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu)
    extends C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW where
  covers_nonzero_eigenvalues :
    ∀ lambda : Real,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        lambda ->
      lambda ≠ 0 ->
      ∃ n : Nat, eigen n = lambda

namespace C9CanonicalL2RayleighTraceSpectralData

/-- Convert canonical-operator trace data into the earlier explicit-operator
Rayleigh package. -/
def toL2RayleighTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2RayleighTraceSpectralData hW) :
    C9L2RayleighTraceSpectralData hW where
  operator := L2Kernel.kernelOpCLM (mu := mu) hW
  eigen := S.eigen
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  maps_one := L2Kernel.kernelOpCLM_one_eq_degreeL2 hW
  rayleigh_le_principal := S.rayleigh_le_principal

end C9CanonicalL2RayleighTraceSpectralData

namespace C9CanonicalL2HilbertTraceSpectralData

/-- Convert a canonical countable Hilbert-eigenbasis package into the canonical
Rayleigh package.  The Rayleigh bound is proved here from the Hilbert-basis
diagonalization, not assumed. -/
def toCanonicalL2RayleighTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2HilbertTraceSpectralData hW) :
    C9CanonicalL2RayleighTraceSpectralData hW where
  eigen := S.eigen
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  rayleigh_le_principal :=
    rayleigh_le_principal_of_hilbertBasis_diag
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.basis S.eigen
      S.diagonal S.principal_max

/-- Convert a countable Hilbert eigenbasis package into the no-sign compact
action package.

The vector-valued action expansion is proved from `basis.hasSum_repr` and the
diagonal action, rather than assumed as a separate field. -/
def toCompactActionTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2HilbertTraceSpectralData hW) :
    C9CanonicalL2CompactActionTraceSpectralData hW where
  mode := S.basis
  eigen := S.eigen
  mode_orthonormal := S.basis.orthonormal
  diagonal := S.diagonal
  principal_max := S.principal_max
  action_expansion :=
    action_expansion_of_complete_eigenmode_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.basis S.eigen
      S.diagonal
      (fun f => by
        simpa [HilbertBasis.repr_apply_apply, real_inner_comm] using
          S.basis.hasSum_repr f)
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

end C9CanonicalL2HilbertTraceSpectralData

namespace C9CanonicalL2CompactActionTraceSpectralDataNoDiag

/-- The eigenvalues listed in no-diagonal compact-action graphon data are
bounded by the graphon operator norm, hence by one. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 :=
  abs_eigen_le_one_of_graphon_action_expansion
    (mu := mu) (W := W) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- If the canonical graphon operator is compact, the eigenvalue list in
no-diagonal compact-action data tends to zero.

The diagonal action is derived from the vector-valued action expansion, so this
does not add a hidden finite-spectrum or finite-rank assumption. -/
theorem eigen_tendsto_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Filter.Tendsto S.eigen Filter.atTop (nhds 0) :=
  CompactSpectral.canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (mu := mu) hW hcompact S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- Every listed spectral value in no-diagonal compact-action data is an
actual eigenvalue of the canonical graphon operator. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  hasEigenvalue_of_orthonormal_diagonal
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal
      (diagonal_of_action_eigen_expansion
        (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
        S.mode_orthonormal S.action_expansion)

/-- The no-diagonal compact-action expansion propagates through every positive
iterate of the canonical graphon operator. -/
theorem action_expansion_iter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    ∀ k f, HasSum
      (fun n : Nat =>
        (S.eigen n ^ (k + 1) * inner Real f (S.mode n)) • S.mode n)
      (opIter (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f) :=
  action_expansion_iter_of_action_eigen_expansion
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- The same positive-iterate expansion, stated with the concrete `L2Kernel`
iterator used by the graphon kernel lemmas. -/
theorem action_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    ∀ k f, HasSum
      (fun n : Nat =>
        (S.eigen n ^ (k + 1) * inner Real f (S.mode n)) • S.mode n)
      (L2Kernel.clmIter (mu := mu)
        (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f) := by
  intro k f
  simpa [opIter_eq_l2_clmIter (mu := mu)
      (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f] using
    S.action_expansion_iter (mu := mu) (hW := hW) k f

/-- Quadratic-form expansion for every positive iterate of the canonical
graphon operator. -/
theorem quadratic_expansion_iter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    ∀ k f, HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) * (inner Real f (S.mode n) ^ 2))
      (inner Real f
        (opIter (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f)) :=
  quadratic_expansion_iter_of_action_eigen_expansion
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- Quadratic-form expansion for every positive iterate, stated with
`L2Kernel.clmIter`. -/
theorem quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    ∀ k f, HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) * (inner Real f (S.mode n) ^ 2))
      (inner Real f
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f)) := by
  intro k f
  simpa [opIter_eq_l2_clmIter (mu := mu)
      (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f] using
    S.quadratic_expansion_iter (mu := mu) (hW := hW) k f

/-- Applying the quadratic iterate expansion to an actual graphon row. -/
theorem graphon_row_quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (k : Nat) (x : Omega) :
    HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2))
      (inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)))) :=
  S.quadratic_expansion_clmIter (mu := mu) (hW := hW) k
    (L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))

/-- The square integral of a listed coordinate against actual graphon rows is
the square of the listed eigenvalue.

This combines the row-energy identity with the fact that the action expansion
diagonalizes each listed mode. -/
theorem integral_graphon_row_inner_sq_eq_eigen_sq
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (n : Nat) :
    (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (S.mode n) ^ 2 ∂mu) =
      S.eigen n ^ 2 := by
  have hrow_energy :
      ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖ ^ 2 =
        ∫ x, inner Real
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
          (S.mode n) ^ 2 ∂mu := by
    simpa using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  rw [← hrow_energy]
  have hdiag :=
    diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion n
  have hnorm_mode : ‖S.mode n‖ = 1 := S.mode_orthonormal.norm_eq_one n
  calc
    ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖ ^ 2
        = ‖S.eigen n • S.mode n‖ ^ 2 := by rw [hdiag]
    _ = S.eigen n ^ 2 := by
        rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs, sq_abs]

/-- Finite partial spectral moments are exactly the integrals of the weighted
finite row-coordinate sums.

This is the finite, no-interchange part of the trace/Lidskii passage: no
infinite sum is moved through an integral here. -/
theorem integral_sum_graphon_row_weighted_inner_sq_eq_sum_eigen_pow
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (k N : Nat) :
    (∫ x, (Finset.range N).sum (fun n : Nat =>
        S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2)) ∂mu) =
      (Finset.range N).sum (fun n : Nat => S.eigen n ^ (k + 3)) := by
  have hterm_integrable :
      ∀ n ∈ Finset.range N, Integrable (fun x : Omega =>
        S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2)) mu := by
    intro n hn
    have hcoord :
        Integrable (fun x : Omega =>
          inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2) mu := by
      simpa using
        L2Kernel.integrable_sum_graphon_row_inner_l2_sq
          (mu := mu) hW S.mode ({n} : Finset Nat)
    exact hcoord.const_mul (S.eigen n ^ (k + 1))
  rw [integral_finset_sum (Finset.range N) hterm_integrable]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [integral_const_mul]
  rw [S.integral_graphon_row_inner_sq_eq_eigen_sq (mu := mu) (hW := hW) n]
  calc
    S.eigen n ^ (k + 1) * S.eigen n ^ 2 =
        S.eigen n ^ ((k + 1) + 2) := by rw [← pow_add]
    _ = S.eigen n ^ (k + 3) := rfl

/-- The row-coordinate quadratic expansion may be integrated term-by-term.

The domination is not a finite-rank or finite-spectrum assertion: each term is
bounded in integral norm by the corresponding coordinate-square integral, and
those integrals are exactly the square-summable eigenvalue squares. -/
theorem hasSum_integral_graphon_row_weighted_inner_sq
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum
      (fun n : Nat =>
        ∫ x, S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2) ∂mu)
      (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))) ∂mu) := by
  let row : Omega -> Lp Real 2 mu :=
    fun x =>
      L2Kernel.goodL2 (mu := mu)
        (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  let coordSq : Nat -> Omega -> Real :=
    fun n x => inner Real (row x) (S.mode n) ^ 2
  let F : Nat -> Omega -> Real :=
    fun n x => S.eigen n ^ (k + 1) * coordSq n x
  let f : Omega -> Real :=
    fun x => inner Real (row x)
      (L2Kernel.clmIter (mu := mu)
        (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) (row x))
  have hcoord_integrable :
      ∀ n : Nat, Integrable (fun x : Omega => coordSq n x) mu := by
    intro n
    simpa [coordSq, row] using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  have hF_integrable : ∀ n : Nat, Integrable (F n) mu := by
    intro n
    exact (hcoord_integrable n).const_mul (S.eigen n ^ (k + 1))
  have hF_integral_norm_le :
      ∀ n : Nat, (∫ x, ‖F n x‖ ∂mu) <= S.eigen n ^ 2 := by
    intro n
    have hpow_abs : |S.eigen n ^ (k + 1)| <= 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg (S.eigen n)) (S.abs_eigen_le_one n)
    have hpoint :
        (fun x : Omega => ‖F n x‖) <= coordSq n := by
      intro x
      have hcoord_nonneg : 0 <= coordSq n x := sq_nonneg _
      calc
        ‖F n x‖ = |S.eigen n ^ (k + 1)| * coordSq n x := by
          simp [F, coordSq, Real.norm_eq_abs]
        _ <= 1 * coordSq n x := by
          exact mul_le_mul_of_nonneg_right hpow_abs hcoord_nonneg
        _ = coordSq n x := by rw [one_mul]
    calc
      (∫ x, ‖F n x‖ ∂mu) <= ∫ x, coordSq n x ∂mu := by
        exact integral_mono (hF_integrable n).norm (hcoord_integrable n) hpoint
      _ = S.eigen n ^ 2 := by
        simpa [coordSq, row] using
          S.integral_graphon_row_inner_sq_eq_eigen_sq (mu := mu) (hW := hW) n
  have hF_integral_norm_summable :
      Summable fun n : Nat => ∫ x, ‖F n x‖ ∂mu := by
    refine S.summable_square.of_norm_bounded ?_
    intro n
    have hnonneg : 0 <= ∫ x, ‖F n x‖ ∂mu :=
      integral_nonneg fun x => norm_nonneg (F n x)
    have hsq_nonneg : 0 <= S.eigen n ^ 2 := sq_nonneg _
    calc
      ‖∫ x, ‖F n x‖ ∂mu‖ = ∫ x, ‖F n x‖ ∂mu :=
        Real.norm_of_nonneg hnonneg
      _ <= S.eigen n ^ 2 := hF_integral_norm_le n
  have hseries :
      HasSum (fun n : Nat => ∫ x, F n x ∂mu)
        (∫ x, (∑' n : Nat, F n x) ∂mu) :=
    hasSum_integral_of_summable_integral_norm
      (F := F) hF_integrable hF_integral_norm_summable
  have htsum_fun : (fun x : Omega => ∑' n : Nat, F n x) = f := by
    funext x
    simpa [F, f, coordSq, row] using
      (S.graphon_row_quadratic_expansion_clmIter
        (mu := mu) (hW := hW) k x).tsum_eq
  rw [htsum_fun] at hseries
  simpa [F, f, coordSq, row] using hseries

/-- Trace moments are the corresponding countable eigenvalue moments once the
row-coordinate expansion is integrated. -/
theorem trace_compPow_hasSum_eigen_pow
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum (fun n : Nat => S.eigen n ^ (k + 3))
      (trace mu (compPow mu W (k + 2))) := by
  rw [L2Kernel.trace_compPow_eq_integral_row_inner_clmIter
    (mu := mu) (W := W) hW k]
  have hseries :=
    S.hasSum_integral_graphon_row_weighted_inner_sq
      (mu := mu) (hW := hW) k
  refine hseries.congr_fun ?_
  intro n
  symm
  rw [integral_const_mul]
  rw [S.integral_graphon_row_inner_sq_eq_eigen_sq (mu := mu) (hW := hW) n]
  calc
    S.eigen n ^ (k + 1) * S.eigen n ^ 2 =
        S.eigen n ^ ((k + 1) + 2) := by rw [← pow_add]
    _ = S.eigen n ^ (k + 3) := rfl

/-- Cubic trace identity derived from the Hilbert-space action expansion and
term-by-term integration. -/
theorem trace_compPow_two_eq_tsum_eigen_cube
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    trace mu (compPow mu W 2) =
      ∑' n : Nat, S.eigen n ^ 3 := by
  simpa using
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 0).tsum_eq.symm

/-- Ninth trace identity derived from the Hilbert-space action expansion and
term-by-term integration. -/
theorem trace_compPow_eight_eq_tsum_eigen_ninth
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    trace mu (compPow mu W 8) =
      ∑' n : Nat, S.eigen n ^ 9 := by
  simpa using
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 6).tsum_eq.symm

/-- A listed nonzero mode has a good representative if its graphon-operator
image has one.

This keeps the graphon spectral interface infinite-dimensional: no finite
nonzero-spectrum assumption is used. -/
theorem hasGoodRepresentative_mode_of_ne_zero_and_good_operator_image
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    {n : Nat}
    (hne : S.eigen n ≠ 0)
    {g : Omega -> Real} (hg : Good g)
    (himage :
      (L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n) =
        L2Kernel.goodL2 (mu := mu) hg) :
    HasGoodRepresentative (mu := mu) (S.mode n) :=
  hasGoodRepresentative_of_nonzero_eigenmode_and_good_operator_image
    (mu := mu) hg himage
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion n)
    hne

/-- A listed nonzero mode has a good representative once the completed graphon
operator is identified with the concrete pointwise `L²` transform. -/
theorem hasGoodRepresentative_mode_of_ne_zero_and_kernelOpCLM_eq_kernelOpL2OfL2
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    {n : Nat}
    (hne : S.eigen n ≠ 0)
    (hpointwise :
      (L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n) =
        L2Kernel.kernelOpL2OfL2 (mu := mu) hW (S.mode n)) :
    HasGoodRepresentative (mu := mu) (S.mode n) :=
  hasGoodRepresentative_of_nonzero_eigenmode_and_good_operator_image
    (mu := mu)
    (L2Kernel.good_kernelOp_l2 (mu := mu) hW (S.mode n))
    (by simpa [L2Kernel.kernelOpL2OfL2] using hpointwise)
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion n)
    hne

/-- Every listed nonzero mode in no-diagonal compact-action graphon data has a
bounded strongly measurable representative.

The proof uses the concrete pointwise representation of `kernelOpCLM` and then
divides by the nonzero listed eigenvalue. -/
theorem hasGoodRepresentative_mode_of_ne_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    {n : Nat}
    (hne : S.eigen n ≠ 0) :
    HasGoodRepresentative (mu := mu) (S.mode n) :=
  S.hasGoodRepresentative_mode_of_ne_zero_and_kernelOpCLM_eq_kernelOpL2OfL2
    hne
    (L2Kernel.kernelOpCLM_eq_kernelOpL2OfL2_apply
      (mu := mu) hW (S.mode n))

/-- In positive density, the top listed coefficient in no-diagonal
compact-action data is nonnegative.

This is derived directly from the vector-valued action expansion by evaluating
the quadratic-form expansion at the constant-one vector. -/
theorem principal_nonneg_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    0 <= S.eigen 0 := by
  have hquad :
      ∀ f : Lp Real 2 mu, HasSum
        (fun n : Nat => S.eigen n * (inner Real f (S.mode n) ^ 2))
        (inner Real f ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :=
    quadratic_expansion_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.action_expansion
  have hpos :
      0 <
        inner Real (L2Kernel.oneL2 (Omega := Omega) mu)
          ((L2Kernel.kernelOpCLM (mu := mu) hW)
            (L2Kernel.oneL2 (Omega := Omega) mu)) := by
    rw [L2Kernel.kernelOpCLM_one_eq_degreeL2 hW]
    simpa using L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW ▸ hp
  exact
    principal_nonneg_of_positive_quadratic_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      hquad S.principal_max hpos

/-- Cubic spectral summability follows from square summability and the graphon
operator norm bound. -/
theorem summable_cube
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    Summable fun n : Nat => S.eigen n ^ 3 := by
  refine S.summable_square.of_norm_bounded ?_
  intro n
  exact abs_cube_le_sq_of_sq_le_one
    ((sq_le_one_iff_abs_le_one (S.eigen n)).mpr (S.abs_eigen_le_one n))

/-- Ninth spectral summability follows from square summability and the graphon
operator norm bound. -/
theorem summable_ninth
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    Summable fun n : Nat => S.eigen n ^ 9 := by
  refine S.summable_square.of_norm_bounded ?_
  intro n
  exact abs_ninth_le_sq_of_sq_le_one
    ((sq_le_one_iff_abs_le_one (S.eigen n)).mpr (S.abs_eigen_le_one n))

/-- The negative ninth tail is summable for no-diagonal compact-action graphon
data. -/
theorem summable_negative_ninth_tail
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    Summable fun n : Nat => max (-(S.eigen (n + 1) ^ 9)) 0 := by
  have hshift : Summable fun n : Nat => S.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_ hshift
  intro n
  exact max_neg_ninth_le_sq_of_sq_le_one
    ((sq_le_one_iff_abs_le_one (S.eigen (n + 1))).mpr
      (S.abs_eigen_le_one (n + 1)))

/-- Recover the diagonal field from orthonormality and the vector-valued action
expansion. -/
def toCompactActionTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionTraceSpectralData hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  diagonal :=
    diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

/-- Forget the square trace identity, keeping only the square bound needed by
the C9 low-band argument. -/
def toCompactActionBoundTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  summable_square := S.summable_square
  square_bound := by
    rw [← S.trace_square]
    exact trace_compPow_one_le_edge hW
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

/-- No-diagonal compact-action trace data give the row-energy package with the
actual graphon rows.

The row-energy identity is proved directly for arbitrary `L²` modes from the
pointwise representation of `kernelOpCLM`, so this conversion does not require
bounded representatives for the modes. -/
def toCompactActionRowEnergyTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  row := fun x =>
    L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  row_finite_integrable := by
    intro N
    simpa using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode (Finset.range N)
  row_norm_integrable := by
    simpa using
      L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (goodK_of_isGraphon hW)
  row_energy := by
    intro N
    simpa using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode (Finset.range N)
  row_norm_bound := by
    rw [L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
      (mu := mu) (goodK_of_isGraphon hW)]
    exact kernelSqNorm_le_edge hW
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

/-- Add the top-eigenvalue sign field directly to no-diagonal compact-action
data in positive density.

Both missing fields of the signed compact-expansion package are derived from
the vector-valued action expansion: diagonal action by orthonormality, and
principal nonnegativity by testing the quadratic expansion at the constant-one
vector. -/
def toCompactExpansionTraceSpectralData_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9CanonicalL2CompactExpansionTraceSpectralData hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  diagonal :=
    diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion
  principal_nonneg := S.principal_nonneg_of_edgeDensity_pos hp
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

/-- Convert no-diagonal compact-action trace data with `tsum` trace identities
into the direct-`HasSum` trace package.

The only apparent extra information in the direct-`HasSum` package is
convergence of the cubic and ninth spectral traces.  For graphon operators,
that convergence follows from square summability and `|eigen n| <= 1`, so this
conversion has no additional analytic hypothesis. -/
def toCompactActionTraceSpectralDataHasSumNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  trace_square_hasSum :=
    S.summable_square.hasSum_iff.mpr S.trace_square.symm
  trace_cube_hasSum :=
    S.summable_cube.hasSum_iff.mpr S.trace_cube.symm
  trace_ninth_hasSum :=
    S.summable_ninth.hasSum_iff.mpr S.trace_ninth.symm

/-- No-diagonal compact-action trace data imply the complete direct-`HasSum`
compact-action package.  The `HasSum` trace identities come from the existing
`tsum` identities, and coverage of nonzero eigenvalues follows from the
action expansion. -/
def toCompleteCompactActionTraceSpectralDataHasSumNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  trace_square_hasSum :=
    S.summable_square.hasSum_iff.mpr S.trace_square.symm
  trace_cube_hasSum :=
    S.summable_cube.hasSum_iff.mpr S.trace_cube.symm
  trace_ninth_hasSum :=
    S.summable_ninth.hasSum_iff.mpr S.trace_ninth.symm
  covers_nonzero_eigenvalues := by
    intro lambda hlambda hlambda0
    exact
      mem_range_eigen_of_hasEigenvalue_of_action_eigen_expansion
        (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
        S.mode_orthonormal S.action_expansion hlambda hlambda0

end C9CanonicalL2CompactActionTraceSpectralDataNoDiag

namespace C9CanonicalL2CompactActionBoundSpectralDataNoDiag

/-- The eigenvalues listed in no-trace bound compact-action graphon data are
bounded by one. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 :=
  abs_eigen_le_one_of_graphon_action_expansion
    (mu := mu) (W := W) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- The no-trace bound compact-action expansion propagates through every
positive iterate of the canonical graphon operator. -/
theorem quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW) :
    ∀ k f, HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) * (inner Real f (S.mode n) ^ 2))
      (inner Real f
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f)) := by
  intro k f
  have hiter :=
    quadratic_expansion_iter_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion k f
  simpa [opIter_eq_l2_clmIter (mu := mu)
      (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f] using hiter

/-- Applying the quadratic iterate expansion to an actual graphon row. -/
theorem graphon_row_quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW)
    (k : Nat) (x : Omega) :
    HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2))
      (inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)))) :=
  S.quadratic_expansion_clmIter (mu := mu) (hW := hW) k
    (L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))

/-- The square integral of a listed coordinate against graphon rows is the
square of the listed eigenvalue. -/
theorem integral_graphon_row_inner_sq_eq_eigen_sq
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW)
    (n : Nat) :
    (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (S.mode n) ^ 2 ∂mu) =
      S.eigen n ^ 2 := by
  have hrow_energy :
      ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖^2 =
        ∫ x, inner Real
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
          (S.mode n) ^ 2 ∂mu := by
    simpa using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  rw [←hrow_energy]
  have hdiag :=
    diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion n
  have hnorm_mode : ‖S.mode n‖ = 1 := S.mode_orthonormal.norm_eq_one n
  calc
    ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖^2
        = ‖S.eigen n • S.mode n‖ ^ 2 := by rw [hdiag]
    _ = S.eigen n ^ 2 := by
        rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs, sq_abs]

/-- The row-coordinate quadratic expansion may be integrated term-by-term for
the no-trace bound compact-action interface. -/
theorem hasSum_integral_graphon_row_weighted_inner_sq
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum
      (fun n : Nat =>
        ∫ x, S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2) ∂mu)
      (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))) ∂mu) := by
  let row : Omega -> Lp Real 2 mu :=
    fun x =>
      L2Kernel.goodL2 (mu := mu)
        (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  let coordSq : Nat -> Omega -> Real :=
    fun n x => inner Real (row x) (S.mode n) ^ 2
  let F : Nat -> Omega -> Real :=
    fun n x => S.eigen n ^ (k + 1) * coordSq n x
  let f : Omega -> Real :=
    fun x => inner Real (row x)
      (L2Kernel.clmIter (mu := mu)
        (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) (row x))
  have hcoord_integrable :
      ∀ n : Nat, Integrable (fun x : Omega => coordSq n x) mu := by
    intro n
    simpa [coordSq, row] using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  have hF_integrable : ∀ n : Nat, Integrable (F n) mu := by
    intro n
    exact (hcoord_integrable n).const_mul (S.eigen n ^ (k + 1))
  have hF_integral_norm_le :
      ∀ n : Nat, (∫ x, ‖F n x‖ ∂mu) <= S.eigen n ^ 2 := by
    intro n
    have hpow_abs : |S.eigen n ^ (k + 1)| <= 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg (S.eigen n)) (S.abs_eigen_le_one n)
    have hpoint :
        (fun x : Omega => ‖F n x‖) <= coordSq n := by
      intro x
      have hcoord_nonneg : 0 <= coordSq n x := sq_nonneg _
      calc
        ‖F n x‖ = |S.eigen n ^ (k + 1)| * coordSq n x := by
          simp [F, coordSq, Real.norm_eq_abs]
        _ <= 1 * coordSq n x := by
          exact mul_le_mul_of_nonneg_right hpow_abs hcoord_nonneg
        _ = coordSq n x := by rw [one_mul]
    calc
      (∫ x, ‖F n x‖ ∂mu) <= ∫ x, coordSq n x ∂mu := by
        exact integral_mono (hF_integrable n).norm (hcoord_integrable n) hpoint
      _ = S.eigen n ^ 2 := by
        simpa [coordSq, row] using
          S.integral_graphon_row_inner_sq_eq_eigen_sq (mu := mu) (hW := hW) n
  have hF_integral_norm_summable :
      Summable fun n : Nat => ∫ x, ‖F n x‖ ∂mu := by
    refine S.summable_square.of_norm_bounded ?_
    intro n
    have hnonneg : 0 <= ∫ x, ‖F n x‖ ∂mu :=
      integral_nonneg fun x => norm_nonneg (F n x)
    calc
      ‖∫ x, ‖F n x‖ ∂mu‖ = ∫ x, ‖F n x‖ ∂mu :=
        Real.norm_of_nonneg hnonneg
      _ <= S.eigen n ^ 2 := hF_integral_norm_le n
  have hseries :
      HasSum (fun n : Nat => ∫ x, F n x ∂mu)
        (∫ x, (∑' n : Nat, F n x) ∂mu) :=
    hasSum_integral_of_summable_integral_norm
      (F := F) hF_integrable hF_integral_norm_summable
  have htsum_fun : (fun x : Omega => ∑' n : Nat, F n x) = f := by
    funext x
    simpa [F, f, coordSq, row] using
      (S.graphon_row_quadratic_expansion_clmIter
        (mu := mu) (hW := hW) k x).tsum_eq
  rw [htsum_fun] at hseries
  simpa [F, f, coordSq, row] using hseries

/-- Trace moments are the corresponding countable eigenvalue moments for
no-trace bound compact-action data. -/
theorem trace_compPow_hasSum_eigen_pow
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum (fun n : Nat => S.eigen n ^ (k + 3))
      (trace mu (compPow mu W (k + 2))) := by
  rw [L2Kernel.trace_compPow_eq_integral_row_inner_clmIter
    (mu := mu) (W := W) hW k]
  have hseries :=
    S.hasSum_integral_graphon_row_weighted_inner_sq
      (mu := mu) (hW := hW) k
  refine hseries.congr_fun ?_
  intro n
  symm
  rw [integral_const_mul]
  rw [S.integral_graphon_row_inner_sq_eq_eigen_sq (mu := mu) (hW := hW) n]
  calc
    S.eigen n ^ (k + 1) * S.eigen n ^ 2 =
        S.eigen n ^ ((k + 1) + 2) := by rw [← pow_add]
    _ = S.eigen n ^ (k + 3) := rfl

/-- Convert no-trace bound compact-action data into the existing bound trace
package by deriving the cube and ninth trace identities. -/
def toCompactActionBoundTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  summable_square := S.summable_square
  square_bound := S.square_bound
  trace_cube :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 0).tsum_eq.symm
  trace_ninth :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 6).tsum_eq.symm

end C9CanonicalL2CompactActionBoundSpectralDataNoDiag

namespace C9CanonicalL2CompactActionFiniteBoundSpectralDataNoDiag

/-- Finite square-bound no-trace compact-action data imply the infinite
bound no-trace package. -/
def toCompactActionBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionFiniteBoundSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW :=
  let hsq :=
    summable_square_and_tsum_le_of_sum_range_square_le
      S.eigen S.finite_square_bound
  {
    mode := S.mode
    eigen := S.eigen
    mode_orthonormal := S.mode_orthonormal
    principal_max := S.principal_max
    action_expansion := S.action_expansion
    summable_square := hsq.1
    square_bound := hsq.2
  }

end C9CanonicalL2CompactActionFiniteBoundSpectralDataNoDiag

namespace C9CanonicalL2CompactActionEnergySpectralDataNoDiag

/-- Energy compact-action data imply the finite square-bound no-trace
package. -/
def toCompactActionFiniteBoundSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionEnergySpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionFiniteBoundSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  finite_square_bound :=
    sum_range_eigen_sq_le_of_action_eigen_expansion_and_energy_bound
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion S.finite_energy_bound

end C9CanonicalL2CompactActionEnergySpectralDataNoDiag

namespace C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag

/-- The eigenvalues listed in bound no-diagonal compact-action graphon data
are bounded by one. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 :=
  abs_eigen_le_one_of_graphon_action_expansion
    (mu := mu) (W := W) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- If the canonical graphon operator is compact, the eigenvalue list in
bound no-diagonal compact-action data tends to zero. -/
theorem eigen_tendsto_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Filter.Tendsto S.eigen Filter.atTop (nhds 0) :=
  CompactSpectral.canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (mu := mu) hW hcompact S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- Every listed spectral value in bound no-diagonal compact-action data is an
actual eigenvalue of the canonical graphon operator. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  hasEigenvalue_of_orthonormal_diagonal
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- In positive density, the top listed coefficient in bound no-diagonal
compact-action data is nonnegative. -/
theorem principal_nonneg_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    0 <= S.eigen 0 := by
  have hquad :
      ∀ f : Lp Real 2 mu, HasSum
        (fun n : Nat => S.eigen n * (inner Real f (S.mode n) ^ 2))
        (inner Real f ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :=
    quadratic_expansion_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.action_expansion
  have hpos :
      0 <
        inner Real (L2Kernel.oneL2 (Omega := Omega) mu)
          ((L2Kernel.kernelOpCLM (mu := mu) hW)
            (L2Kernel.oneL2 (Omega := Omega) mu)) := by
    rw [L2Kernel.kernelOpCLM_one_eq_degreeL2 hW]
    simpa using L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW ▸ hp
  exact
    principal_nonneg_of_positive_quadratic_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      hquad S.principal_max hpos

/-- The principal lower bound follows from the compact action expansion and
positive edge density; no square trace identity is used. -/
theorem principal_ge_edge_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    edgeDensity W mu <= S.eigen 0 := by
  have hquad_expansion :
      ∀ f : Lp Real 2 mu, HasSum
        (fun n : Nat => S.eigen n * (inner Real f (S.mode n) ^ 2))
        (inner Real f ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :=
    quadratic_expansion_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.action_expansion
  have hquad :=
    quadratic_le_principal_of_compact_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      hquad_expansion
      (summable_inner_sq_of_orthonormal S.mode_orthonormal)
      (tsum_inner_sq_le_self_of_orthonormal S.mode_orthonormal)
      S.principal_max (S.principal_nonneg_of_edgeDensity_pos hp)
  have h := hquad (L2Kernel.oneL2 (Omega := Omega) mu)
  rw [L2Kernel.kernelOpCLM_one_eq_degreeL2 hW,
    L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW,
    L2Kernel.inner_oneL2_oneL2] at h
  simpa using h

/-- Bound compact-action data give the graphon-facing bound trace package in
positive density. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9BoundTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.summable_square
  square_bound := S.square_bound
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  principal_ge_edge := S.principal_ge_edge_of_edgeDensity_pos hp

end C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag

namespace C9CanonicalL2CompactActionBoundSpectralDataNoDiag

/-- In positive density, no-trace bound compact-action data give the
graphon-facing bound trace package. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9BoundTraceSpectralData W mu :=
  (S.toCompactActionBoundTraceSpectralDataNoDiag
    (mu := mu) (hW := hW)).toBoundTraceSpectralData hp

end C9CanonicalL2CompactActionBoundSpectralDataNoDiag

namespace C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag

/-- The eigenvalues listed in finite-bound no-diagonal compact-action graphon
data are bounded by one. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 :=
  abs_eigen_le_one_of_graphon_action_expansion
    (mu := mu) (W := W) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- If the canonical graphon operator is compact, the eigenvalue list in
finite-bound no-diagonal compact-action data tends to zero. -/
theorem eigen_tendsto_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Filter.Tendsto S.eigen Filter.atTop (nhds 0) :=
  CompactSpectral.canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (mu := mu) hW hcompact S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- Every listed spectral value in finite-bound no-diagonal compact-action
data is an actual eigenvalue of the canonical graphon operator. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  hasEigenvalue_of_orthonormal_diagonal
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- Finite square-bound compact-action data imply the infinite square-bound
package.

This is the bridge from a finite-dimensional Bessel estimate on every initial
segment to the countable spectral package consumed by C9. -/
def toCompactActionBoundTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW :=
  let hsq :=
    summable_square_and_tsum_le_of_sum_range_square_le
      S.eigen S.finite_square_bound
  {
    mode := S.mode
    eigen := S.eigen
    mode_orthonormal := S.mode_orthonormal
    principal_max := S.principal_max
    action_expansion := S.action_expansion
    summable_square := hsq.1
    square_bound := hsq.2
    trace_cube := S.trace_cube
    trace_ninth := S.trace_ninth
  }

/-- In positive density, finite square-bound compact-action data give the
graphon-facing bound trace package. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9BoundTraceSpectralData W mu :=
  S.toCompactActionBoundTraceSpectralDataNoDiag.toBoundTraceSpectralData hp

end C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag

namespace C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag

/-- The eigenvalues listed in energy no-diagonal compact-action graphon data
are bounded by one. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 :=
  abs_eigen_le_one_of_graphon_action_expansion
    (mu := mu) (W := W) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- If the canonical graphon operator is compact, the eigenvalue list in
energy no-diagonal compact-action data tends to zero. -/
theorem eigen_tendsto_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Filter.Tendsto S.eigen Filter.atTop (nhds 0) :=
  CompactSpectral.canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (mu := mu) hW hcompact S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- Every listed spectral value in energy no-diagonal compact-action data is
an actual eigenvalue of the canonical graphon operator. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  hasEigenvalue_of_orthonormal_diagonal
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- Energy compact-action data imply the finite square-bound package.

The square bound is proved, not copied: diagonal action turns
`‖T mode_n‖²` into `eigen_n²`, and the finite-energy hypothesis supplies the
kernel-side bound. -/
def toCompactActionFiniteBoundTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  finite_square_bound :=
    sum_range_eigen_sq_le_of_action_eigen_expansion_and_energy_bound
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion S.finite_energy_bound
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

/-- In positive density, energy compact-action data give the graphon-facing
bound trace package. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9BoundTraceSpectralData W mu :=
  S.toCompactActionFiniteBoundTraceSpectralDataNoDiag.toBoundTraceSpectralData hp

end C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag

namespace C9CanonicalL2CompactActionCoreSpectralDataNoDiag

/-- The older full-orthonormal core package is a special case of the padded
package: restrict the orthonormal family to the nonzero eigenvalue indices. -/
def toPaddedCoreSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionCoreSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  nonzero_orthonormal :=
    S.mode_orthonormal.comp (fun n : {n : Nat // S.eigen n ≠ 0} => n.1)
      (fun _ _ h => Subtype.ext h)
  principal_max := S.principal_max
  action_expansion := S.action_expansion

/-- Pure compact-action spectral data imply the row-energy no-trace package.

The row is the actual graphon row `W x ·` viewed in `L²`; finite row-energy
identities and the row norm bound are graphon kernel facts already proved in
`L2Kernel`. -/
def toCompactActionRowEnergySpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionCoreSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  row := fun x =>
    L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  row_finite_integrable := by
    intro N
    simpa using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode (Finset.range N)
  row_norm_integrable := by
    simpa using
      L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (goodK_of_isGraphon hW)
  row_energy := by
    intro N
    simpa using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode (Finset.range N)
  row_norm_bound := by
    rw [L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
      (mu := mu) (goodK_of_isGraphon hW)]
    exact kernelSqNorm_le_edge hW

end C9CanonicalL2CompactActionCoreSpectralDataNoDiag

namespace C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag

/-- The quadratic-form expansion obtained by taking the inner product of the
padded vector-valued action expansion with `f`. -/
theorem quadratic_expansion
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (f : Lp Real 2 mu) :
    HasSum
      (fun n : Nat => S.eigen n * (inner Real f (S.mode n) ^ 2))
      (inner Real f ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :=
  quadratic_expansion_of_action_eigen_expansion
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.action_expansion f

/-- Every nonzero listed padded mode is a genuine eigenmode of the graphon
operator. -/
theorem diagonal_of_ne_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    {n : Nat} (hne : S.eigen n ≠ 0) :
    (L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n) =
      S.eigen n • S.mode n :=
  diagonal_of_padded_action_eigen_expansion
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.nonzero_orthonormal S.action_expansion n hne

/-- In positive density, the top coefficient in padded core data is
nonnegative. -/
theorem principal_nonneg_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    0 <= S.eigen 0 := by
  have hpos :
      0 <
        inner Real (L2Kernel.oneL2 (Omega := Omega) mu)
          ((L2Kernel.kernelOpCLM (mu := mu) hW)
            (L2Kernel.oneL2 (Omega := Omega) mu)) := by
    rw [L2Kernel.kernelOpCLM_one_eq_degreeL2 hW]
    simpa using L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW ▸ hp
  exact
    principal_nonneg_of_positive_quadratic_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      (S.quadratic_expansion (mu := mu) (hW := hW)) S.principal_max hpos

/-- The principal lower bound follows from padded compact-action data and
positive edge density.  Zero padding causes no coordinate-summability
assumption here; the Rayleigh estimate uses only finite filtered Bessel
inequalities on nonzero modes. -/
theorem principal_ge_edge_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    edgeDensity W mu <= S.eigen 0 := by
  have hquad :=
    quadratic_le_principal_of_padded_compact_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.nonzero_orthonormal
      (S.quadratic_expansion (mu := mu) (hW := hW))
      S.principal_max (S.principal_nonneg_of_edgeDensity_pos hp)
  have h := hquad (L2Kernel.oneL2 (Omega := Omega) mu)
  rw [L2Kernel.kernelOpCLM_one_eq_degreeL2 hW,
    L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW,
    L2Kernel.inner_oneL2_oneL2] at h
  simpa using h

/-- Quadratic-form expansion for every positive iterate of the canonical
graphon operator, in the zero-padded spectral interface. -/
theorem quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW) :
    ∀ k f, HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) * (inner Real f (S.mode n) ^ 2))
      (inner Real f
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f)) := by
  intro k f
  have hiter :=
    quadratic_expansion_iter_of_padded_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.nonzero_orthonormal S.action_expansion k f
  simpa [opIter_eq_l2_clmIter (mu := mu)
      (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f] using hiter

/-- Applying the padded quadratic iterate expansion to an actual graphon row. -/
theorem graphon_row_quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (k : Nat) (x : Omega) :
    HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2))
      (inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)))) :=
  S.quadratic_expansion_clmIter (mu := mu) (hW := hW) k
    (L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))

/-- Finite initial square bounds for padded core data.

Zero-padded indices contribute no eigenvalue square.  On the remaining finite
set, diagonal action and nonzero-mode orthonormality identify eigenvalue
squares with operator-energy terms, which are then bounded by the graphon row
Bessel inequality. -/
theorem finite_square_bound
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW) :
    ∀ N : Nat,
      (Finset.range N).sum (fun n => S.eigen n ^ 2) <= edgeDensity W mu := by
  intro N
  classical
  let T := L2Kernel.kernelOpCLM (mu := mu) hW
  let row : Omega -> Lp Real 2 mu := fun x =>
    L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  let s : Finset Nat :=
    (Finset.range N).filter (fun n : Nat => S.eigen n ≠ 0)
  have hfilter :
      (Finset.range N).sum (fun n => S.eigen n ^ 2) =
        s.sum (fun n => S.eigen n ^ 2) := by
    symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    by_cases hn : S.eigen n = 0
    · simp [hn]
    · simp [hn]
  have hdiag_energy :
      s.sum (fun n => S.eigen n ^ 2) =
        s.sum (fun n => ‖T (S.mode n)‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hne : S.eigen n ≠ 0 := (Finset.mem_filter.mp hn).2
    have hdiag :
        T (S.mode n) = S.eigen n • S.mode n :=
      S.diagonal_of_ne_zero (mu := mu) (hW := hW) hne
    have hnorm_mode : ‖S.mode n‖ = 1 := by
      simpa using S.nonzero_orthonormal.norm_eq_one ⟨n, hne⟩
    calc
      S.eigen n ^ 2 = |S.eigen n| ^ 2 := by rw [sq_abs]
      _ = ‖S.eigen n • S.mode n‖ ^ 2 := by
        rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs]
      _ = ‖T (S.mode n)‖ ^ 2 := by rw [hdiag]
  have hrow_energy :
      s.sum (fun n => ‖T (S.mode n)‖ ^ 2) =
        ∫ x, s.sum
          (fun n : Nat => inner Real (row x) (S.mode n) ^ 2) ∂mu := by
    simpa [T, row, s] using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode s
  have hfinite_integrable :
      Integrable
        (fun x : Omega =>
          s.sum (fun n : Nat => inner Real (row x) (S.mode n) ^ 2)) mu := by
    simpa [row, s] using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode s
  have hrow_norm_integrable :
      Integrable (fun x : Omega => inner Real (row x) (row x)) mu := by
    simpa [row] using
      L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (goodK_of_isGraphon hW)
  have hpoint :
      ∀ x : Omega,
        s.sum (fun n : Nat => inner Real (row x) (S.mode n) ^ 2) <=
          inner Real (row x) (row x) := by
    intro x
    simpa [row, s] using
      sum_filter_ne_zero_inner_sq_le_self_of_padded_orthonormal
        (mode := S.mode) (eigen := S.eigen)
        S.nonzero_orthonormal (row x) (Finset.range N)
  calc
    (Finset.range N).sum (fun n => S.eigen n ^ 2)
        = s.sum (fun n => S.eigen n ^ 2) := hfilter
    _ = s.sum (fun n => ‖T (S.mode n)‖ ^ 2) := hdiag_energy
    _ = ∫ x, s.sum
          (fun n : Nat => inner Real (row x) (S.mode n) ^ 2) ∂mu := hrow_energy
    _ <= ∫ x, inner Real (row x) (row x) ∂mu := by
      exact integral_mono hfinite_integrable hrow_norm_integrable hpoint
    _ <= edgeDensity W mu := by
      rw [show (∫ x, inner Real (row x) (row x) ∂mu) =
          ∫ x, inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)) ∂mu by
        rfl]
      rw [L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
        (mu := mu) (goodK_of_isGraphon hW)]
      exact kernelSqNorm_le_edge hW

/-- Square summability and the infinite square bound follow from the finite
initial square bounds for padded core data. -/
theorem summable_square_and_square_bound
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW) :
    Summable (fun n : Nat => S.eigen n ^ 2) ∧
      (∑' n : Nat, S.eigen n ^ 2) <= edgeDensity W mu :=
  summable_square_and_tsum_le_of_sum_range_square_le
    S.eigen (S.finite_square_bound (mu := mu) (hW := hW))

/-- Square summability for padded core data. -/
theorem summable_square
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW) :
    Summable (fun n : Nat => S.eigen n ^ 2) :=
  (S.summable_square_and_square_bound (mu := mu) (hW := hW)).1

/-- Infinite square bound for padded core data. -/
theorem square_bound
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW) :
    (∑' n : Nat, S.eigen n ^ 2) <= edgeDensity W mu :=
  (S.summable_square_and_square_bound (mu := mu) (hW := hW)).2

/-- Each listed padded eigenvalue is bounded by one in absolute value. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 := by
  intro n
  have hsq_le_edge :
      S.eigen n ^ 2 <= ∑' m : Nat, S.eigen m ^ 2 :=
    single_le_tsum_of_nonneg
      (S.summable_square (mu := mu) (hW := hW)) (fun m => sq_nonneg _) n
  have hsq_le_one :
      S.eigen n ^ 2 <= 1 :=
    hsq_le_edge.trans
      ((S.square_bound (mu := mu) (hW := hW)).trans (edgeDensity_le_one hW))
  exact (sq_le_one_iff_abs_le_one (S.eigen n)).mp hsq_le_one

/-- For a nonzero listed padded mode, the square row-coordinate integral is
the square of its eigenvalue. -/
theorem integral_graphon_row_inner_sq_eq_eigen_sq_of_ne_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    {n : Nat} (hne : S.eigen n ≠ 0) :
    (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (S.mode n) ^ 2 ∂mu) =
      S.eigen n ^ 2 := by
  have hrow_energy :
      ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖ ^ 2 =
        ∫ x, inner Real
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
          (S.mode n) ^ 2 ∂mu := by
    simpa using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  rw [← hrow_energy]
  have hdiag := S.diagonal_of_ne_zero (mu := mu) (hW := hW) hne
  have hnorm_mode : ‖S.mode n‖ = 1 := by
    simpa using S.nonzero_orthonormal.norm_eq_one ⟨n, hne⟩
  calc
    ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖ ^ 2
        = ‖S.eigen n • S.mode n‖ ^ 2 := by rw [hdiag]
    _ = S.eigen n ^ 2 := by
        rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs, sq_abs]

/-- Weighted row-coordinate integrals have the expected spectral moments.

This is the padded replacement for the unweighted identity.  When the listed
eigenvalue is zero, the weight is zero; when it is nonzero, the previous
lemma gives the coordinate-square integral. -/
theorem integral_graphon_row_weighted_inner_sq_eq_eigen_pow
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (k n : Nat) :
    (∫ x, S.eigen n ^ (k + 1) *
        (inner Real
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
          (S.mode n) ^ 2) ∂mu) =
      S.eigen n ^ (k + 3) := by
  by_cases hne : S.eigen n = 0
  · simp [hne]
  · rw [integral_const_mul]
    rw [S.integral_graphon_row_inner_sq_eq_eigen_sq_of_ne_zero
      (mu := mu) (hW := hW) hne]
    calc
      S.eigen n ^ (k + 1) * S.eigen n ^ 2 =
          S.eigen n ^ ((k + 1) + 2) := by rw [← pow_add]
      _ = S.eigen n ^ (k + 3) := rfl

/-- The row-coordinate quadratic expansion may be integrated term-by-term for
zero-padded compact-action data. -/
theorem hasSum_integral_graphon_row_weighted_inner_sq
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum
      (fun n : Nat =>
        ∫ x, S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2) ∂mu)
      (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))) ∂mu) := by
  let row : Omega -> Lp Real 2 mu :=
    fun x =>
      L2Kernel.goodL2 (mu := mu)
        (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  let coordSq : Nat -> Omega -> Real :=
    fun n x => inner Real (row x) (S.mode n) ^ 2
  let F : Nat -> Omega -> Real :=
    fun n x => S.eigen n ^ (k + 1) * coordSq n x
  let f : Omega -> Real :=
    fun x => inner Real (row x)
      (L2Kernel.clmIter (mu := mu)
        (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) (row x))
  have hcoord_integrable :
      ∀ n : Nat, Integrable (fun x : Omega => coordSq n x) mu := by
    intro n
    simpa [coordSq, row] using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  have hF_integrable : ∀ n : Nat, Integrable (F n) mu := by
    intro n
    exact (hcoord_integrable n).const_mul (S.eigen n ^ (k + 1))
  have hF_integral_norm_le :
      ∀ n : Nat, (∫ x, ‖F n x‖ ∂mu) <= S.eigen n ^ 2 := by
    intro n
    by_cases hn : S.eigen n = 0
    · simp [F, hn]
    · have hpow_abs : |S.eigen n ^ (k + 1)| <= 1 := by
        rw [abs_pow]
        exact pow_le_one₀
          (abs_nonneg (S.eigen n))
          (S.abs_eigen_le_one (mu := mu) (hW := hW) n)
      have hpoint :
          (fun x : Omega => ‖F n x‖) <= coordSq n := by
        intro x
        have hcoord_nonneg : 0 <= coordSq n x := sq_nonneg _
        calc
          ‖F n x‖ = |S.eigen n ^ (k + 1)| * coordSq n x := by
            simp [F, coordSq, Real.norm_eq_abs]
          _ <= 1 * coordSq n x := by
            exact mul_le_mul_of_nonneg_right hpow_abs hcoord_nonneg
          _ = coordSq n x := by rw [one_mul]
      calc
        (∫ x, ‖F n x‖ ∂mu) <= ∫ x, coordSq n x ∂mu := by
          exact integral_mono (hF_integrable n).norm (hcoord_integrable n) hpoint
        _ = S.eigen n ^ 2 := by
          simpa [coordSq, row] using
            S.integral_graphon_row_inner_sq_eq_eigen_sq_of_ne_zero
              (mu := mu) (hW := hW) hn
  have hF_integral_norm_summable :
      Summable fun n : Nat => ∫ x, ‖F n x‖ ∂mu := by
    refine (S.summable_square (mu := mu) (hW := hW)).of_norm_bounded ?_
    intro n
    have hnonneg : 0 <= ∫ x, ‖F n x‖ ∂mu :=
      integral_nonneg fun x => norm_nonneg (F n x)
    calc
      ‖∫ x, ‖F n x‖ ∂mu‖ = ∫ x, ‖F n x‖ ∂mu :=
        Real.norm_of_nonneg hnonneg
      _ <= S.eigen n ^ 2 := hF_integral_norm_le n
  have hseries :
      HasSum (fun n : Nat => ∫ x, F n x ∂mu)
        (∫ x, (∑' n : Nat, F n x) ∂mu) :=
    hasSum_integral_of_summable_integral_norm
      (F := F) hF_integrable hF_integral_norm_summable
  have htsum_fun : (fun x : Omega => ∑' n : Nat, F n x) = f := by
    funext x
    simpa [F, f, coordSq, row] using
      (S.graphon_row_quadratic_expansion_clmIter
        (mu := mu) (hW := hW) k x).tsum_eq
  rw [htsum_fun] at hseries
  simpa [F, f, coordSq, row] using hseries

/-- Trace moments are the corresponding countable eigenvalue moments for
zero-padded compact-action data. -/
theorem trace_compPow_hasSum_eigen_pow
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum (fun n : Nat => S.eigen n ^ (k + 3))
      (trace mu (compPow mu W (k + 2))) := by
  rw [L2Kernel.trace_compPow_eq_integral_row_inner_clmIter
    (mu := mu) (W := W) hW k]
  have hseries :=
    S.hasSum_integral_graphon_row_weighted_inner_sq
      (mu := mu) (hW := hW) k
  refine hseries.congr_fun ?_
  intro n
  symm
  exact S.integral_graphon_row_weighted_inner_sq_eq_eigen_pow
    (mu := mu) (hW := hW) k n

/-- Padded compact-action data give the graphon-facing bound trace package in
positive density. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9BoundTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.summable_square (mu := mu) (hW := hW)
  square_bound := S.square_bound (mu := mu) (hW := hW)
  trace_cube :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 0).tsum_eq.symm
  trace_ninth :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 6).tsum_eq.symm
  principal_ge_edge := S.principal_ge_edge_of_edgeDensity_pos hp

end C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag

namespace C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag

/-- Quadratic-form expansion derived from the padded action expansion. -/
theorem quadratic_expansion
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)
    (f : Lp Real 2 mu) :
    HasSum
      (fun n : Nat => S.eigen n * (inner Real f (S.mode n) ^ 2))
      (inner Real f ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :=
  quadratic_expansion_of_action_eigen_expansion
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.action_expansion f

/-- Every nonzero listed padded mode is a genuine eigenmode of the graphon
operator. -/
theorem diagonal_of_ne_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)
    {n : Nat} (hne : S.eigen n ≠ 0) :
    (L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n) =
      S.eigen n • S.mode n :=
  diagonal_of_padded_action_eigen_expansion
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.nonzero_orthonormal S.action_expansion n hne

/-- Quadratic-form expansion for every positive iterate of the canonical
graphon operator, in the direct-principal padded spectral interface. -/
theorem quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    ∀ k f, HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) * (inner Real f (S.mode n) ^ 2))
      (inner Real f
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f)) := by
  intro k f
  have hiter :=
    quadratic_expansion_iter_of_padded_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.nonzero_orthonormal S.action_expansion k f
  simpa [opIter_eq_l2_clmIter (mu := mu)
      (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) f] using hiter

/-- Applying the padded quadratic iterate expansion to an actual graphon row. -/
theorem graphon_row_quadratic_expansion_clmIter
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)
    (k : Nat) (x : Omega) :
    HasSum
      (fun n : Nat =>
        S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2))
      (inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)))) :=
  S.quadratic_expansion_clmIter (mu := mu) (hW := hW) k
    (L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))

/-- Finite initial square bounds for direct-principal padded core data. -/
theorem finite_square_bound
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    ∀ N : Nat,
      (Finset.range N).sum (fun n => S.eigen n ^ 2) <= edgeDensity W mu := by
  intro N
  classical
  let T := L2Kernel.kernelOpCLM (mu := mu) hW
  let row : Omega -> Lp Real 2 mu := fun x =>
    L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  let s : Finset Nat :=
    (Finset.range N).filter (fun n : Nat => S.eigen n ≠ 0)
  have hfilter :
      (Finset.range N).sum (fun n => S.eigen n ^ 2) =
        s.sum (fun n => S.eigen n ^ 2) := by
    symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    by_cases hn : S.eigen n = 0
    · simp [hn]
    · simp [hn]
  have hdiag_energy :
      s.sum (fun n => S.eigen n ^ 2) =
        s.sum (fun n => ‖T (S.mode n)‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hne : S.eigen n ≠ 0 := (Finset.mem_filter.mp hn).2
    have hdiag :
        T (S.mode n) = S.eigen n • S.mode n :=
      S.diagonal_of_ne_zero (mu := mu) (hW := hW) hne
    have hnorm_mode : ‖S.mode n‖ = 1 := by
      simpa using S.nonzero_orthonormal.norm_eq_one ⟨n, hne⟩
    calc
      S.eigen n ^ 2 = |S.eigen n| ^ 2 := by rw [sq_abs]
      _ = ‖S.eigen n • S.mode n‖ ^ 2 := by
        rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs]
      _ = ‖T (S.mode n)‖ ^ 2 := by rw [hdiag]
  have hrow_energy :
      s.sum (fun n => ‖T (S.mode n)‖ ^ 2) =
        ∫ x, s.sum
          (fun n : Nat => inner Real (row x) (S.mode n) ^ 2) ∂mu := by
    simpa [T, row, s] using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode s
  have hfinite_integrable :
      Integrable
        (fun x : Omega =>
          s.sum (fun n : Nat => inner Real (row x) (S.mode n) ^ 2)) mu := by
    simpa [row, s] using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode s
  have hrow_norm_integrable :
      Integrable (fun x : Omega => inner Real (row x) (row x)) mu := by
    simpa [row] using
      L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (goodK_of_isGraphon hW)
  have hpoint :
      ∀ x : Omega,
        s.sum (fun n : Nat => inner Real (row x) (S.mode n) ^ 2) <=
          inner Real (row x) (row x) := by
    intro x
    simpa [row, s] using
      sum_filter_ne_zero_inner_sq_le_self_of_padded_orthonormal
        (mode := S.mode) (eigen := S.eigen)
        S.nonzero_orthonormal (row x) (Finset.range N)
  calc
    (Finset.range N).sum (fun n => S.eigen n ^ 2)
        = s.sum (fun n => S.eigen n ^ 2) := hfilter
    _ = s.sum (fun n => ‖T (S.mode n)‖ ^ 2) := hdiag_energy
    _ = ∫ x, s.sum
          (fun n : Nat => inner Real (row x) (S.mode n) ^ 2) ∂mu := hrow_energy
    _ <= ∫ x, inner Real (row x) (row x) ∂mu := by
      exact integral_mono hfinite_integrable hrow_norm_integrable hpoint
    _ <= edgeDensity W mu := by
      rw [show (∫ x, inner Real (row x) (row x) ∂mu) =
          ∫ x, inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)) ∂mu by
        rfl]
      rw [L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
        (mu := mu) (goodK_of_isGraphon hW)]
      exact kernelSqNorm_le_edge hW

/-- Square summability and the infinite square bound follow from the finite
initial square bounds for direct-principal padded core data. -/
theorem summable_square_and_square_bound
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    Summable (fun n : Nat => S.eigen n ^ 2) ∧
      (∑' n : Nat, S.eigen n ^ 2) <= edgeDensity W mu :=
  summable_square_and_tsum_le_of_sum_range_square_le
    S.eigen (S.finite_square_bound (mu := mu) (hW := hW))

/-- Square summability for direct-principal padded core data. -/
theorem summable_square
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    Summable (fun n : Nat => S.eigen n ^ 2) :=
  (S.summable_square_and_square_bound (mu := mu) (hW := hW)).1

/-- Infinite square bound for direct-principal padded core data. -/
theorem square_bound
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    (∑' n : Nat, S.eigen n ^ 2) <= edgeDensity W mu :=
  (S.summable_square_and_square_bound (mu := mu) (hW := hW)).2

/-- Each listed padded eigenvalue is bounded by one in absolute value. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 := by
  intro n
  have hsq_le_edge :
      S.eigen n ^ 2 <= ∑' m : Nat, S.eigen m ^ 2 :=
    single_le_tsum_of_nonneg
      (S.summable_square (mu := mu) (hW := hW)) (fun m => sq_nonneg _) n
  have hsq_le_one :
      S.eigen n ^ 2 <= 1 :=
    hsq_le_edge.trans
      ((S.square_bound (mu := mu) (hW := hW)).trans (edgeDensity_le_one hW))
  exact (sq_le_one_iff_abs_le_one (S.eigen n)).mp hsq_le_one

/-- For a nonzero listed padded mode, the square row-coordinate integral is
the square of its eigenvalue. -/
theorem integral_graphon_row_inner_sq_eq_eigen_sq_of_ne_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)
    {n : Nat} (hne : S.eigen n ≠ 0) :
    (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (S.mode n) ^ 2 ∂mu) =
      S.eigen n ^ 2 := by
  have hrow_energy :
      ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖ ^ 2 =
        ∫ x, inner Real
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
          (S.mode n) ^ 2 ∂mu := by
    simpa using
      L2Kernel.sum_norm_kernelOpCLM_sq_eq_integral_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  rw [← hrow_energy]
  have hdiag := S.diagonal_of_ne_zero (mu := mu) (hW := hW) hne
  have hnorm_mode : ‖S.mode n‖ = 1 := by
    simpa using S.nonzero_orthonormal.norm_eq_one ⟨n, hne⟩
  calc
    ‖(L2Kernel.kernelOpCLM (mu := mu) hW) (S.mode n)‖ ^ 2
        = ‖S.eigen n • S.mode n‖ ^ 2 := by rw [hdiag]
    _ = S.eigen n ^ 2 := by
        rw [norm_smul, hnorm_mode, mul_one, Real.norm_eq_abs, sq_abs]

/-- Weighted row-coordinate integrals have the expected spectral moments. -/
theorem integral_graphon_row_weighted_inner_sq_eq_eigen_pow
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)
    (k n : Nat) :
    (∫ x, S.eigen n ^ (k + 1) *
        (inner Real
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
          (S.mode n) ^ 2) ∂mu) =
      S.eigen n ^ (k + 3) := by
  by_cases hne : S.eigen n = 0
  · simp [hne]
  · rw [integral_const_mul]
    rw [S.integral_graphon_row_inner_sq_eq_eigen_sq_of_ne_zero
      (mu := mu) (hW := hW) hne]
    calc
      S.eigen n ^ (k + 1) * S.eigen n ^ 2 =
          S.eigen n ^ ((k + 1) + 2) := by rw [← pow_add]
      _ = S.eigen n ^ (k + 3) := rfl

/-- The row-coordinate quadratic expansion may be integrated term-by-term for
direct-principal padded compact-action data. -/
theorem hasSum_integral_graphon_row_weighted_inner_sq
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum
      (fun n : Nat =>
        ∫ x, S.eigen n ^ (k + 1) *
          (inner Real
            (L2Kernel.goodL2 (mu := mu)
              (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
            (S.mode n) ^ 2) ∂mu)
      (∫ x, inner Real
        (L2Kernel.goodL2 (mu := mu)
          (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))
        (L2Kernel.clmIter (mu := mu)
          (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1)
          (L2Kernel.goodL2 (mu := mu)
            (L2Kernel.goodK_row (goodK_of_isGraphon hW) x))) ∂mu) := by
  let row : Omega -> Lp Real 2 mu :=
    fun x =>
      L2Kernel.goodL2 (mu := mu)
        (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  let coordSq : Nat -> Omega -> Real :=
    fun n x => inner Real (row x) (S.mode n) ^ 2
  let F : Nat -> Omega -> Real :=
    fun n x => S.eigen n ^ (k + 1) * coordSq n x
  let f : Omega -> Real :=
    fun x => inner Real (row x)
      (L2Kernel.clmIter (mu := mu)
        (L2Kernel.kernelOpCLM (mu := mu) hW) (k + 1) (row x))
  have hcoord_integrable :
      ∀ n : Nat, Integrable (fun x : Omega => coordSq n x) mu := by
    intro n
    simpa [coordSq, row] using
      L2Kernel.integrable_sum_graphon_row_inner_l2_sq
        (mu := mu) hW S.mode ({n} : Finset Nat)
  have hF_integrable : ∀ n : Nat, Integrable (F n) mu := by
    intro n
    exact (hcoord_integrable n).const_mul (S.eigen n ^ (k + 1))
  have hF_integral_norm_le :
      ∀ n : Nat, (∫ x, ‖F n x‖ ∂mu) <= S.eigen n ^ 2 := by
    intro n
    by_cases hn : S.eigen n = 0
    · simp [F, hn]
    · have hpow_abs : |S.eigen n ^ (k + 1)| <= 1 := by
        rw [abs_pow]
        exact pow_le_one₀
          (abs_nonneg (S.eigen n))
          (S.abs_eigen_le_one (mu := mu) (hW := hW) n)
      have hpoint :
          (fun x : Omega => ‖F n x‖) <= coordSq n := by
        intro x
        have hcoord_nonneg : 0 <= coordSq n x := sq_nonneg _
        calc
          ‖F n x‖ = |S.eigen n ^ (k + 1)| * coordSq n x := by
            simp [F, coordSq, Real.norm_eq_abs]
          _ <= 1 * coordSq n x := by
            exact mul_le_mul_of_nonneg_right hpow_abs hcoord_nonneg
          _ = coordSq n x := by rw [one_mul]
      calc
        (∫ x, ‖F n x‖ ∂mu) <= ∫ x, coordSq n x ∂mu := by
          exact integral_mono (hF_integrable n).norm (hcoord_integrable n) hpoint
        _ = S.eigen n ^ 2 := by
          simpa [coordSq, row] using
            S.integral_graphon_row_inner_sq_eq_eigen_sq_of_ne_zero
              (mu := mu) (hW := hW) hn
  have hF_integral_norm_summable :
      Summable fun n : Nat => ∫ x, ‖F n x‖ ∂mu := by
    refine (S.summable_square (mu := mu) (hW := hW)).of_norm_bounded ?_
    intro n
    have hnonneg : 0 <= ∫ x, ‖F n x‖ ∂mu :=
      integral_nonneg fun x => norm_nonneg (F n x)
    calc
      ‖∫ x, ‖F n x‖ ∂mu‖ = ∫ x, ‖F n x‖ ∂mu :=
        Real.norm_of_nonneg hnonneg
      _ <= S.eigen n ^ 2 := hF_integral_norm_le n
  have hseries :
      HasSum (fun n : Nat => ∫ x, F n x ∂mu)
        (∫ x, (∑' n : Nat, F n x) ∂mu) :=
    hasSum_integral_of_summable_integral_norm
      (F := F) hF_integrable hF_integral_norm_summable
  have htsum_fun : (fun x : Omega => ∑' n : Nat, F n x) = f := by
    funext x
    simpa [F, f, coordSq, row] using
      (S.graphon_row_quadratic_expansion_clmIter
        (mu := mu) (hW := hW) k x).tsum_eq
  rw [htsum_fun] at hseries
  simpa [F, f, coordSq, row] using hseries

/-- Trace moments are the corresponding countable eigenvalue moments for
direct-principal padded compact-action data. -/
theorem trace_compPow_hasSum_eigen_pow
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)
    (k : Nat) :
    HasSum (fun n : Nat => S.eigen n ^ (k + 3))
      (trace mu (compPow mu W (k + 2))) := by
  rw [L2Kernel.trace_compPow_eq_integral_row_inner_clmIter
    (mu := mu) (W := W) hW k]
  have hseries :=
    S.hasSum_integral_graphon_row_weighted_inner_sq
      (mu := mu) (hW := hW) k
  refine hseries.congr_fun ?_
  intro n
  symm
  exact S.integral_graphon_row_weighted_inner_sq_eq_eigen_pow
    (mu := mu) (hW := hW) k n

/-- Direct-principal padded compact-action data give the graphon-facing bound
trace package. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW) :
    C9BoundTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.summable_square (mu := mu) (hW := hW)
  square_bound := S.square_bound (mu := mu) (hW := hW)
  trace_cube :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 0).tsum_eq.symm
  trace_ninth :=
    (S.trace_compPow_hasSum_eigen_pow (mu := mu) (hW := hW) 6).tsum_eq.symm
  principal_ge_edge := S.principal_ge_edge

end C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag

namespace C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag

/-- Row-energy compact-action data imply the finite operator-energy no-trace
package by integrating finite Bessel inequalities over the graphon rows. -/
def toCompactActionEnergySpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionEnergySpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  finite_energy_bound :=
    finite_energy_bound_of_row_energy_identity
      (mu := mu) S.mode_orthonormal
      S.row_finite_integrable S.row_norm_integrable
      S.row_energy S.row_norm_bound

end C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag

namespace C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag

/-- Row-energy compact-action data imply the finite operator-energy package by
integrating finite Bessel inequalities over the graphon rows. -/
def toCompactActionEnergyTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  finite_energy_bound :=
    finite_energy_bound_of_row_energy_identity
      (mu := mu) S.mode_orthonormal
      S.row_finite_integrable S.row_norm_integrable
      S.row_energy S.row_norm_bound
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

/-- Row-energy compact-action data imply the finite square-bound package. -/
def toCompactActionFiniteBoundTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW :=
  S.toCompactActionEnergyTraceSpectralDataNoDiag.toCompactActionFiniteBoundTraceSpectralDataNoDiag

/-- Row-energy compact-action data imply the graphon-facing bound trace
package in positive density. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9BoundTraceSpectralData W mu :=
  S.toCompactActionEnergyTraceSpectralDataNoDiag.toBoundTraceSpectralData hp

end C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag

namespace C9CanonicalL2CompactActionGoodRowSpectralDataNoDiag

/-- Bounded-representative compact-action data give the row-energy no-trace
package with the actual graphon rows. -/
def toCompactActionRowEnergySpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionGoodRowSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag hW where
  mode := fun n => L2Kernel.goodL2 (mu := mu) (S.rep_good n)
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  row := fun x =>
    L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  row_finite_integrable := by
    intro N
    simpa using
      L2Kernel.integrable_sum_goodK_row_inner_sq
        (mu := mu) (goodK_of_isGraphon hW) S.rep_good
        (Finset.range N)
  row_norm_integrable := by
    simpa using
      L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (goodK_of_isGraphon hW)
  row_energy := by
    intro N
    have hsum :
        (Finset.range N).sum
            (fun n : Nat =>
              ‖(L2Kernel.kernelOpCLM (mu := mu) hW)
                (L2Kernel.goodL2 (mu := mu) (S.rep_good n))‖ ^ 2) =
          (Finset.range N).sum
            (fun n : Nat =>
              ‖L2Kernel.kernelOpL2OfGoodK (mu := mu)
                (goodK_of_isGraphon hW) (S.rep_good n)‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [L2Kernel.kernelOpCLM_goodL2 (mu := mu) hW (S.rep_good n)]
      rw [L2Kernel.kernelOpL2OfGood_eq_kernelOpL2OfGoodK (mu := mu) hW (S.rep_good n)]
    rw [hsum]
    simpa using
      L2Kernel.sum_norm_kernelOpL2OfGoodK_sq_eq_integral_sum_row_inner_sq
        (mu := mu) (goodK_of_isGraphon hW) S.rep_good
        (Finset.range N)
  row_norm_bound := by
    rw [L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
      (mu := mu) (goodK_of_isGraphon hW)]
    exact kernelSqNorm_le_edge hW

end C9CanonicalL2CompactActionGoodRowSpectralDataNoDiag

namespace C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag

/-- Bounded-representative compact-action data give the row-energy package
with the actual graphon rows.

This discharges the row integrability, row norm bound, and finite row-energy
identity from concrete `L2Kernel` lemmas.  What remains outside this conversion
is choosing bounded representatives for the spectral modes and proving the
cube/ninth trace identities. -/
def toCompactActionRowEnergyTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag hW) :
    C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag hW where
  mode := fun n => L2Kernel.goodL2 (mu := mu) (S.rep_good n)
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  row := fun x =>
    L2Kernel.goodL2 (mu := mu)
      (L2Kernel.goodK_row (goodK_of_isGraphon hW) x)
  row_finite_integrable := by
    intro N
    simpa using
      L2Kernel.integrable_sum_goodK_row_inner_sq
        (mu := mu) (goodK_of_isGraphon hW) S.rep_good
        (Finset.range N)
  row_norm_integrable := by
    simpa using
      L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (goodK_of_isGraphon hW)
  row_energy := by
    intro N
    have hsum :
        (Finset.range N).sum
            (fun n : Nat =>
              ‖(L2Kernel.kernelOpCLM (mu := mu) hW)
                (L2Kernel.goodL2 (mu := mu) (S.rep_good n))‖ ^ 2) =
          (Finset.range N).sum
            (fun n : Nat =>
              ‖L2Kernel.kernelOpL2OfGoodK (mu := mu)
                (goodK_of_isGraphon hW) (S.rep_good n)‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [L2Kernel.kernelOpCLM_goodL2 (mu := mu) hW (S.rep_good n)]
      rw [L2Kernel.kernelOpL2OfGood_eq_kernelOpL2OfGoodK (mu := mu) hW (S.rep_good n)]
    rw [hsum]
    simpa using
      L2Kernel.sum_norm_kernelOpL2OfGoodK_sq_eq_integral_sum_row_inner_sq
        (mu := mu) (goodK_of_isGraphon hW) S.rep_good
        (Finset.range N)
  row_norm_bound := by
    rw [L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
      (mu := mu) (goodK_of_isGraphon hW)]
    exact kernelSqNorm_le_edge hW
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

/-- Bounded-representative compact-action data imply the graphon-facing bound
trace package in positive density. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9BoundTraceSpectralData W mu :=
  S.toCompactActionRowEnergyTraceSpectralDataNoDiag.toBoundTraceSpectralData hp

end C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag

namespace C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag

/-- The eigenvalues listed in direct-`HasSum` no-diagonal compact-action
graphon data are bounded by one. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW) :
    ∀ n, |S.eigen n| <= 1 :=
  abs_eigen_le_one_of_graphon_action_expansion
    (mu := mu) (W := W) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- If the canonical graphon operator is compact, the eigenvalue list in
direct-`HasSum` no-diagonal compact-action data tends to zero. -/
theorem eigen_tendsto_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Filter.Tendsto S.eigen Filter.atTop (nhds 0) :=
  CompactSpectral.canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (mu := mu) hW hcompact S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- Every listed spectral value in direct-`HasSum` no-diagonal compact-action
data is an actual eigenvalue of the canonical graphon operator. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  hasEigenvalue_of_orthonormal_diagonal
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal
    (diagonal_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.mode_orthonormal S.action_expansion)

/-- In positive density, the top listed coefficient in direct-`HasSum`
no-diagonal compact-action data is nonnegative. -/
theorem principal_nonneg_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    0 <= S.eigen 0 := by
  have hquad :
      ∀ f : Lp Real 2 mu, HasSum
        (fun n : Nat => S.eigen n * (inner Real f (S.mode n) ^ 2))
        (inner Real f ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :=
    quadratic_expansion_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.action_expansion
  have hpos :
      0 <
        inner Real (L2Kernel.oneL2 (Omega := Omega) mu)
          ((L2Kernel.kernelOpCLM (mu := mu) hW)
            (L2Kernel.oneL2 (Omega := Omega) mu)) := by
    rw [L2Kernel.kernelOpCLM_one_eq_degreeL2 hW]
    simpa using L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW ▸ hp
  exact
    principal_nonneg_of_positive_quadratic_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      hquad S.principal_max hpos

/-- Cubic spectral summability follows from the square trace `HasSum` and the
graphon operator norm bound. -/
theorem summable_cube
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW) :
    Summable fun n : Nat => S.eigen n ^ 3 := by
  refine S.trace_square_hasSum.summable.of_norm_bounded ?_
  intro n
  exact abs_cube_le_sq_of_sq_le_one
    ((sq_le_one_iff_abs_le_one (S.eigen n)).mpr (S.abs_eigen_le_one n))

/-- Ninth spectral summability follows from the square trace `HasSum` and the
graphon operator norm bound. -/
theorem summable_ninth
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW) :
    Summable fun n : Nat => S.eigen n ^ 9 := by
  refine S.trace_square_hasSum.summable.of_norm_bounded ?_
  intro n
  exact abs_ninth_le_sq_of_sq_le_one
    ((sq_le_one_iff_abs_le_one (S.eigen n)).mpr (S.abs_eigen_le_one n))

/-- The negative ninth tail is summable for direct-`HasSum` no-diagonal
compact-action graphon data. -/
theorem summable_negative_ninth_tail
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW) :
    Summable fun n : Nat => max (-(S.eigen (n + 1) ^ 9)) 0 := by
  have hshift : Summable fun n : Nat => S.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.trace_square_hasSum.summable
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_ hshift
  intro n
  exact max_neg_ninth_le_sq_of_sq_le_one
    ((sq_le_one_iff_abs_le_one (S.eigen (n + 1))).mpr
      (S.abs_eigen_le_one (n + 1)))

/-- Convert the direct-`HasSum` trace package into the existing no-diagonal
compact-action package. -/
def toCompactActionTraceSpectralDataNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW) :
    C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  summable_square := S.trace_square_hasSum.summable
  trace_square := S.trace_square_hasSum.tsum_eq.symm
  trace_cube := S.trace_cube_hasSum.tsum_eq.symm
  trace_ninth := S.trace_ninth_hasSum.tsum_eq.symm

/-- Direct-`HasSum` no-diagonal data also give the signed compact-expansion
package in positive density. -/
def toCompactExpansionTraceSpectralData_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9CanonicalL2CompactExpansionTraceSpectralData hW :=
  S.toCompactActionTraceSpectralDataNoDiag
    |>.toCompactExpansionTraceSpectralData_of_edgeDensity_pos hp

/-- The vector-valued action expansion already forces coverage of every
nonzero eigenvalue, so the complete compact-action package has no extra
spectral-coverage hypothesis beyond the direct-`HasSum` no-diagonal package. -/
def toCompleteCompactActionTraceSpectralDataHasSumNoDiag
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW) :
    C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  trace_square_hasSum := S.trace_square_hasSum
  trace_cube_hasSum := S.trace_cube_hasSum
  trace_ninth_hasSum := S.trace_ninth_hasSum
  covers_nonzero_eigenvalues := by
    intro lambda hlambda hlambda0
    exact
      mem_range_eigen_of_hasEigenvalue_of_action_eigen_expansion
        (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
        S.mode_orthonormal S.action_expansion hlambda hlambda0

end C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag

namespace C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag

/-- Every listed spectral value in complete direct-`HasSum` compact-action
data is an actual eigenvalue of the canonical graphon operator.

Together with `covers_nonzero_eigenvalues`, this says the listed countable
sequence captures the nonzero point spectrum exactly, while still allowing an
infinite nonzero spectrum accumulating at zero. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  S.toC9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag.hasEigenvalue

/-- For a complete compact-action graphon spectral package, a nonzero real
number occurs in the listed eigenvalue sequence iff it is a genuine eigenvalue
of the canonical graphon operator.

This is the grounded countable-spectrum replacement for any finite-spectrum
intuition: the sequence may be infinite and zero-padded, but it covers exactly
the nonzero eigenvalues. -/
theorem mem_range_eigen_iff_hasEigenvalue_of_ne_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag hW)
    {lambda : Real} (hlambda : lambda ≠ 0) :
    lambda ∈ Set.range S.eigen ↔
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        lambda := by
  constructor
  · rintro ⟨n, hn⟩
    simpa [hn] using S.hasEigenvalue n
  · intro hlambda_eigen
    exact S.covers_nonzero_eigenvalues lambda hlambda_eigen hlambda

end C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag

namespace C9CanonicalL2CompactExpansionTraceSpectralData

/-- If the canonical graphon operator is compact, the eigenvalue list in
compact-expansion trace data tends to zero. -/
theorem eigen_tendsto_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactExpansionTraceSpectralData hW)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Filter.Tendsto S.eigen Filter.atTop (nhds 0) :=
  CompactSpectral.canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (mu := mu) hW hcompact S.mode_orthonormal S.diagonal

/-- Every listed spectral value in compact-expansion trace data is an actual
eigenvalue of the canonical graphon operator. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactExpansionTraceSpectralData hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  hasEigenvalue_of_orthonormal_diagonal
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal S.diagonal

/-- Convert compact-expansion trace data into the canonical Rayleigh package.
The Rayleigh bound is proved from the countable expansion and Bessel
inequality, not assumed as a standalone scalar fact. -/
def toCanonicalL2RayleighTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactExpansionTraceSpectralData hW) :
    C9CanonicalL2RayleighTraceSpectralData hW where
  eigen := S.eigen
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  rayleigh_le_principal :=
    rayleigh_le_principal_of_compact_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      (quadratic_expansion_of_action_eigen_expansion
        (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
        S.action_expansion)
      (summable_inner_sq_of_orthonormal S.mode_orthonormal)
      (tsum_inner_sq_le_self_of_orthonormal S.mode_orthonormal)
      S.principal_max S.principal_nonneg

end C9CanonicalL2CompactExpansionTraceSpectralData

namespace C9CanonicalL2CompactActionTraceSpectralData

/-- The eigenvalues listed in compact-action graphon data are bounded by one. -/
theorem abs_eigen_le_one
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralData hW) :
    ∀ n, |S.eigen n| <= 1 :=
  abs_eigen_le_one_of_graphon_action_expansion
    (mu := mu) (W := W) S.mode S.eigen
    S.mode_orthonormal S.action_expansion

/-- If the canonical graphon operator is compact, the eigenvalue list in
compact-action trace data tends to zero. -/
theorem eigen_tendsto_zero
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralData hW)
    (hcompact :
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)) :
    Filter.Tendsto S.eigen Filter.atTop (nhds 0) :=
  CompactSpectral.canonicalGraphonCompact_orthonormal_eigenvalues_tendsto_zero
    (mu := mu) hW hcompact S.mode_orthonormal S.diagonal

/-- Every listed spectral value in compact-action trace data is an actual
eigenvalue of the canonical graphon operator. -/
theorem hasEigenvalue
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralData hW) :
    ∀ n,
      Module.End.HasEigenvalue
        (L2Kernel.kernelOpCLM (mu := mu) hW).toLinearMap
        (S.eigen n) :=
  hasEigenvalue_of_orthonormal_diagonal
    (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
    S.mode_orthonormal S.diagonal

/-- In the graphon low band, positive edge density forces the top listed
compact spectral value to be nonnegative. -/
theorem principal_nonneg_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralData hW)
    (hp : 0 < edgeDensity W mu) :
    0 <= S.eigen 0 := by
  have hquad :
      ∀ f : Lp Real 2 mu, HasSum
        (fun n : Nat => S.eigen n * (inner Real f (S.mode n) ^ 2))
        (inner Real f ((L2Kernel.kernelOpCLM (mu := mu) hW) f)) :=
    quadratic_expansion_of_action_eigen_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      S.action_expansion
  have hpos :
      0 <
        inner Real (L2Kernel.oneL2 (Omega := Omega) mu)
          ((L2Kernel.kernelOpCLM (mu := mu) hW)
            (L2Kernel.oneL2 (Omega := Omega) mu)) := by
    rw [L2Kernel.kernelOpCLM_one_eq_degreeL2 hW]
    simpa using L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW ▸ hp
  exact
    principal_nonneg_of_positive_quadratic_expansion
      (L2Kernel.kernelOpCLM (mu := mu) hW) S.mode S.eigen
      hquad S.principal_max hpos

/-- Add the top-eigenvalue sign field to compact-action data using positive
edge density. -/
def toCompactExpansionTraceSpectralData_of_edgeDensity_pos
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralData hW)
    (hp : 0 < edgeDensity W mu) :
    C9CanonicalL2CompactExpansionTraceSpectralData hW where
  mode := S.mode
  eigen := S.eigen
  mode_orthonormal := S.mode_orthonormal
  diagonal := S.diagonal
  principal_nonneg := S.principal_nonneg_of_edgeDensity_pos hp
  principal_max := S.principal_max
  action_expansion := S.action_expansion
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth

end C9CanonicalL2CompactActionTraceSpectralData

namespace C9L2RayleighTraceSpectralData

/-- The Rayleigh quotient of the graphon operator at the constant-one vector is
the graphon edge density, provided the operator sends `1` to the degree
function. -/
theorem rayleigh_oneL2_eq_edgeDensity
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9L2RayleighTraceSpectralData hW) :
    S.operator.rayleighQuotient (L2Kernel.oneL2 (Omega := Omega) mu) =
      edgeDensity W mu := by
  have hnum :
      S.operator.reApplyInnerSelf (L2Kernel.oneL2 (Omega := Omega) mu) =
        edgeDensity W mu := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, S.maps_one]
    simpa [real_inner_comm] using
      (L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW)
  rw [ContinuousLinearMap.rayleighQuotient, hnum,
    L2Kernel.norm_oneL2_sq]
  ring

/-- The principal Rayleigh bound follows directly by evaluating the Rayleigh
bound at the constant-one vector. -/
theorem principal_ge_edge
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9L2RayleighTraceSpectralData hW) :
    edgeDensity W mu <= S.eigen 0 := by
  rw [← S.rayleigh_oneL2_eq_edgeDensity]
  exact S.rayleigh_le_principal
    (L2Kernel.oneL2 (Omega := Omega) mu)
    (L2Kernel.oneL2_ne_zero (Omega := Omega) (mu := mu))

/-- Convert the Rayleigh-form operator package into the quadratic-form package
used by the C9 assembly. -/
def toL2OperatorTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9L2RayleighTraceSpectralData hW) :
    C9L2OperatorTraceSpectralData hW where
  operator := S.operator
  eigen := S.eigen
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  maps_one := S.maps_one
  quadratic_le_principal :=
    quadratic_le_principal_of_rayleigh_le S.operator S.rayleigh_le_principal

/-- Forget the explicit Rayleigh-form operator once its principal Rayleigh
consequence has been proved. -/
def toRawTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9L2RayleighTraceSpectralData hW) :
    C9RawTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  principal_ge_edge := S.principal_ge_edge

end C9L2RayleighTraceSpectralData

namespace C9L2OperatorTraceSpectralData

/-- The principal Rayleigh bound follows from the L² graphon identities and
quadratic-form domination. -/
theorem principal_ge_edge
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9L2OperatorTraceSpectralData hW) :
    edgeDensity W mu <= S.eigen 0 := by
  have hquad :=
    S.quadratic_le_principal (L2Kernel.oneL2 (Omega := Omega) mu)
  rw [S.maps_one,
    L2Kernel.inner_oneL2_degreeL2_eq_edgeDensity hW,
    L2Kernel.inner_oneL2_oneL2] at hquad
  simpa using hquad

/-- Forget the explicit L² operator once its Rayleigh consequence has been
proved. -/
def toRawTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9L2OperatorTraceSpectralData hW) :
    C9RawTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.summable_square
  trace_square := S.trace_square
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  principal_ge_edge := S.principal_ge_edge

end C9L2OperatorTraceSpectralData

namespace C9TraceSpectralData

/-- Convert trace spectral data into the C9 data used by the low-band proof.

The only extra input is `IsGraphon W mu`, used to prove the square bound from
the square trace identity. -/
def toC9SpectralData
    [IsProbabilityMeasure mu]
    (S : C9TraceSpectralData W mu) (hW : IsGraphon W mu) :
    C9SpectralData W mu where
  expansion := S.expansion
  summable_square := S.summable_square
  summable_cube := S.summable_cube
  trace_cube := S.trace_cube
  square_bound := by
    rw [← S.trace_square]
    exact trace_compPow_one_le_edge hW
  principal_ge_edge := S.principal_ge_edge

end C9TraceSpectralData

namespace C9HasSumTraceSpectralData

/-- Direct `HasSum` trace data imply the raw countable trace-data interface.

This conversion only changes the representation of trace identities from
`HasSum` to `tsum`; it keeps the same countable eigenvalue sequence and the
same principal lower bound. -/
def toRawTraceSpectralData
    (S : C9HasSumTraceSpectralData W mu) :
    C9RawTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.trace_square_hasSum.summable
  trace_square := S.trace_square_hasSum.tsum_eq.symm
  trace_cube := S.trace_cube_hasSum.tsum_eq.symm
  trace_ninth := S.trace_ninth_hasSum.tsum_eq.symm
  principal_ge_edge := S.principal_ge_edge

end C9HasSumTraceSpectralData

namespace C9BoundTraceSpectralData

/-- Bound trace data are exactly enough to build the spectral package used by
the C9 low-band scalar argument.

Higher-power summability follows from square summability plus
`∑ λ_n^2 <= edgeDensity W μ <= 1`; no square trace identity is used. -/
def toC9SpectralData
    [IsProbabilityMeasure mu]
    (S : C9BoundTraceSpectralData W mu) (hW : IsGraphon W mu) :
    C9SpectralData W mu :=
  let hsq_le_one : (∑' n : Nat, S.eigen n ^ 2) <= 1 :=
    S.square_bound.trans (edgeDensity_le_one hW)
  {
    expansion := {
      eigen := S.eigen
      summable_ninth :=
        summable_ninth_of_summable_square_of_tsum_le_one
          S.summable_square hsq_le_one
      summable_negative_ninth_tail :=
        summable_negative_ninth_tail_of_summable_square_of_tsum_le_one
          S.summable_square hsq_le_one
      trace_ninth := S.trace_ninth
    }
    summable_square := S.summable_square
    summable_cube :=
      summable_cube_of_summable_square_of_tsum_le_one
        S.summable_square hsq_le_one
    trace_cube := S.trace_cube
    square_bound := S.square_bound
    principal_ge_edge := S.principal_ge_edge
  }

end C9BoundTraceSpectralData

namespace C9RawTraceSpectralData

/-- Raw trace data imply bound trace data by applying the elementary graphon
two-cycle bound to the square trace identity. -/
def toBoundTraceSpectralData
    [IsProbabilityMeasure mu]
    (S : C9RawTraceSpectralData W mu) (hW : IsGraphon W mu) :
    C9BoundTraceSpectralData W mu where
  eigen := S.eigen
  summable_square := S.summable_square
  square_bound := by
    rw [← S.trace_square]
    exact trace_compPow_one_le_edge hW
  trace_cube := S.trace_cube
  trace_ninth := S.trace_ninth
  principal_ge_edge := S.principal_ge_edge

/-- Convert raw trace data into the trace spectral data used by C9. -/
def toC9TraceSpectralData
    [IsProbabilityMeasure mu]
    (S : C9RawTraceSpectralData W mu) (hW : IsGraphon W mu) :
    C9TraceSpectralData W mu :=
  let hsq_le_one : (∑' n : Nat, S.eigen n ^ 2) <= 1 := by
    have hsq_le_edge : (∑' n : Nat, S.eigen n ^ 2) <= edgeDensity W mu := by
      rw [← S.trace_square]
      exact trace_compPow_one_le_edge hW
    exact hsq_le_edge.trans (edgeDensity_le_one hW)
  {
    expansion := {
      eigen := S.eigen
      summable_ninth :=
        summable_ninth_of_summable_square_of_tsum_le_one
          S.summable_square hsq_le_one
      summable_negative_ninth_tail :=
        summable_negative_ninth_tail_of_summable_square_of_tsum_le_one
          S.summable_square hsq_le_one
      trace_ninth := S.trace_ninth
    }
    summable_square := S.summable_square
    summable_cube :=
      summable_cube_of_summable_square_of_tsum_le_one
        S.summable_square hsq_le_one
    trace_square := S.trace_square
    trace_cube := S.trace_cube
    principal_ge_edge := S.principal_ge_edge
  }

end C9RawTraceSpectralData

/-!
## Legacy graphon wrapper interfaces

The preferred C9 assembly path now uses pointwise graphon statements such as
`c9GraphonBoundTraceSpectralData_lowBand`.  The following `For`/`Theorem`
propositions are retained as legacy adapters for exploratory spectral routes
inside this file; they should not be the public interface used by
`Conditional.lean`.
-/

/-- The standard graphon Hilbert-Schmidt spectral package needed for C9.

This packages the missing operator-theoretic construction: for every graphon,
the associated compact self-adjoint integral operator admits countable
eigenvalue data with the square bound, Rayleigh principal bound, and cube/ninth
trace identities used above.  It deliberately does not pass through a
finite-rank or finite-nonzero-eigenvalue claim.  It is stated as a `Prop` so it
can be assumed as a single standard theorem or later proved from Mathlib
operator theory. -/
def C9GraphonSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    Nonempty (C9SpectralData W mu)

/-- The countable graphon spectral-data package for one fixed graphon. -/
def C9GraphonSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  IsGraphon W mu ->
  Nonempty (C9SpectralData W mu)

/-- The sharper graphon spectral trace package for one fixed graphon.

This asks the Hilbert/operator layer for trace identities, not for the
graphon square-bound inequality. -/
def C9GraphonSpectralTraceDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  IsGraphon W mu ->
  Nonempty (C9TraceSpectralData W mu)

/-- The raw graphon spectral trace package for one fixed graphon.

This is the smallest current graphon-facing spectral input: the operator layer
supplies square summability, square/cube/ninth trace identities, and the
principal Rayleigh bound.  Lean derives the higher-power summability and the
square bound. -/
def C9GraphonRawTraceSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  IsGraphon W mu ->
  Nonempty (C9RawTraceSpectralData W mu)

/-- Raw trace spectral data for the C9 low band only.

This is the spectral input actually consumed by the all-density C9 assembly:
outside `1 / 2 < edgeDensity W μ <= 1003 / 2000`, the existing trivial and
path-density arguments already close the theorem. -/
def C9GraphonRawTraceSpectralDataForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  IsGraphon W mu ->
  1 / 2 < edgeDensity W mu ->
  edgeDensity W mu <= 1003 / 2000 ->
  Nonempty (C9RawTraceSpectralData W mu)

/-- Bound trace spectral data for the C9 low band only.

This is weaker than raw trace data: the square trace identity is replaced by
the square bound `∑ λ_n^2 <= edgeDensity W μ`. -/
def C9GraphonBoundTraceSpectralDataForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  IsGraphon W mu ->
  1 / 2 < edgeDensity W mu ->
  edgeDensity W mu <= 1003 / 2000 ->
  Nonempty (C9BoundTraceSpectralData W mu)

/-- Direct-`HasSum` trace data for one fixed graphon.

This is the leanest graphon-facing spectral package currently used by C9:
countably many spectral values, direct convergence/value statements for the
square/cube/ninth traces, and the principal lower bound. -/
def C9GraphonHasSumTraceSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  IsGraphon W mu ->
  Nonempty (C9HasSumTraceSpectralData W mu)

/-- The graphon spectral package with an explicit `L²` operator model for one
fixed graphon.

This is stronger than `C9GraphonRawTraceSpectralDataFor`: the principal bound
is obtained from a Rayleigh/quadratic-form inequality for the operator and the
proved identity `⟪1, T 1⟫ = edgeDensity`. -/
def C9GraphonL2OperatorTraceSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    Nonempty (C9L2OperatorTraceSpectralData hW)

/-- The graphon spectral package with an explicit `L²` operator and the
standard Rayleigh quotient bound.  This is stronger than
`C9GraphonL2OperatorTraceSpectralDataFor`; the quadratic-form domination used
there is derived from the Rayleigh bound. -/
def C9GraphonL2RayleighTraceSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    Nonempty (C9L2RayleighTraceSpectralData hW)

/-- The graphon spectral package for the canonical `L²` graphon operator.
The operator itself is `L2Kernel.kernelOpCLM hW`, and `T 1 = degree` is proved
rather than assumed. -/
def C9GraphonCanonicalL2RayleighTraceSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    Nonempty (C9CanonicalL2RayleighTraceSpectralData hW)

/-- The graphon spectral package for the canonical `L²` graphon operator,
stated as an ordered countable Hilbert eigenbasis.  This avoids any finite
non-zero spectrum assumption while deriving the principal Rayleigh bound from
Hilbert-space series identities. -/
def C9GraphonCanonicalL2HilbertTraceSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    Nonempty (C9CanonicalL2HilbertTraceSpectralData hW)

/-- The graphon spectral package for the canonical `L²` graphon operator in
compact-expansion form.  This is intended as the most faithful current target:
countably many compact spectral modes are listed, while no countable basis for
the whole ambient `L²` space is assumed. -/
def C9GraphonCanonicalL2CompactExpansionTraceSpectralDataFor
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    Nonempty (C9CanonicalL2CompactExpansionTraceSpectralData hW)

/-- The no-sign compact-action spectral package needed only on the C9 low
band.  The sign of the top eigenvalue is derived from `edgeDensity W μ > 0`
inside the C9 assembly. -/
def C9GraphonCanonicalL2CompactActionTraceSpectralDataForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionTraceSpectralData hW)

/-- The low-band compact-action spectral package without an explicit diagonal
field.  Diagonal action follows from the action expansion and orthonormality. -/
def C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)

/-- Low-band compact-action spectral data with no diagonal field and only the
square bound, not the square trace identity. -/
def C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW)

/-- Low-band compact-action spectral data with a square bound and no
cube/ninth trace assumptions.  Those trace identities are derived from the
action expansion by the row-coordinate integration theorem above. -/
def C9GraphonCanonicalL2CompactActionBoundSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW)

/-- Low-band compact-action finite-bound spectral data with no cube/ninth
trace assumptions. -/
def C9GraphonCanonicalL2CompactActionFiniteBoundSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionFiniteBoundSpectralDataNoDiag hW)

/-- Low-band compact-action finite-energy spectral data with no cube/ninth
trace assumptions. -/
def C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionEnergySpectralDataNoDiag hW)

/-- Low-band compact-action row-energy spectral data with no cube/ninth trace
assumptions. -/
def C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag hW)

/-- Low-band pure compact-action spectral data with no cube/ninth trace
assumptions and no row/repr fields. -/
def C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionCoreSpectralDataNoDiag hW)

/-- Low-band padded pure compact-action spectral data.

Unlike `C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagForSpectral`,
this allows zero padding and is therefore compatible with finite spectra and
finite-dimensional graphon `L²` spaces. -/
def C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)

/-- Low-band padded pure compact-action spectral data with the principal
Rayleigh lower bound stated directly, rather than as a sorted-eigenvalue
condition. -/
def C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)

/-- Low-band Hilbert-basis nonzero spectral-subspace data.

This is one step closer to the compact self-adjoint theorem than the padded
C9 interface: the padded action expansion is derived from a Hilbert basis of
the nonzero spectral subspace and the fact that the canonical operator maps
into that subspace. -/
def C9GraphonCanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag hW)

/-- Low-band Hilbert-basis spectral data for the canonical zero-orthogonal
subspace `(eigenspace T 0)ᗮ`. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag hW)

/-- Low-band lean eigenbasis data for the canonical zero-orthogonal subspace
`(eigenspace T 0)ᗮ`. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag hW)

/-- Low-band lean eigenbasis data for the canonical zero-orthogonal subspace,
with direct principal Rayleigh lower bound instead of global eigenvalue
ordering. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
        hW)

/-- Low-band dense countable orthonormal eigenmode data for the canonical
zero-orthogonal subspace, with direct principal Rayleigh lower bound. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
        hW)

/-- Low-band dense countable orthonormal eigenmode data for the canonical
zero-orthogonal subspace, with a Rayleigh domination theorem. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
        hW)

/-- Low-band dense countable orthonormal eigenmode data for the canonical
zero-orthogonal subspace, with principal value equal to the operator norm. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty
      (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag
        hW)

/-- Low-band compact-action good-row spectral data with no cube/ninth trace
assumptions. -/
def C9GraphonCanonicalL2CompactActionGoodRowSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionGoodRowSpectralDataNoDiag hW)

/-- Low-band compact-action spectral data with finite initial-segment square
bounds instead of an infinite square summability/bound field. -/
def C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW)

/-- The low-band compact-action spectral package whose square side is stated
as finite operator-energy estimates for the canonical graphon operator.

This is one step closer to the Hilbert-Schmidt kernel theorem than the
finite-square-bound package: Lean derives the finite eigenvalue-square bound
from this energy bound. -/
def C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW)

/-- The low-band compact-action spectral package whose finite energy estimate
is supplied by row-wise Hilbert-Schmidt identities. -/
def C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag hW)

/-- The low-band compact-action spectral package with bounded representatives
for the listed modes.  Row-energy fields are derived from concrete graphon
rows. -/
def C9GraphonCanonicalL2CompactActionGoodRowTraceSpectralDataNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag hW)

/-- The low-band compact-action spectral package with the trace identities
stated directly as `HasSum`s. -/
def C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW)

/-- The low-band complete compact-action spectral package with direct
`HasSum` trace identities.

Compared with
`C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral`,
this also requires that the listed sequence covers every nonzero eigenvalue of
the canonical graphon operator.  This is closer to the actual compact spectral
theorem and still makes no finite-spectrum assertion. -/
def C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagForSpectral
    (W : Omega -> Omega -> Real) (mu : Measure Omega)
    [IsProbabilityMeasure mu] : Prop :=
  ∀ hW : IsGraphon W mu,
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag hW)

/-- The sharper graphon Hilbert-Schmidt spectral trace theorem needed for C9.

This is now the preferred statement of the remaining operator-theoretic gap:
it asks for countable spectral trace identities and the principal Rayleigh
bound, while the square bound is derived separately from graphon boundedness. -/
def C9GraphonSpectralTraceDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    Nonempty (C9TraceSpectralData W mu)

/-- The raw graphon Hilbert-Schmidt spectral trace theorem needed for C9.

This is now the preferred statement of the remaining operator-theoretic gap:
prove the square/cube/ninth trace identities for a countable eigenvalue
sequence, square summability, and the principal Rayleigh bound. -/
def C9GraphonRawTraceSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    Nonempty (C9RawTraceSpectralData W mu)

/-- Global low-band raw graphon Hilbert-Schmidt spectral trace theorem needed
for C9.

This is weaker than `C9GraphonRawTraceSpectralDataTheorem`: it asks for the
trace/eigenvalue package only in the density band where the spectral C9
argument is used. -/
def C9GraphonRawTraceSpectralDataSpectralTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9RawTraceSpectralData W mu)

/-- Global low-band bound graphon spectral theorem needed for C9.

Compared with `C9GraphonRawTraceSpectralDataSpectralTheorem`, this removes the
square trace identity from the external theorem statement. -/
def C9GraphonBoundTraceSpectralDataSpectralTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    1 / 2 < edgeDensity W mu ->
    edgeDensity W mu <= 1003 / 2000 ->
    Nonempty (C9BoundTraceSpectralData W mu)

/-- Global minimal direct-`HasSum` graphon spectral theorem needed for C9.

It asks only for the trace series and the principal lower bound that the
countable low-band proof consumes; in particular it has no finite-spectrum
or global eigenvalue-ordering assertion. -/
def C9GraphonHasSumTraceSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    IsGraphon W mu ->
    Nonempty (C9HasSumTraceSpectralData W mu)

/-- Global graphon spectral theorem stated with an explicit `L²` operator
model.  Proving this implies the raw trace-data theorem without assuming the
principal Rayleigh bound as a black-box scalar field. -/
def C9GraphonL2OperatorTraceSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty (C9L2OperatorTraceSpectralData hW)

/-- Global graphon spectral theorem stated with the standard Rayleigh quotient
bound for the explicit `L²` operator. -/
def C9GraphonL2RayleighTraceSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty (C9L2RayleighTraceSpectralData hW)

/-- Global graphon spectral theorem stated for the canonical `L²` graphon
operator. -/
def C9GraphonCanonicalL2RayleighTraceSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty (C9CanonicalL2RayleighTraceSpectralData hW)

/-- Global graphon spectral theorem stated as an ordered countable Hilbert
eigenbasis for the canonical `L²` graphon operator. -/
def C9GraphonCanonicalL2HilbertTraceSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty (C9CanonicalL2HilbertTraceSpectralData hW)

/-- Global graphon spectral theorem stated as a compact expansion for the
canonical `L²` graphon operator, without requiring separability of the whole
ambient Hilbert space. -/
def C9GraphonCanonicalL2CompactExpansionTraceSpectralDataTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty (C9CanonicalL2CompactExpansionTraceSpectralData hW)

/-- Global pure compact-action spectral theorem.

This is the clean remaining Hilbert-space target for the no-trace C9 route:
for every graphon, the completed `L²` graphon operator has a countable
orthonormal action expansion.  No density-band, trace, row-energy, or
bounded-representative assumptions are included here. -/
def C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty (C9CanonicalL2CompactActionCoreSpectralDataNoDiag hW)

/-- Global padded pure compact-action spectral theorem.

This is the corrected global target for compact graphon operators.  It permits
zero padding of the eigenvalue sequence, so finite-spectrum graphons are not
excluded by the statement. -/
def C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty (C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)

/-- Global dense countable orthonormal eigenmode theorem for the canonical
zero-orthogonal subspace, with Rayleigh domination.

This is the current clean compact-spectral target below C9: construct a
countable orthonormal family of nonzero eigenmodes spanning `(ker T)ᗮ`, and
prove that the first listed eigenvalue dominates every Rayleigh quotient. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
          hW)

/-- Global dense countable orthonormal eigenmode theorem for the canonical
zero-orthogonal subspace, with principal value equal to the operator norm. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag
          hW)

/-- Global low-band no-sign compact-action spectral theorem for the canonical
`L²` graphon operator. -/
def C9GraphonCanonicalL2CompactActionTraceSpectralDataSpectralTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionTraceSpectralData hW)

/-- Global low-band compact-action spectral theorem without an explicit
diagonal field. -/
def C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagSpectralTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)

/-- Global low-band compact-action bound theorem without an explicit diagonal
field. -/
def C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionBoundTraceSpectralDataNoDiag hW)

/-- Global low-band compact-action bound theorem without cube/ninth trace
assumptions.  The trace identities are derived from the action expansion. -/
def C9GraphonCanonicalL2CompactActionBoundSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionBoundSpectralDataNoDiag hW)

/-- Global low-band compact-action finite-bound theorem without cube/ninth
trace assumptions. -/
def C9GraphonCanonicalL2CompactActionFiniteBoundSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionFiniteBoundSpectralDataNoDiag hW)

/-- Global low-band compact-action finite-energy theorem without cube/ninth
trace assumptions. -/
def C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionEnergySpectralDataNoDiag hW)

/-- Global low-band compact-action row-energy theorem without cube/ninth trace
assumptions. -/
def C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag hW)

/-- Global low-band pure compact-action theorem without cube/ninth trace,
row-energy, or bounded-representative assumptions. -/
def C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionCoreSpectralDataNoDiag hW)

/-- Global low-band padded pure compact-action theorem. -/
def C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag hW)

/-- Global low-band padded pure compact-action theorem with the principal
Rayleigh lower bound stated directly. -/
def C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiag hW)

/-- Global low-band Hilbert-basis nonzero spectral-subspace theorem. -/
def C9GraphonCanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiag hW)

/-- Global low-band Hilbert-basis theorem for the canonical zero-orthogonal
subspace `(eigenspace T 0)ᗮ`. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiag hW)

/-- Global low-band lean eigenbasis theorem for the canonical zero-orthogonal
subspace `(eigenspace T 0)ᗮ`. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiag hW)

/-- Global low-band lean eigenbasis theorem for the canonical zero-orthogonal
subspace, with direct principal Rayleigh lower bound. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiag
          hW)

/-- Global low-band dense countable orthonormal eigenmode theorem for the
canonical zero-orthogonal subspace, with direct principal Rayleigh lower
bound. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag
          hW)

/-- Low-band compactness theorem for the canonical graphon `L²` operator. -/
def C9GraphonCanonicalL2CompactSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW)

/-- Low-band finite-rank Hilbert-Schmidt approximation theorem for the
canonical graphon kernel.  This is a measure-theoretic approximation input,
not a finite-spectrum assumption about the limiting graphon operator. -/
def C9GraphonHilbertSchmidtFiniteRankApproxSpectralTheorem :
    Prop :=
  ∀ {Omega : Type u} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      CompactSpectral.GraphonHilbertSchmidtFiniteRankApproxFor
        (mu := mu) hW

/-- The low-band finite-rank Hilbert-Schmidt approximation input is now proved
for every graphon.  The low-band hypotheses are unused here; they are kept only
to match the C9 pipeline interface. -/
theorem C9GraphonHilbertSchmidtFiniteRankApproxSpectralTheorem.proved :
    C9GraphonHilbertSchmidtFiniteRankApproxSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW _hgt _hle
  exact CompactSpectral.graphonHilbertSchmidtFiniteRankApproxFor
    (mu := mu) hW

/-- Low-band finite-rank Hilbert-Schmidt approximation data imply the compact
canonical graphon-operator input used by the C9 spectral pipeline. -/
theorem C9GraphonCanonicalL2CompactSpectralTheorem.of_hilbertSchmidt_finiteRank_approx
    (happrox : C9GraphonHilbertSchmidtFiniteRankApproxSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    CompactSpectral.canonicalGraphonCompact_of_hilbertSchmidtFiniteRankApproxFor
      (mu := mu) hW (happrox hW hgt hle)

/-- The canonical graphon `L²` operator is compact in the C9 low band.  This is
now a theorem, not a conditional input, because graphon kernels have exact
finite-rank Hilbert-Schmidt approximants. -/
theorem C9GraphonCanonicalL2CompactSpectralTheorem.proved :
    C9GraphonCanonicalL2CompactSpectralTheorem.{u} :=
  C9GraphonCanonicalL2CompactSpectralTheorem.of_hilbertSchmidt_finiteRank_approx
    C9GraphonHilbertSchmidtFiniteRankApproxSpectralTheorem.proved

/-- Low-band analytic endpoint theorem: the canonical graphon operator is
compact, and its positive norm is an eigenvalue.

Together with the compact self-adjoint eigenspace decomposition already proved
in this file, this is the remaining operator-theoretic input needed to build
the principal-bound spectral data. -/
def C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) ∧
        Module.End.HasEigenvalue
          (L2Kernel.kernelOpCLM (mu := mu) hW :
            Module.End Real (Lp Real 2 mu))
          ‖L2Kernel.kernelOpCLM (mu := mu) hW‖

/-- Global low-band dense countable orthonormal eigenmode theorem for the
canonical zero-orthogonal subspace, with Rayleigh domination. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiag
          hW)

/-- Global low-band dense countable orthonormal eigenmode theorem for the
canonical zero-orthogonal subspace, with principal value equal to the operator
norm. -/
def C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty
        (C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiag
          hW)

/-- Global low-band compact-action good-row theorem without cube/ninth trace
assumptions. -/
def C9GraphonCanonicalL2CompactActionGoodRowSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionGoodRowSpectralDataNoDiag hW)

/-- Global low-band compact-action finite-bound theorem without an explicit
diagonal field. -/
def C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiag hW)

/-- Global low-band compact-action energy theorem without an explicit diagonal
field.  The finite eigenvalue-square bound is derived from its finite
operator-energy estimates. -/
def C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag hW)

/-- Global low-band compact-action row-energy theorem without an explicit
diagonal field.  Finite operator-energy estimates are derived from its
row-wise Hilbert-Schmidt representation. -/
def C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag hW)

/-- Global low-band compact-action theorem with bounded representatives for
the listed modes. -/
def C9GraphonCanonicalL2CompactActionGoodRowTraceSpectralDataNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag hW)

/-- Global low-band compact-action spectral theorem with the trace identities
stated directly as `HasSum`s. -/
def C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagSpectralTheorem : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW)

/-- Global low-band complete compact-action spectral theorem with direct
`HasSum` trace identities and coverage of all nonzero eigenvalues. -/
def C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagSpectralTheorem :
    Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W : Omega -> Omega -> Real},
    ∀ hW : IsGraphon W mu,
      1 / 2 < edgeDensity W mu ->
      edgeDensity W mu <= 1003 / 2000 ->
      Nonempty (C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag hW)

/-- Raw trace spectral data imply the trace-data interface. -/
theorem C9GraphonSpectralTraceDataFor.of_raw
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonRawTraceSpectralDataFor W mu) :
    C9GraphonSpectralTraceDataFor W mu := by
  intro hW
  exact ⟨(Classical.choice (hspec hW)).toC9TraceSpectralData hW⟩

/-- Explicit `L²` operator trace data imply the raw trace-data interface. -/
theorem C9GraphonRawTraceSpectralDataFor.of_l2_operator
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonL2OperatorTraceSpectralDataFor W mu) :
    C9GraphonRawTraceSpectralDataFor W mu := by
  intro hW
  exact ⟨(Classical.choice (hspec hW)).toRawTraceSpectralData⟩

/-- Direct-`HasSum` trace data imply the raw trace-data interface. -/
theorem C9GraphonRawTraceSpectralDataFor.of_hasSum_trace
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonHasSumTraceSpectralDataFor W mu) :
    C9GraphonRawTraceSpectralDataFor W mu := by
  intro hW
  exact ⟨(Classical.choice (hspec hW)).toRawTraceSpectralData⟩

/-- Raw low-band trace data imply the weaker bound low-band trace package. -/
theorem C9GraphonBoundTraceSpectralDataForSpectral.of_raw
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonRawTraceSpectralDataForSpectral W mu) :
    C9GraphonBoundTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  exact ⟨(Classical.choice (hspec hW hgt hle)).toBoundTraceSpectralData hW⟩

/-- Rayleigh-form `L²` operator trace data imply the quadratic-form operator
trace-data interface. -/
theorem C9GraphonL2OperatorTraceSpectralDataFor.of_l2_rayleigh
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonL2RayleighTraceSpectralDataFor W mu) :
    C9GraphonL2OperatorTraceSpectralDataFor W mu := by
  intro hW
  exact ⟨(Classical.choice (hspec hW)).toL2OperatorTraceSpectralData⟩

/-- Canonical-operator Rayleigh trace data imply the explicit-operator
Rayleigh trace-data interface. -/
theorem C9GraphonL2RayleighTraceSpectralDataFor.of_canonical
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2RayleighTraceSpectralDataFor W mu) :
    C9GraphonL2RayleighTraceSpectralDataFor W mu := by
  intro hW
  exact
    ⟨(Classical.choice (hspec hW)).toL2RayleighTraceSpectralData⟩

/-- Canonical Hilbert-eigenbasis trace data imply the canonical Rayleigh
trace-data interface. -/
theorem C9GraphonCanonicalL2RayleighTraceSpectralDataFor.of_hilbert
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2HilbertTraceSpectralDataFor W mu) :
    C9GraphonCanonicalL2RayleighTraceSpectralDataFor W mu := by
  intro hW
  exact
    ⟨(Classical.choice (hspec hW)).toCanonicalL2RayleighTraceSpectralData⟩

/-- Canonical Hilbert-eigenbasis trace data also imply the low-band no-sign
compact-action interface.  The action expansion is proved from Hilbert-basis
completeness. -/
theorem C9GraphonCanonicalL2CompactActionTraceSpectralDataForSpectral.of_hilbert
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2HilbertTraceSpectralDataFor W mu) :
    C9GraphonCanonicalL2CompactActionTraceSpectralDataForSpectral W mu := by
  intro hW _hgt _hle
  exact ⟨(Classical.choice (hspec hW)).toCompactActionTraceSpectralData⟩

/-- No-diagonal compact-action trace data imply the compact-action interface:
the diagonal field is recovered from orthonormality and the action expansion. -/
theorem C9GraphonCanonicalL2CompactActionTraceSpectralDataForSpectral.of_no_diag
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral
      W mu) :
    C9GraphonCanonicalL2CompactActionTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionTraceSpectralData⟩

/-- Direct-`HasSum` no-diagonal compact-action trace data imply the
no-diagonal `tsum` interface. -/
theorem C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral.of_hasSum_no_diag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionTraceSpectralDataNoDiag⟩

/-- No-diagonal compact-action trace data imply the weaker bound package by
forgetting the square trace identity. -/
theorem C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_no_diag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionBoundTraceSpectralDataNoDiag⟩

/-- No-trace bound compact-action data imply the existing bound trace
package: cube and ninth trace identities are derived by term-by-term
integration of the row-coordinate expansion. -/
theorem C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_bound_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionBoundSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionBoundTraceSpectralDataNoDiag⟩

/-- Finite-bound no-trace compact-action data imply the infinite-bound
no-trace compact-action package. -/
theorem C9GraphonCanonicalL2CompactActionBoundSpectralDataNoDiagForSpectral.of_finite_bound_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionFiniteBoundSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionBoundSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionBoundSpectralDataNoDiag⟩

/-- Energy no-trace compact-action data imply the finite-bound no-trace
compact-action package. -/
theorem C9GraphonCanonicalL2CompactActionFiniteBoundSpectralDataNoDiagForSpectral.of_energy_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionFiniteBoundSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionFiniteBoundSpectralDataNoDiag⟩

/-- Row-energy no-trace compact-action data imply energy no-trace data. -/
theorem C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagForSpectral.of_row_energy_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionEnergySpectralDataNoDiag⟩

/-- The global pure compact-action theorem implies its low-band form. -/
theorem C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagSpectralTheorem.of_global
    (hspec :
      C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW _hgt _hle
  exact @hspec Omega _ mu _ W hW

/-- The global padded pure compact-action theorem implies its low-band form. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.of_global
    (hspec :
      C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW _hgt _hle
  exact @hspec Omega _ mu _ W hW

/-- The global Rayleigh dense-eigenmode theorem implies its low-band form. -/
theorem C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagSpectralTheorem.of_global
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW _hgt _hle
  exact @hspec Omega _ mu _ W hW

/-- The global op-norm dense-eigenmode theorem implies its low-band form. -/
theorem C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagSpectralTheorem.of_global
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW _hgt _hle
  exact @hspec Omega _ mu _ W hW

/-- Compactness plus the positive op-norm endpoint eigenvalue supplies the
dense principal-bound eigenmode theorem used by the low-band C9 pipeline. -/
theorem C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.of_positiveNormEndpoint
    (hspec :
      C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  rcases hspec hW hgt hle with ⟨hcompact, hendpoint⟩
  refine ⟨?_⟩
  exact
    C9CanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiag.ofCompactGraphonPositiveNormEndpoint
      (mu := mu) (hW := hW) hcompact (by linarith) hendpoint

/-- Compactness alone supplies the positive norm endpoint for graphon
operators, so the low-band compactness theorem implies the older endpoint
package. -/
theorem C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem.of_compact
    (hcompact :
      C9GraphonCanonicalL2CompactSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  have hcompactW := hcompact hW hgt hle
  have hp : 0 < edgeDensity W mu := by linarith
  exact
    ⟨hcompactW,
      CompactSpectral.canonicalGraphonCompact_hasEigenvalue_norm_of_edgeDensity_pos
        (mu := mu) hW hcompactW hp⟩

/-- The positive norm endpoint package is proved in the C9 low band, since
canonical graphon compactness is now proved. -/
theorem C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem.proved :
    C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem.{u} :=
  C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem.of_compact
    C9GraphonCanonicalL2CompactSpectralTheorem.proved

/-- Low-band compactness alone supplies the dense principal-bound eigenmode
theorem used by the C9 pipeline. -/
theorem C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.of_compact
    (hcompact :
      C9GraphonCanonicalL2CompactSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.{u} :=
  C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.of_positiveNormEndpoint
    (C9GraphonCanonicalL2CompactPositiveNormEndpointSpectralTheorem.of_compact hcompact)

/-- The dense principal-bound eigenmode package is proved in the C9 low band
from the compactness theorem. -/
theorem C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.proved :
    C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.{u} :=
  C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.of_compact
    C9GraphonCanonicalL2CompactSpectralTheorem.proved

/-- The older full-orthonormal core theorem implies the padded low-band core
theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.of_core
    (hspec :
      C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCoreSpectralDataNoDiag⟩

/-- Hilbert-basis nonzero spectral-subspace data imply the padded low-band
core theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.of_nonzero_hilbertBasis
    (hspec :
      C9GraphonCanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCoreSpectralDataNoDiag⟩

/-- Canonical zero-orthogonal Hilbert-basis data imply the padded low-band
core theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.of_zero_orthogonal_hilbertBasis
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCoreSpectralDataNoDiag⟩

/-- Lean canonical zero-orthogonal eigenbasis data imply the padded low-band
core theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.of_zero_orthogonal_eigenBasis
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCoreSpectralDataNoDiag⟩

/-- Direct-principal canonical zero-orthogonal eigenbasis data imply the
direct-principal padded low-band core theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.of_zero_orthogonal_eigenBasis_principal_bound
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCorePrincipalBoundSpectralDataNoDiag⟩

/-- Dense countable orthonormal eigenmode data imply the direct-principal
padded low-band core theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.of_zero_orthogonal_orthonormal_eigen_principal_bound
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCorePrincipalBoundSpectralDataNoDiag⟩

/-- The compact graphon operator spectral theorem supplies the direct-principal
padded compact-action package needed by the low-band C9 bound route. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.proved :
    C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.{u} :=
  C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.of_zero_orthogonal_orthonormal_eigen_principal_bound
    C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagSpectralTheorem.proved

/-- Rayleigh-form dense countable orthonormal eigenmode data imply the
direct-principal padded low-band core theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.of_zero_orthogonal_orthonormal_eigen_rayleigh
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCorePrincipalBoundSpectralDataNoDiag⟩

/-- Op-norm-principal dense countable orthonormal eigenmode data imply the
direct-principal padded low-band core theorem. -/
theorem C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.of_zero_orthogonal_orthonormal_eigen_opNorm
    (hspec :
      C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagSpectralTheorem.{u}) :
    C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toPaddedCorePrincipalBoundSpectralDataNoDiag⟩

/-- Padded pure compact-action spectral data imply the bound trace package
consumed by the C9 scalar certificate. -/
theorem C9GraphonBoundTraceSpectralDataForSpectral.of_padded_core_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonBoundTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  have hp : 0 < edgeDensity W mu := by linarith
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toBoundTraceSpectralData hp⟩

/-- Direct-principal padded pure compact-action spectral data imply the bound
trace package consumed by the C9 scalar certificate. -/
theorem C9GraphonBoundTraceSpectralDataForSpectral.of_padded_core_principal_bound_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonBoundTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toBoundTraceSpectralData⟩

/-- The global direct-principal padded compact-action theorem implies the
global low-band bound trace theorem needed by C9. -/
theorem C9GraphonBoundTraceSpectralDataSpectralTheorem.of_padded_core_principal_bound_no_trace
    (hspec :
      C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.{u}) :
    C9GraphonBoundTraceSpectralDataSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toBoundTraceSpectralData⟩

/-- Pointwise low-band bound trace data for a graphon.

This is the preferred graphon-facing spectral package for C9: it avoids the
extra global theorem wrapper and states exactly the data needed by the final
low-band assembly. -/
theorem c9GraphonBoundTraceSpectralData_lowBand
    [IsProbabilityMeasure mu]
    (hW : IsGraphon W mu)
    (hgt : 1 / 2 < edgeDensity W mu)
    (hle : edgeDensity W mu <= 1003 / 2000) :
    Nonempty (C9BoundTraceSpectralData W mu) := by
  exact
    ⟨(Classical.choice
      (C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagSpectralTheorem.proved
        hW hgt hle)).toBoundTraceSpectralData⟩

/-- Legacy theorem-shaped wrapper for the pointwise low-band bound trace
data.  New assembly code should use `c9GraphonBoundTraceSpectralData_lowBand`
directly. -/
theorem C9GraphonBoundTraceSpectralDataSpectralTheorem.proved :
    C9GraphonBoundTraceSpectralDataSpectralTheorem.{u} := by
  intro Omega _ mu _ W hW hgt hle
  exact c9GraphonBoundTraceSpectralData_lowBand hW hgt hle

/-- Pure compact-action spectral data imply row-energy no-trace data. -/
theorem C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForSpectral.of_core_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionRowEnergySpectralDataNoDiag⟩

/-- Good-row no-trace compact-action data imply row-energy no-trace data. -/
theorem C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForSpectral.of_good_row_no_trace
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionGoodRowSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionRowEnergySpectralDataNoDiag⟩

/-- Finite-bound compact-action trace data imply the infinite-bound
compact-action interface. -/
theorem C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_finite_bound
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionBoundTraceSpectralDataNoDiag⟩

/-- Energy compact-action trace data imply the finite-bound compact-action
interface.  This is where the abstract Hilbert-space energy/eigenvalue bridge
enters the graphon low-band pipeline. -/
theorem C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral.of_energy
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionFiniteBoundTraceSpectralDataNoDiag⟩

/-- Energy compact-action trace data also imply the infinite-bound
compact-action interface. -/
theorem C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_energy
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
      W mu :=
  C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_finite_bound
    (C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral.of_energy
      hspec)

/-- Row-energy compact-action trace data imply the finite-energy compact-action
interface. -/
theorem C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral.of_row_energy
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionEnergyTraceSpectralDataNoDiag⟩

/-- Row-energy compact-action trace data imply the finite-bound compact-action
interface. -/
theorem C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral.of_row_energy
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral
      W mu :=
  C9GraphonCanonicalL2CompactActionFiniteBoundTraceSpectralDataNoDiagForSpectral.of_energy
    (C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral.of_row_energy
      hspec)

/-- Row-energy compact-action trace data imply the infinite-bound
compact-action interface. -/
theorem C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_row_energy
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
      W mu :=
  C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_energy
    (C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral.of_row_energy
      hspec)

/-- No-diagonal compact-action trace data already imply the row-energy
compact-action interface; the rows are the actual graphon rows in `L²`. -/
theorem C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral.of_no_diag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionRowEnergyTraceSpectralDataNoDiag⟩

/-- Bounded-representative compact-action trace data imply the row-energy
compact-action interface. -/
theorem C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral.of_good_row
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionGoodRowTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionRowEnergyTraceSpectralDataNoDiag⟩

/-- Bounded-representative compact-action trace data imply the finite-energy
compact-action interface. -/
theorem C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral.of_good_row
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionGoodRowTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral
      W mu :=
  C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForSpectral.of_row_energy
    (C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral.of_good_row
      hspec)

/-- Bounded-representative compact-action trace data imply the infinite-bound
compact-action interface. -/
theorem C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_good_row
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionGoodRowTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
      W mu :=
  C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral.of_row_energy
    (C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForSpectral.of_good_row
      hspec)

/-- No-diagonal `tsum` compact-action trace data also imply the direct
`HasSum` interface.

The cubic and ninth convergence required by the direct `HasSum` package is
derived from square summability and the graphon operator norm bound. -/
theorem C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral.of_no_diag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompactActionTraceSpectralDataHasSumNoDiag⟩

/-- Direct-`HasSum` compact-action trace data already imply the complete
direct-`HasSum` compact-action interface.

The coverage of every nonzero eigenvalue is proved from the vector-valued
action expansion, so this implication introduces no finite-spectrum assumption
and does not ask graphon theory for a separate enumeration theorem. -/
theorem C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagForSpectral.of_hasSum_no_diag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompleteCompactActionTraceSpectralDataHasSumNoDiag⟩

/-- No-diagonal compact-action trace data already imply the complete
direct-`HasSum` compact-action interface.  This combines the `tsum`-to-`HasSum`
conversion with the proved nonzero-eigenvalue coverage from action expansion. -/
theorem C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagForSpectral.of_no_diag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toCompleteCompactActionTraceSpectralDataHasSumNoDiag⟩

/-- Complete direct-`HasSum` compact-action trace data imply the existing
direct-`HasSum` compact-action interface by forgetting only the coverage
field. -/
theorem C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral.of_complete
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagForSpectral
        W mu) :
    C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral
      W mu := by
  intro hW hgt hle
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toC9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag⟩

/-- Canonical compact-expansion trace data imply the canonical Rayleigh
trace-data interface. -/
theorem C9GraphonCanonicalL2RayleighTraceSpectralDataFor.of_compact_expansion
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2CompactExpansionTraceSpectralDataFor W mu) :
    C9GraphonCanonicalL2RayleighTraceSpectralDataFor W mu := by
  intro hW
  exact
    ⟨(Classical.choice (hspec hW)).toCanonicalL2RayleighTraceSpectralData⟩

/-- Rayleigh-form `L²` operator trace data imply the raw trace-data
interface. -/
theorem C9GraphonRawTraceSpectralDataFor.of_l2_rayleigh
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonL2RayleighTraceSpectralDataFor W mu) :
    C9GraphonRawTraceSpectralDataFor W mu :=
by
  intro hW
  exact ⟨(Classical.choice (hspec hW)).toRawTraceSpectralData⟩

/-- Canonical-operator Rayleigh trace data imply the raw trace-data interface. -/
theorem C9GraphonRawTraceSpectralDataFor.of_canonical
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2RayleighTraceSpectralDataFor W mu) :
    C9GraphonRawTraceSpectralDataFor W mu :=
  C9GraphonRawTraceSpectralDataFor.of_l2_rayleigh
    (C9GraphonL2RayleighTraceSpectralDataFor.of_canonical hspec)

/-- Canonical Hilbert-eigenbasis trace data imply the raw trace-data
interface. -/
theorem C9GraphonRawTraceSpectralDataFor.of_canonical_hilbert
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2HilbertTraceSpectralDataFor W mu) :
    C9GraphonRawTraceSpectralDataFor W mu :=
  C9GraphonRawTraceSpectralDataFor.of_canonical
    (C9GraphonCanonicalL2RayleighTraceSpectralDataFor.of_hilbert hspec)

/-- Canonical compact-expansion trace data imply the raw trace-data
interface. -/
theorem C9GraphonRawTraceSpectralDataFor.of_canonical_compact_expansion
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonCanonicalL2CompactExpansionTraceSpectralDataFor W mu) :
    C9GraphonRawTraceSpectralDataFor W mu :=
  C9GraphonRawTraceSpectralDataFor.of_canonical
    (C9GraphonCanonicalL2RayleighTraceSpectralDataFor.of_compact_expansion hspec)

/-- No-diagonal compact-action trace data for the canonical graphon operator
give the raw trace-data package once the edge density is positive.

This is the low-band bridge used by the C9 scalar argument: the diagonal
eigenvector equations and principal sign are derived, while spectral
completeness remains available separately for operator-theoretic statements. -/
def C9CanonicalL2CompactActionTraceSpectralDataNoDiag.toRawTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9RawTraceSpectralData W mu :=
  let SCompact := S.toCompactExpansionTraceSpectralData_of_edgeDensity_pos hp
  let SRay := SCompact.toCanonicalL2RayleighTraceSpectralData
  let SL2 := SRay.toL2RayleighTraceSpectralData
  SL2.toRawTraceSpectralData

/-- Direct-`HasSum` compact-action trace data for the canonical graphon
operator give the raw trace-data package once the edge density is positive.

The positivity assumption is used only to orient the principal eigenvalue
nonnegatively; in the C9 low band it follows from `1 / 2 < edgeDensity W μ`. -/
def C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag.toRawTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9RawTraceSpectralData W mu :=
  S.toCompactActionTraceSpectralDataNoDiag.toRawTraceSpectralData hp

/-- Complete direct-`HasSum` compact-action trace data imply the raw trace-data
package in positive density.  The extra coverage field is preserved for
operator-theoretic honesty, though the C9 scalar argument consumes only the raw
trace identities and principal bound. -/
def C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag.toRawTraceSpectralData
    [IsProbabilityMeasure mu]
    {hW : IsGraphon W mu}
    (S : C9CanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiag hW)
    (hp : 0 < edgeDensity W mu) :
    C9RawTraceSpectralData W mu :=
  S.toC9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag.toRawTraceSpectralData hp

/-- The low-band complete compact-action spectral theorem implies the
low-band raw trace theorem actually needed by the C9 assembly. -/
theorem C9GraphonRawTraceSpectralDataForSpectral.of_complete_compact_action
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagForSpectral
        W mu) :
    C9GraphonRawTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  have hp : 0 < edgeDensity W mu := by linarith
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toRawTraceSpectralData hp⟩

/-- The direct-`HasSum` compact-action spectral theorem also implies the
low-band raw trace theorem needed by C9. -/
theorem C9GraphonRawTraceSpectralDataForSpectral.of_compact_action_hasSum_noDiag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForSpectral
        W mu) :
    C9GraphonRawTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  have hp : 0 < edgeDensity W mu := by linarith
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toRawTraceSpectralData hp⟩

/-- The no-diagonal compact-action spectral theorem also implies the low-band
raw trace theorem needed by C9.

The direct `HasSum` trace identities and nonzero-eigenvalue coverage are
derived from the no-diagonal package, so this bridge keeps the public
low-band hypothesis in the weakest compact-action form currently available. -/
theorem C9GraphonRawTraceSpectralDataForSpectral.of_compact_action_noDiag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonRawTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  have hp : 0 < edgeDensity W mu := by linarith
  exact ⟨(Classical.choice (hspec hW hgt hle)).toRawTraceSpectralData hp⟩

/-- Bound compact-action data imply the low-band bound trace theorem needed
by C9. -/
theorem C9GraphonBoundTraceSpectralDataForSpectral.of_compact_action_bound_noDiag
    [IsProbabilityMeasure mu]
    (hspec :
      C9GraphonCanonicalL2CompactActionBoundTraceSpectralDataNoDiagForSpectral
        W mu) :
    C9GraphonBoundTraceSpectralDataForSpectral W mu := by
  intro hW hgt hle
  have hp : 0 < edgeDensity W mu := by linarith
  exact
    ⟨(Classical.choice (hspec hW hgt hle)).toBoundTraceSpectralData hp⟩

/-- Trace spectral data imply the older `C9SpectralDataFor` interface. -/
theorem C9GraphonSpectralDataFor.of_trace
    [IsProbabilityMeasure mu]
    (hspec : C9GraphonSpectralTraceDataFor W mu) :
    C9GraphonSpectralDataFor W mu := by
  intro hW
  exact ⟨(Classical.choice (hspec hW)).toC9SpectralData hW⟩

/-- The two external graphon-theory inputs still needed for all-density C9,
bundled for one fixed graphon.

The first field is exactly where one may assume Razborov/Reiher's triangle
density theorem.  The second field is the remaining graphon Hilbert-operator
spectral package, with countably many eigenvalues and explicit trace
identities.  The elementary square bound is then derived in Lean from
`trace_compPow_one_le_edge`, and higher-power summability is derived from the
square trace. -/
structure C9AnalyticInputs
    (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop where
  razborov : C9RazborovTriangleDensityFor W mu
  spectral : C9GraphonRawTraceSpectralDataFor W mu

namespace C9SpectralData

/-- Principal eigenvalue in the chosen countable spectral ordering. -/
def principal (S : C9SpectralData W mu) : Real := S.expansion.principal

/-- Negative ninth-power mass of the non-principal tail. -/
def negativeMass (S : C9SpectralData W mu) : Real := S.expansion.negativeMass

theorem negativeMass_nonneg (S : C9SpectralData W mu) :
    0 <= S.negativeMass := by
  rw [negativeMass, C9SpectralExpansion.negativeMass, negativeNinthTailMass]
  exact tsum_nonneg fun n => le_max_right _ _

/-- The ninth trace lower bound inherited from the countable expansion. -/
theorem principal_pow_sub_negativeMass_le_trace (S : C9SpectralData W mu) :
    S.principal ^ 9 - S.negativeMass <= trace mu (compPow mu W 8) := by
  exact S.expansion.principal_pow_sub_negativeMass_le_trace

/-- The square mass of the non-principal tail. -/
def tailSquareMass (S : C9SpectralData W mu) : Real :=
  ∑' n : Nat, S.expansion.eigen (n + 1) ^ 2

/-- The square mass of positive non-principal modes. -/
def positiveTailSquareMass (S : C9SpectralData W mu) : Real :=
  ∑' n : Nat, max (S.expansion.eigen (n + 1)) 0 ^ 2

/-- The square mass of negative non-principal modes. -/
def negativeTailSquareMass (S : C9SpectralData W mu) : Real :=
  ∑' n : Nat, max (-(S.expansion.eigen (n + 1))) 0 ^ 2

private lemma tail_square_le_total_square (eigen : Nat -> Real)
    (hsum : Summable fun n : Nat => eigen n ^ 2) :
    (∑' n : Nat, eigen (n + 1) ^ 2) <= ∑' n : Nat, eigen n ^ 2 := by
  rw [hsum.tsum_eq_zero_add]
  nlinarith [sq_nonneg (eigen 0)]

/-- The non-principal square mass is bounded by the edge density. -/
theorem tailSquareMass_le_edge (S : C9SpectralData W mu) :
    S.tailSquareMass <= edgeDensity W mu :=
  (tail_square_le_total_square S.expansion.eigen S.summable_square).trans
    S.square_bound

/-- The tail square bound after removing the principal mode. -/
theorem tailSquareMass_le_edge_sub_principal_sq
    (S : C9SpectralData W mu) :
    S.tailSquareMass <= edgeDensity W mu - S.principal ^ 2 := by
  have hbound := S.square_bound
  rw [S.summable_square.tsum_eq_zero_add] at hbound
  rw [tailSquareMass, principal, C9SpectralExpansion.principal]
  nlinarith

private lemma single_le_tsum_of_nonneg {f : Nat -> Real}
    (hf : Summable f) (hnonneg : ∀ n, 0 <= f n) (n : Nat) :
    f n <= ∑' n, f n := by
  have h := hf.sum_le_tsum ({n} : Finset Nat) (fun i _ => hnonneg i)
  simpa using h

/-- Every non-principal eigenvalue is individually controlled by the square
bound. -/
theorem tail_eigen_sq_le_edge (S : C9SpectralData W mu) (n : Nat) :
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
    (S : C9SpectralData W mu) :
    Summable fun n : Nat => max (S.expansion.eigen (n + 1)) 0 ^ 2 := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le
    (fun n => sq_nonneg (max (S.expansion.eigen (n + 1)) 0)) ?_ hshift
  intro n
  exact max_self_zero_sq_le_sq (S.expansion.eigen (n + 1))

private lemma negative_tail_square_summable
    (S : C9SpectralData W mu) :
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

/-- The non-principal square mass splits exactly into its positive and
negative parts, with no finiteness assumption on the spectrum. -/
theorem tailSquareMass_eq_positive_add_negative
    (S : C9SpectralData W mu) :
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

theorem positiveTailSquareMass_nonneg (S : C9SpectralData W mu) :
    0 <= S.positiveTailSquareMass := by
  exact tsum_nonneg fun n => sq_nonneg _

theorem negativeTailSquareMass_nonneg (S : C9SpectralData W mu) :
    0 <= S.negativeTailSquareMass := by
  exact tsum_nonneg fun n => sq_nonneg _

theorem positiveTailSquareMass_le_tailSquareMass
    (S : C9SpectralData W mu) :
    S.positiveTailSquareMass <= S.tailSquareMass := by
  rw [S.tailSquareMass_eq_positive_add_negative]
  linarith [S.negativeTailSquareMass_nonneg]

theorem negativeTailSquareMass_le_tailSquareMass
    (S : C9SpectralData W mu) :
    S.negativeTailSquareMass <= S.tailSquareMass := by
  rw [S.tailSquareMass_eq_positive_add_negative]
  linarith [S.positiveTailSquareMass_nonneg]

/-- If the negative modes already use at least `z^2` square mass, the positive
square mass is bounded by the remaining tail bound. -/
theorem positiveTailSquareMass_le_tail_sub_sq
    (S : C9SpectralData W mu) {z : Real}
    (hz : z ^ 2 <= S.negativeTailSquareMass) :
    S.positiveTailSquareMass <= S.tailSquareMass - z ^ 2 := by
  rw [S.tailSquareMass_eq_positive_add_negative]
  linarith

/-- The same remaining-bound estimate with the graphon square bound and the
principal mode removed. -/
theorem positiveTailSquareMass_le_edge_sub_principal_sq_sub_sq
    (S : C9SpectralData W mu) {z : Real}
    (hz : z ^ 2 <= S.negativeTailSquareMass) :
    S.positiveTailSquareMass <=
      edgeDensity W mu - S.principal ^ 2 - z ^ 2 := by
  have htail := S.positiveTailSquareMass_le_tail_sub_sq hz
  have hbound := S.tailSquareMass_le_edge_sub_principal_sq
  linarith

/-- The positive part of the non-principal cubic tail. -/
def positiveTailCubeMass (S : C9SpectralData W mu) : Real :=
  ∑' n : Nat, max (S.expansion.eigen (n + 1) ^ 3) 0

/-- The negative part of the non-principal cubic tail. -/
def negativeTailCubeMass (S : C9SpectralData W mu) : Real :=
  ∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 3)) 0

/-- The signed non-principal cubic tail. -/
def tailCubeSum (S : C9SpectralData W mu) : Real :=
  ∑' n : Nat, S.expansion.eigen (n + 1) ^ 3

theorem positiveTailCubeMass_nonneg (S : C9SpectralData W mu) :
    0 <= S.positiveTailCubeMass := by
  exact tsum_nonneg fun n => le_max_right _ _

theorem negativeTailCubeMass_nonneg (S : C9SpectralData W mu) :
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
    (S : C9SpectralData W mu) :
    Summable fun n : Nat => max (S.expansion.eigen (n + 1) ^ 3) 0 := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_
    (hshift.mul_left (Real.sqrt (edgeDensity W mu)))
  intro n
  exact max_cube_zero_le_sqrt_mul_sq (S.tail_eigen_sq_le_edge n)

/-- The positive cubic tail is bounded by `sqrt(p)` times the tail square mass. -/
theorem positiveTailCubeMass_le_sqrt_edge_mul_tailSquareMass
    (S : C9SpectralData W mu) :
    S.positiveTailCubeMass <=
      Real.sqrt (edgeDensity W mu) * S.tailSquareMass := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  have hbound :
      (∑' n : Nat, max (S.expansion.eigen (n + 1) ^ 3) 0) <=
        ∑' n : Nat,
          Real.sqrt (edgeDensity W mu) * S.expansion.eigen (n + 1) ^ 2 := by
    exact Summable.tsum_le_tsum
      (fun n => max_cube_zero_le_sqrt_mul_sq (S.tail_eigen_sq_le_edge n))
      S.positive_tail_cube_summable
      (hshift.mul_left (Real.sqrt (edgeDensity W mu)))
  calc
    S.positiveTailCubeMass
        <= ∑' n : Nat,
          Real.sqrt (edgeDensity W mu) * S.expansion.eigen (n + 1) ^ 2 := hbound
    _ = Real.sqrt (edgeDensity W mu) * S.tailSquareMass := by
          rw [tailSquareMass, tsum_mul_left]

private lemma negative_tail_cube_summable
    (S : C9SpectralData W mu) :
    Summable fun n : Nat => max (-(S.expansion.eigen (n + 1) ^ 3)) 0 := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  refine Summable.of_nonneg_of_le (fun n => le_max_right _ _) ?_
    (hshift.mul_left (Real.sqrt (edgeDensity W mu)))
  intro n
  exact max_neg_cube_zero_le_sqrt_mul_sq (S.tail_eigen_sq_le_edge n)

/-- The negative cubic tail is bounded by `sqrt(p)` times the tail square mass. -/
theorem negativeTailCubeMass_le_sqrt_edge_mul_tailSquareMass
    (S : C9SpectralData W mu) :
    S.negativeTailCubeMass <=
      Real.sqrt (edgeDensity W mu) * S.tailSquareMass := by
  have hshift : Summable fun n : Nat => S.expansion.eigen (n + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 S.summable_square
  have hbound :
      (∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 3)) 0) <=
        ∑' n : Nat,
          Real.sqrt (edgeDensity W mu) * S.expansion.eigen (n + 1) ^ 2 := by
    exact Summable.tsum_le_tsum
      (fun n => max_neg_cube_zero_le_sqrt_mul_sq (S.tail_eigen_sq_le_edge n))
      S.negative_tail_cube_summable
      (hshift.mul_left (Real.sqrt (edgeDensity W mu)))
  calc
    S.negativeTailCubeMass
        <= ∑' n : Nat,
          Real.sqrt (edgeDensity W mu) * S.expansion.eigen (n + 1) ^ 2 := hbound
    _ = Real.sqrt (edgeDensity W mu) * S.tailSquareMass := by
          rw [tailSquareMass, tsum_mul_left]

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

private lemma positive_tail_part_sq_le_mass
    (S : C9SpectralData W mu) (n : Nat) :
    max (S.expansion.eigen (n + 1)) 0 ^ 2 <=
      S.positiveTailSquareMass := by
  exact single_le_tsum_of_nonneg S.positive_tail_square_summable
    (fun n => sq_nonneg _) n

private lemma negative_tail_part_sq_le_mass
    (S : C9SpectralData W mu) (n : Nat) :
    max (-(S.expansion.eigen (n + 1))) 0 ^ 2 <=
      S.negativeTailSquareMass := by
  exact single_le_tsum_of_nonneg S.negative_tail_square_summable
    (fun n => sq_nonneg _) n

/-- Positive cubic mass is bounded by the `l^2` positive square mass in the
sharp countable form used by the low-band proof. -/
theorem positiveTailCubeMass_le_sqrt_positiveSquare_mul_positiveSquare
    (S : C9SpectralData W mu) :
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

/-- Negative cubic mass is bounded by the `l^2` negative square mass in the
same countable form. -/
theorem negativeTailCubeMass_le_sqrt_negativeSquare_mul_negativeSquare
    (S : C9SpectralData W mu) :
    S.negativeTailCubeMass <=
      Real.sqrt S.negativeTailSquareMass * S.negativeTailSquareMass := by
  have hbound :
      (∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 3)) 0) <=
        ∑' n : Nat,
          Real.sqrt S.negativeTailSquareMass *
            max (-(S.expansion.eigen (n + 1))) 0 ^ 2 := by
    refine Summable.tsum_le_tsum ?_ S.negative_tail_cube_summable
      (S.negative_tail_square_summable.mul_left
        (Real.sqrt S.negativeTailSquareMass))
    intro n
    let a := S.expansion.eigen (n + 1)
    have hterm := max_cube_zero_le_sqrt_mul_sq
      (a := max (-a) 0) (M := S.negativeTailSquareMass)
      (S.negative_tail_part_sq_le_mass n)
    have hc0 : 0 <= max (-a) 0 := le_max_right _ _
    have hc3 : 0 <= max (-a) 0 ^ 3 := pow_nonneg hc0 3
    rw [max_eq_left hc3] at hterm
    simpa [a, max_neg_cube_zero_eq_neg_part_cube] using hterm
  calc
    S.negativeTailCubeMass
        <= ∑' n : Nat,
          Real.sqrt S.negativeTailSquareMass *
            max (-(S.expansion.eigen (n + 1))) 0 ^ 2 := hbound
    _ = Real.sqrt S.negativeTailSquareMass *
          S.negativeTailSquareMass := by
          rw [negativeTailSquareMass, tsum_mul_left]

/-- Positive cubic mass bounded by any explicit upper bound for positive
square mass. -/
theorem positiveTailCubeMass_le_sqrt_bound_mul_bound
    (S : C9SpectralData W mu) {B : Real}
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

/-- The signed cubic tail is positive cubic mass minus negative cubic mass. -/
theorem tailCubeSum_eq_positive_sub_negative (S : C9SpectralData W mu) :
    S.tailCubeSum = S.positiveTailCubeMass - S.negativeTailCubeMass := by
  have hpos := S.positive_tail_cube_summable
  have hneg := S.negative_tail_cube_summable
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
          rw [hpos.tsum_sub hneg]
          rfl

/-- The signed non-principal cubic tail is the triangle trace minus the
principal cubic contribution. -/
theorem tailCubeSum_eq_trace_cube_sub_principal_cube
    (S : C9SpectralData W mu) :
    S.tailCubeSum = trace mu (compPow mu W 2) - S.principal ^ 3 := by
  calc
    S.tailCubeSum
        = (∑' n : Nat, S.expansion.eigen n ^ 3) -
            S.expansion.eigen 0 ^ 3 := by
          rw [tailCubeSum, S.summable_cube.tsum_eq_zero_add]
          ring
    _ = trace mu (compPow mu W 2) - S.principal ^ 3 := by
          rw [S.trace_cube, principal, C9SpectralExpansion.principal]

/-- Linear triangle slack gives the lower bound on the signed non-principal
cubic tail used in the C9 spectral argument. -/
theorem tailCubeSum_lower_of_linear_triangle
    (S : C9SpectralData W mu)
    (htri :
      (149 / 100) * (edgeDensity W mu - 1 / 2) <=
        trace mu (compPow mu W 2)) :
    (149 / 100) * (edgeDensity W mu - 1 / 2) - S.principal ^ 3 <=
    S.tailCubeSum := by
  rw [S.tailCubeSum_eq_trace_cube_sub_principal_cube]
  linarith

/-- A signed cubic-tail upper bound from a positive-square bound and a
negative-cubic lower bound. -/
theorem tailCubeSum_le_of_positiveSquare_and_negativeCube
    (S : C9SpectralData W mu) {B z : Real}
    (hB0 : 0 <= B)
    (hpos : S.positiveTailSquareMass <= B)
    (hneg : z ^ 3 <= S.negativeTailCubeMass) :
    S.tailCubeSum <= Real.sqrt B * B - z ^ 3 := by
  rw [S.tailCubeSum_eq_positive_sub_negative]
  have hposcube := S.positiveTailCubeMass_le_sqrt_bound_mul_bound hB0 hpos
  linarith

/-- Linear triangle slack, combined with positive-square and negative-cubic
bounds, yields the scalar inequality that the C9 closure certificate must
contradict. -/
theorem linear_triangle_le_cubic_capacity
    (S : C9SpectralData W mu) {B z : Real}
    (htri :
      (149 / 100) * (edgeDensity W mu - 1 / 2) <=
        trace mu (compPow mu W 2))
    (hB0 : 0 <= B)
    (hpos : S.positiveTailSquareMass <= B)
    (hneg : z ^ 3 <= S.negativeTailCubeMass) :
    (149 / 100) * (edgeDensity W mu - 1 / 2) - S.principal ^ 3 <=
      Real.sqrt B * B - z ^ 3 := by
  exact (S.tailCubeSum_lower_of_linear_triangle htri).trans
    (S.tailCubeSum_le_of_positiveSquare_and_negativeCube hB0 hpos hneg)

private lemma finset_sum_cube_le_sum_cube {ι : Type*} (s : Finset ι) (c : ι -> Real)
    (hc0 : ∀ i, 0 <= c i) :
    (∑ i ∈ s, c i ^ 3) <= (∑ i ∈ s, c i) ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      have hsum0 : 0 <= ∑ i ∈ s, c i := Finset.sum_nonneg fun i _ => hc0 i
      have hpow := pow_add_pow_le (hc0 a) hsum0 (show (3 : Nat) ≠ 0 by decide)
      nlinarith

private lemma tsum_cube_le_tsum_cube {c : Nat -> Real}
    (hc0 : ∀ n, 0 <= c n) (hc : Summable c) :
    (∑' n : Nat, c n ^ 3) <= (∑' n : Nat, c n) ^ 3 := by
  have hsum_le :
      ∀ s : Finset Nat, ∑ n ∈ s, c n ^ 3 <= (∑' n : Nat, c n) ^ 3 := by
    intro s
    have hfin := finset_sum_cube_le_sum_cube s c hc0
    have hpartial : ∑ n ∈ s, c n <= ∑' n : Nat, c n :=
      hc.sum_le_tsum s (fun n _ => hc0 n)
    have hmono : (∑ n ∈ s, c n) ^ 3 <= (∑' n : Nat, c n) ^ 3 := by
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => hc0 n) hpartial 3
    exact hfin.trans hmono
  exact Real.tsum_le_of_sum_le (fun n => pow_nonneg (hc0 n) 3) hsum_le

private lemma max_neg_cube_pow_three_eq_max_neg_ninth (a : Real) :
    (max (-(a ^ 3)) 0) ^ 3 = max (-(a ^ 9)) 0 := by
  by_cases ha : 0 <= a
  · have h3 : 0 <= a ^ 3 := pow_nonneg ha 3
    have h9 : 0 <= a ^ 9 := pow_nonneg ha 9
    have hleft : max (-(a ^ 3)) 0 = 0 := max_eq_right (by linarith)
    have hright : max (-(a ^ 9)) 0 = 0 := max_eq_right (by linarith)
    rw [hleft, hright]
    norm_num
  · have ha_nonpos : a <= 0 := le_of_not_ge ha
    have h3neg : a ^ 3 <= 0 := by nlinarith [sq_nonneg a]
    have h8nonneg : 0 <= a ^ 8 := by
      have h : 0 <= (a ^ 4) ^ 2 := sq_nonneg (a ^ 4)
      convert h using 1
      ring
    have h9nonpos : a ^ 9 <= 0 := by
      have h : a ^ 9 = a * a ^ 8 := by ring
      rw [h]
      exact mul_nonpos_of_nonpos_of_nonneg ha_nonpos h8nonneg
    have hleft : max (-(a ^ 3)) 0 = -(a ^ 3) := max_eq_left (by linarith)
    have hright : max (-(a ^ 9)) 0 = -(a ^ 9) := max_eq_left (by linarith)
    rw [hleft, hright]
    ring

/-- The negative ninth mass is bounded by the cube of the negative cubic mass.
This is the countable `l^3/l^9` monotonicity step used in the paper. -/
theorem negativeMass_le_negativeTailCubeMass_cube
    (S : C9SpectralData W mu) :
    S.negativeMass <= S.negativeTailCubeMass ^ 3 := by
  calc
    S.negativeMass
        = ∑' n : Nat,
            max (-(S.expansion.eigen (n + 1) ^ 3)) 0 ^ 3 := by
          rw [negativeMass, C9SpectralExpansion.negativeMass,
            negativeNinthTailMass]
          apply tsum_congr
          intro n
          exact (max_neg_cube_pow_three_eq_max_neg_ninth
            (S.expansion.eigen (n + 1))).symm
    _ <= (∑' n : Nat, max (-(S.expansion.eigen (n + 1) ^ 3)) 0) ^ 3 := by
          exact tsum_cube_le_tsum_cube
            (fun n => le_max_right _ _)
            S.negative_tail_cube_summable
    _ = S.negativeTailCubeMass ^ 3 := by
          rw [negativeTailCubeMass]

/-- A ninth-power lower bound on the negative spectral tail forces the
corresponding cubic lower bound. -/
theorem negativeTailCubeMass_lower_of_negativeMass_lower
    (S : C9SpectralData W mu) {z : Real}
    (hz0 : 0 <= z) (hz : z ^ 9 <= S.negativeMass) :
    z ^ 3 <= S.negativeTailCubeMass := by
  have hpow : z ^ 9 <= S.negativeTailCubeMass ^ 3 :=
    hz.trans S.negativeMass_le_negativeTailCubeMass_cube
  have hrewrite : (z ^ 3) ^ 3 = z ^ 9 := by ring
  rw [← hrewrite] at hpow
  exact (pow_le_pow_iff_left₀ (pow_nonneg hz0 3)
    S.negativeTailCubeMass_nonneg (by norm_num : (3 : Nat) ≠ 0)).1 hpow

private lemma sq_le_of_cube_le_sqrt_mul_self
    {z x : Real} (hz0 : 0 <= z) (hx0 : 0 <= x)
    (h : z ^ 3 <= Real.sqrt x * x) :
    z ^ 2 <= x := by
  have hz3 : 0 <= z ^ 3 := pow_nonneg hz0 3
  have hsq := pow_le_pow_left₀ hz3 h 2
  have hsqrt_sq : (Real.sqrt x * x) ^ 2 = x ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hx0]
    ring
  have hzpow : (z ^ 3) ^ 2 = (z ^ 2) ^ 3 := by ring
  rw [hsqrt_sq, hzpow] at hsq
  exact (pow_le_pow_iff_left₀ (pow_nonneg hz0 2) hx0
    (by norm_num : (3 : Nat) ≠ 0)).1 hsq

/-- A cubic lower bound on the negative tail forces the matching square lower
bound, using the countable `l^2/l^3` estimate. -/
theorem negativeTailSquareMass_lower_of_negativeCube_lower
    (S : C9SpectralData W mu) {z : Real}
    (hz0 : 0 <= z) (hz : z ^ 3 <= S.negativeTailCubeMass) :
    z ^ 2 <= S.negativeTailSquareMass := by
  exact sq_le_of_cube_le_sqrt_mul_self hz0 S.negativeTailSquareMass_nonneg
    (hz.trans S.negativeTailCubeMass_le_sqrt_negativeSquare_mul_negativeSquare)

/-- A ninth-power lower bound on the negative tail also consumes `z^2` square
mass in the negative modes. -/
theorem negativeTailSquareMass_lower_of_negativeMass_lower
    (S : C9SpectralData W mu) {z : Real}
    (hz0 : 0 <= z) (hz : z ^ 9 <= S.negativeMass) :
    z ^ 2 <= S.negativeTailSquareMass := by
  exact S.negativeTailSquareMass_lower_of_negativeCube_lower hz0
    (S.negativeTailCubeMass_lower_of_negativeMass_lower hz0 hz)

/-- Combined infinite-spectral closure inequality: if the negative ninth mass
is at least `z^9`, then triangle slack must fit inside the remaining positive
cubic capacity after the negative modes have consumed `z^2` square mass. -/
theorem linear_triangle_le_capacity_of_negativeMass
    (S : C9SpectralData W mu) {z : Real}
    (htri :
      (149 / 100) * (edgeDensity W mu - 1 / 2) <=
        trace mu (compPow mu W 2))
    (hz0 : 0 <= z)
    (hB0 : 0 <= edgeDensity W mu - S.principal ^ 2 - z ^ 2)
    (hz : z ^ 9 <= S.negativeMass) :
    (149 / 100) * (edgeDensity W mu - 1 / 2) - S.principal ^ 3 <=
      Real.sqrt (edgeDensity W mu - S.principal ^ 2 - z ^ 2) *
        (edgeDensity W mu - S.principal ^ 2 - z ^ 2) - z ^ 3 := by
  have hnegcube := S.negativeTailCubeMass_lower_of_negativeMass_lower hz0 hz
  have hnegsq := S.negativeTailSquareMass_lower_of_negativeMass_lower hz0 hz
  have hpos :=
    S.positiveTailSquareMass_le_edge_sub_principal_sq_sub_sq hnegsq
  exact S.linear_triangle_le_cubic_capacity htri hB0 hpos hnegcube

/-- The paper's C9 spectral-closure estimate, stated over countably infinite
spectral data and Razborov's triangle-density lower bound.

This is intentionally a `Prop`: it is the next analytic theorem to prove from
the fields of `C9SpectralData`, not an approximation or finite-rank statement. -/
def ClosureEstimate (S : C9SpectralData W mu) : Prop :=
  RazborovTriangleLower W mu ->
  1 / 2 < edgeDensity W mu ->
  edgeDensity W mu <= 1003 / 2000 ->
  S.negativeMass <=
    S.principal ^ 9 - edgeDensity W mu ^ 9 +
      edgeDensity W mu * (1 - edgeDensity W mu) ^ 8

/-- The spectral closure estimate after Razborov has been reduced to the
linear triangle slack used in the C9 scalar certificate. -/
def LinearTriangleClosureEstimate (S : C9SpectralData W mu) : Prop :=
  1 / 2 < edgeDensity W mu ->
  edgeDensity W mu <= 1003 / 2000 ->
  (149 / 100) * (edgeDensity W mu - 1 / 2) <=
    trace mu (compPow mu W 2) ->
  S.negativeMass <=
    S.principal ^ 9 - edgeDensity W mu ^ 9 +
      edgeDensity W mu * (1 - edgeDensity W mu) ^ 8

/-- The countable spectral C9 closure follows from the remaining scalar
capacity exclusion.  This theorem contains no finite-rank approximation: the
root `z` is taken from the total negative ninth `tsum` mass. -/
theorem linearTriangleClosureEstimate_of_scalarCapacityExclusion
    (S : C9SpectralData W mu)
    (hscalar : C9LinearScalarCapacityExclusion) :
    S.LinearTriangleClosureEstimate := by
  intro hgt hle htri
  by_contra htarget
  have hlt :
      S.principal ^ 9 - edgeDensity W mu ^ 9 +
          edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 <
        S.negativeMass := not_le.mp htarget
  obtain ⟨z, hz0, hzpow⟩ :=
    exists_nonneg_ninth_root S.negativeMass_nonneg
  have hzle : z ^ 9 <= S.negativeMass := by rw [hzpow]
  have hnegsq :
      z ^ 2 <= S.negativeTailSquareMass :=
    S.negativeTailSquareMass_lower_of_negativeMass_lower hz0 hzle
  have hB0 : 0 <= edgeDensity W mu - S.principal ^ 2 - z ^ 2 := by
    have hneg_tail := S.negativeTailSquareMass_le_tailSquareMass
    have htail_bound := S.tailSquareMass_le_edge_sub_principal_sq
    linarith
  have hcapacity :=
    S.linear_triangle_le_capacity_of_negativeMass htri hz0 hB0 hzle
  have hstrict :
      Real.sqrt (edgeDensity W mu - S.principal ^ 2 - z ^ 2) *
          (edgeDensity W mu - S.principal ^ 2 - z ^ 2) - z ^ 3 <
        (149 / 100) * (edgeDensity W mu - 1 / 2) - S.principal ^ 3 := by
    have hltz :
        S.principal ^ 9 - edgeDensity W mu ^ 9 +
            edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 < z ^ 9 := by
      rwa [← hzpow] at hlt
    exact hscalar hgt hle S.principal_ge_edge hz0 hltz hB0
  linarith

/-- The C9 linear-triangle spectral closure estimate for countable spectral
data.  The scalar capacity exclusion is proved above, so this theorem has no
remaining scalar hypothesis. -/
theorem linearTriangleClosureEstimate
    (S : C9SpectralData W mu) :
    S.LinearTriangleClosureEstimate :=
  S.linearTriangleClosureEstimate_of_scalarCapacityExclusion
    c9LinearScalarCapacityExclusion

/-- C9 in the low band follows from Razborov plus the spectral closure estimate
for the countable spectral data. -/
theorem c9_cycle_bound_of_closure
    (S : C9SpectralData W mu)
    (hclosure : S.ClosureEstimate)
    (htri : RazborovTriangleLower W mu)
    (hgt : 1 / 2 < edgeDensity W mu)
    (hle : edgeDensity W mu <= 1003 / 2000) :
    trace mu (compPow mu W 8) >=
      edgeDensity W mu ^ 9 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 := by
  exact S.expansion.c9_cycle_bound_of_mass_bound rfl (hclosure htri hgt hle)

end C9SpectralData

private lemma razborov_parameter_le_one_fivehundred
    {c eps : Real}
    (_hc0 : 0 <= c) (hc13 : c <= 1 / 3)
    (heps : eps = c - (3 / 2) * c ^ 2) (hepsle : eps <= 3 / 2000) :
    c <= 1 / 500 := by
  by_contra h
  have hcge : 1 / 500 <= c := by linarith
  have hdif : 0 <= c - 1 / 500 := by linarith
  have hfactor : 0 <= 1 - (3 / 2) * (c + 1 / 500) := by nlinarith
  have hmono : (1 / 500 : Real) - (3 / 2) * (1 / 500) ^ 2 <=
      c - (3 / 2) * c ^ 2 := by
    have hm := mul_nonneg hdif hfactor
    nlinarith
  rw [heps] at hepsle
  norm_num at hmono
  linarith

private lemma razborov_theta_linear_lower
    {c eps theta : Real} (hc0 : 0 <= c) (hc : c <= 1 / 500)
    (heps : eps = c - (3 / 2) * c ^ 2)
    (htheta : theta = (3 / 2) * c * (1 - c) ^ 2) :
    (149 / 100) * eps <= theta := by
  rw [heps, htheta]
  nlinarith [hc0, hc]

/-- In the C9 low band, Razborov's triangle lower bound implies the exact
linear triangle slack used by the scalar certificate. -/
theorem triangle_linear_lower_of_razborov
    (htri : RazborovTriangleLower W mu)
    (hupper : edgeDensity W mu <= 1003 / 2000) :
    (149 / 100) * (edgeDensity W mu - 1 / 2) <=
      trace mu (compPow mu W 2) := by
  rcases htri with ⟨c, hc0, hc13, hp, htheta⟩
  have heps : edgeDensity W mu - 1 / 2 = c - (3 / 2) * c ^ 2 := by
    rw [hp]
    ring
  have hepsle : edgeDensity W mu - 1 / 2 <= 3 / 2000 := by
    linarith
  have hc500 : c <= 1 / 500 :=
    razborov_parameter_le_one_fivehundred hc0 hc13 heps hepsle
  have hlinear :
      (149 / 100) * (edgeDensity W mu - 1 / 2) <=
        (3 / 2) * c * (1 - c) ^ 2 :=
    razborov_theta_linear_lower hc0 hc500 heps rfl
  exact hlinear.trans htheta

namespace C9SpectralData

/-- Razborov's triangle bound plus the linear-triangle spectral closure imply
the Razborov-form closure estimate. -/
theorem closureEstimate_of_linearTriangleClosure
    (S : C9SpectralData W mu)
    (hlinear : S.LinearTriangleClosureEstimate) :
    S.ClosureEstimate := by
  intro htri hgt hle
  exact hlinear hgt hle (triangle_linear_lower_of_razborov htri hle)

/-- C9 in the low band from Razborov and the linear-triangle version of the
countable spectral closure estimate. -/
theorem c9_cycle_bound_of_linearTriangleClosure
    (S : C9SpectralData W mu)
    (hlinear : S.LinearTriangleClosureEstimate)
    (htri : RazborovTriangleLower W mu)
    (hgt : 1 / 2 < edgeDensity W mu)
    (hle : edgeDensity W mu <= 1003 / 2000) :
    trace mu (compPow mu W 8) >=
      edgeDensity W mu ^ 9 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 := by
  exact S.c9_cycle_bound_of_closure
    (S.closureEstimate_of_linearTriangleClosure hlinear) htri hgt hle

/-- C9 in the low band from Razborov and countable spectral data. -/
theorem c9_cycle_bound_of_razborov
    (S : C9SpectralData W mu)
    (htri : RazborovTriangleLower W mu)
    (hgt : 1 / 2 < edgeDensity W mu)
    (hle : edgeDensity W mu <= 1003 / 2000) :
    trace mu (compPow mu W 8) >=
      edgeDensity W mu ^ 9 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 := by
  exact S.c9_cycle_bound_of_linearTriangleClosure
    S.linearTriangleClosureEstimate htri hgt hle

end C9SpectralData

end InfiniteSpectral
end Spectral
end OddCycleBound
