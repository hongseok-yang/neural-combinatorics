import OddCycleBound.Main
import OddCycleBound.LowBand.C9
import OddCycleBound.LowBand.InfiniteSpectral

/-!
# Conditional all-density assembly for C9, C11, and C13

The path-certificate theorems in `Main.lean` prove the high-density ranges.
This file records the exact remaining Lean interfaces needed to turn those
path certificates into all-density theorems.  No analytic statement is
axiomatized here: the missing spectral/frontier inputs are ordinary hypotheses
to the assembly theorems below.
-/

open MeasureTheory

namespace OddCycleBound

universe u

variable {Omega : Type u} [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

private abbrev CycleBound (n : Nat) (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  trace mu (compPow mu W n) >=
    edgeDensity W mu ^ (n + 1) - edgeDensity W mu * (1 - edgeDensity W mu) ^ n

private lemma trace_compPow_nonneg (hW : IsGraphon W mu) (n : Nat) :
    0 <= trace mu (compPow mu W n) := by
  rw [trace]
  exact integral_nonneg fun x => compPow_nonneg hW n x x

private lemma rhs9_nonpos_of_le_half (hW : IsGraphon W mu)
    (hp : edgeDensity W mu <= 1 / 2) :
    edgeDensity W mu ^ 9 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 <= 0 := by
  have hp0 : 0 <= edgeDensity W mu := edgeDensity_nonneg hW
  have hple : edgeDensity W mu <= 1 - edgeDensity W mu := by linarith
  have hpow : edgeDensity W mu ^ 8 <= (1 - edgeDensity W mu) ^ 8 :=
    pow_le_pow_left₀ hp0 hple 8
  have hmul := mul_le_mul_of_nonneg_left hpow hp0
  have hsplit : edgeDensity W mu ^ 9 = edgeDensity W mu * edgeDensity W mu ^ 8 := by ring
  nlinarith

private lemma rhs11_nonpos_of_le_half (hW : IsGraphon W mu)
    (hp : edgeDensity W mu <= 1 / 2) :
    edgeDensity W mu ^ 11 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 <= 0 := by
  have hp0 : 0 <= edgeDensity W mu := edgeDensity_nonneg hW
  have hple : edgeDensity W mu <= 1 - edgeDensity W mu := by linarith
  have hpow : edgeDensity W mu ^ 10 <= (1 - edgeDensity W mu) ^ 10 :=
    pow_le_pow_left₀ hp0 hple 10
  have hmul := mul_le_mul_of_nonneg_left hpow hp0
  have hsplit : edgeDensity W mu ^ 11 = edgeDensity W mu * edgeDensity W mu ^ 10 := by ring
  nlinarith

private lemma rhs13_nonpos_of_le_half (hW : IsGraphon W mu)
    (hp : edgeDensity W mu <= 1 / 2) :
    edgeDensity W mu ^ 13 - edgeDensity W mu * (1 - edgeDensity W mu) ^ 12 <= 0 := by
  have hp0 : 0 <= edgeDensity W mu := edgeDensity_nonneg hW
  have hple : edgeDensity W mu <= 1 - edgeDensity W mu := by linarith
  have hpow : edgeDensity W mu ^ 12 <= (1 - edgeDensity W mu) ^ 12 :=
    pow_le_pow_left₀ hp0 hple 12
  have hmul := mul_le_mul_of_nonneg_left hpow hp0
  have hsplit : edgeDensity W mu ^ 13 = edgeDensity W mu * edgeDensity W mu ^ 12 := by ring
  nlinarith

/-- Conditional all-density C9 assembly.

The only non-path input is the spectral/triangle band
`1 / 2 < p <= 1003 / 2000`. -/
theorem C9_bound_of_gap
    (hW : IsGraphon W mu)
    (hgap : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      CycleBound 8 W mu) :
    CycleBound 8 W mu := by
  by_cases hlow : edgeDensity W mu <= 1 / 2
  · have htr := trace_compPow_nonneg (W := W) hW 8
    have hrhs := rhs9_nonpos_of_le_half (W := W) hW hlow
    exact le_trans hrhs htr
  · have hgt : 1 / 2 < edgeDensity W mu := by linarith
    by_cases hpath : 1003 / 2000 <= edgeDensity W mu
    · exact C9_path_bound hW hpath
    · have hle : edgeDensity W mu <= 1003 / 2000 := by linarith
      exact hgap hgt hle

/-- Conditional all-density C9 assembly from the actual spectral negative-mass
estimate used in the paper's low-band argument.

The low-band hypothesis supplies a principal value `ell`, a negative
ninth-power mass `N9`, and the two spectral inequalities
`trace >= ell^9 - N9` and
`N9 <= ell^9 - p^9 + p*q^8`.  The final algebraic step is handled by
`LowBand.C9.cycle_bound_of_negative_mass_bound`. -/
theorem C9_bound_of_negative_mass_gap
    (hW : IsGraphon W mu)
    (hgap : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      ∃ ell N9 q : Real,
        q = 1 - edgeDensity W mu ∧
        ell ^ 9 - N9 <= trace mu (compPow mu W 8) ∧
        N9 <= ell ^ 9 - edgeDensity W mu ^ 9 + edgeDensity W mu * q ^ 8) :
    CycleBound 8 W mu := by
  refine C9_bound_of_gap hW ?_
  intro hgt hle
  rcases hgap hgt hle with ⟨ell, N9, q, hq, htrace, hN9⟩
  exact LowBand.C9.cycle_bound_of_negative_mass_bound hq htrace hN9

/-- Conditional all-density C9 assembly from a countably infinite spectral
expansion of the ninth trace.

This is the graphon-facing version of the low-band spectral interface: the
expansion may have infinitely many non-zero eigenvalues.  The remaining
low-band hypothesis is the analytic negative-mass estimate, the part expected
from the triangle-density theorem plus Hilbert-operator inequalities. -/
theorem C9_bound_of_infinite_spectral_gap
    (hW : IsGraphon W mu)
    (hgap : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      ∃ S : LowBand.InfiniteSpectral.C9SpectralExpansion W mu,
      ∃ q : Real,
        q = 1 - edgeDensity W mu ∧
        S.negativeMass <=
          S.principal ^ 9 - edgeDensity W mu ^ 9 + edgeDensity W mu * q ^ 8) :
    CycleBound 8 W mu := by
  refine C9_bound_of_gap hW ?_
  intro hgt hle
  rcases hgap hgt hle with ⟨S, q, hq, hmass⟩
  exact LowBand.InfiniteSpectral.C9SpectralExpansion.c9_cycle_bound_of_mass_bound
    S hq hmass

/-- Conditional all-density C9 assembly from Razborov's triangle-density
lower bound and the countable spectral closure estimate.

Unlike `C9_bound_of_negative_mass_gap`, the spectral input here is not a
finite-rank tuple.  It is the countably infinite spectral data used by the
paper's low-band argument, together with the exact closure estimate that remains
to be proved from those data. -/
theorem C9_bound_of_razborov_and_spectral_closure
    (hW : IsGraphon W mu)
    (htri : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      LowBand.InfiniteSpectral.RazborovTriangleLower W mu)
    (hspec : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      ∃ S : LowBand.InfiniteSpectral.C9SpectralData W mu,
        S.ClosureEstimate) :
    CycleBound 8 W mu := by
  refine C9_bound_of_gap hW ?_
  intro hgt hle
  rcases hspec hgt hle with ⟨S, hclosure⟩
  exact S.c9_cycle_bound_of_closure hclosure (htri hgt hle) hgt hle

/-- Conditional all-density C9 assembly from Razborov and the sharper
linear-triangle form of the countable spectral closure estimate. -/
theorem C9_bound_of_razborov_and_linear_spectral_closure
    (hW : IsGraphon W mu)
    (htri : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      LowBand.InfiniteSpectral.RazborovTriangleLower W mu)
    (hspec : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      ∃ S : LowBand.InfiniteSpectral.C9SpectralData W mu,
        S.LinearTriangleClosureEstimate) :
    CycleBound 8 W mu := by
  refine C9_bound_of_gap hW ?_
  intro hgt hle
  rcases hspec hgt hle with ⟨S, hlinear⟩
  exact S.c9_cycle_bound_of_linearTriangleClosure hlinear (htri hgt hle) hgt hle

/-- Conditional all-density C9 assembly from Razborov, countable spectral
data, and the remaining pure scalar capacity exclusion.

This is narrower than assuming the whole low-band spectral closure: the
infinite spectral mass bookkeeping and the passage from negative ninth mass to
the closure estimate are proved in Lean.  The still-external input is only the
real-variable low-band exclusion `C9LinearScalarCapacityExclusion`. -/
theorem C9_bound_of_razborov_and_scalar_capacity_exclusion
    (hW : IsGraphon W mu)
    (htri : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      LowBand.InfiniteSpectral.RazborovTriangleLower W mu)
    (hscalar : LowBand.InfiniteSpectral.C9LinearScalarCapacityExclusion)
    (hspec : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      LowBand.InfiniteSpectral.C9SpectralData W mu) :
    CycleBound 8 W mu := by
  refine C9_bound_of_gap hW ?_
  intro hgt hle
  let S := hspec hgt hle
  have hlinear := S.linearTriangleClosureEstimate_of_scalarCapacityExclusion hscalar
  exact S.c9_cycle_bound_of_linearTriangleClosure hlinear (htri hgt hle) hgt hle

/-- Conditional all-density C9 assembly from Razborov and countable spectral
data.

The low-band scalar capacity exclusion and the countable spectral mass
bookkeeping are now proved in Lean; the remaining external analytic input here
is the existence of the graphon-facing countable spectral data. -/
theorem C9_bound_of_razborov_and_countable_spectral_data
    (hW : IsGraphon W mu)
    (htri : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      LowBand.InfiniteSpectral.RazborovTriangleLower W mu)
    (hspec : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 1003 / 2000 ->
      LowBand.InfiniteSpectral.C9SpectralData W mu) :
    CycleBound 8 W mu := by
  refine C9_bound_of_gap hW ?_
  intro hgt hle
  exact (hspec hgt hle).c9_cycle_bound_of_razborov (htri hgt hle) hgt hle

/-- All-density C9 from the two standard external analytic packages:
Razborov/Reiher triangle density and the countable graphon spectral data
theorem.

The scalar low-band argument and the infinite-series spectral bookkeeping are
proved in Lean; these two named hypotheses are the remaining graphon-theory
inputs. -/
theorem C9_bound_of_razborov_and_graphon_spectral_theorems
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec : LowBand.InfiniteSpectral.C9GraphonSpectralDataFor W mu) :
    CycleBound 8 W mu := by
  exact C9_bound_of_razborov_and_countable_spectral_data hW
    (fun hgt hle => htri hW hgt hle)
    (fun _hgt _hle => Classical.choice (hspec hW))

/-- All-density C9 from Razborov/Reiher and the sharper graphon spectral
trace-data package.

The square budget is not part of this spectral input: it is derived from
`trace(W^2) = ∑ λ_n^2` and the integral graphon inequality
`trace(W^2) <= edgeDensity W`. -/
theorem C9_bound_of_razborov_and_graphon_spectral_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec : LowBand.InfiniteSpectral.C9GraphonSpectralTraceDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_spectral_theorems hW htri
    (LowBand.InfiniteSpectral.C9GraphonSpectralDataFor.of_trace hspec)

/-- All-density C9 from Razborov/Reiher and the raw graphon spectral
trace-data package.

The raw package asks the operator layer only for square summability,
square/cube/ninth trace identities, and the principal Rayleigh bound.  Lean
derives higher-power summability and the graphon square budget. -/
theorem C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec : LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_spectral_trace_theorem hW htri
    (LowBand.InfiniteSpectral.C9GraphonSpectralTraceDataFor.of_raw hspec)

/-- All-density C9 from Razborov/Reiher and raw graphon spectral trace data
only on the C9 low band.

This is the density-local version of
`C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem`: the spectral
trace theorem is not requested outside `1 / 2 < p <= 1003 / 2000`, because the
existing trivial and path-density arguments cover the complementary regions. -/
theorem C9_bound_of_razborov_and_graphon_raw_spectral_trace_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataForLowBand W mu) :
    CycleBound 8 W mu := by
  refine C9_bound_of_razborov_and_countable_spectral_data hW ?_ ?_
  · intro hgt hle
    exact htri hW hgt hle
  · intro hgt hle
    let Sraw := Classical.choice (hspec hW hgt hle)
    let Strace := Sraw.toC9TraceSpectralData hW
    exact Strace.toC9SpectralData hW

/-- All-density C9 from Razborov/Reiher and low-band budget trace data.

This is weaker than the raw low-band trace endpoint on the square side: it
assumes only `∑ λ_n^2 <= edgeDensity W μ`, not the square trace identity. -/
theorem C9_bound_of_razborov_and_graphon_budget_spectral_trace_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonBudgetTraceSpectralDataForLowBand W mu) :
    CycleBound 8 W mu := by
  refine C9_bound_of_razborov_and_countable_spectral_data hW ?_ ?_
  · intro hgt hle
    exact htri hW hgt hle
  · intro hgt hle
    let Sbudget := Classical.choice (hspec hW hgt hle)
    exact Sbudget.toC9SpectralData hW

/-- All-density C9 from Razborov/Reiher and the minimal direct-`HasSum`
countable graphon trace package.

This is the smallest current spectral interface for the low-band proof: no
finite-spectrum assertion, no compact-action expansion field, and no global
ordering of the eigenvalue sequence beyond the principal lower bound
`edgeDensity W μ <= λ₀`. -/
theorem C9_bound_of_razborov_and_graphon_hasSum_spectral_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec : LowBand.InfiniteSpectral.C9GraphonHasSumTraceSpectralDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem hW htri
    (LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataFor.of_hasSum_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and an explicit `L²` graphon operator
trace-data package.

This is stronger and more grounded than the raw trace package: the principal
Rayleigh bound is derived from the operator quadratic-form domination and the
proved identity `⟪1, T 1⟫ = edgeDensity`. -/
theorem C9_bound_of_razborov_and_graphon_l2_operator_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonL2OperatorTraceSpectralDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem hW htri
    (LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataFor.of_l2_operator
      hspec)

/-- All-density C9 from Razborov/Reiher and an explicit `L²` graphon operator
trace-data package with the standard Rayleigh quotient bound.

The quadratic-form principal bound used downstream is proved in
`InfiniteSpectral` from the Rayleigh quotient inequality. -/
theorem C9_bound_of_razborov_and_graphon_l2_rayleigh_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonL2RayleighTraceSpectralDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem hW htri
    (LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataFor.of_l2_rayleigh
      hspec)

/-- All-density C9 from Razborov/Reiher and spectral trace data for the
canonical graphon `L²` operator constructed in `L2Kernel`.

Here the operator itself and the identity `T 1 = degree` are no longer assumed;
only the compact/self-adjoint spectral trace/Rayleigh package for that
constructed operator remains. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_rayleigh_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2RayleighTraceSpectralDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem hW htri
    (LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataFor.of_canonical
      hspec)

/-- All-density C9 from Razborov/Reiher and a countable Hilbert eigenbasis
trace theorem for the canonical graphon `L²` operator.

This is the grounded spectral endpoint: the graphon operator is the canonical
one from `L2Kernel`, the eigenbasis is countable rather than finite-rank, and
the principal Rayleigh bound is proved in `InfiniteSpectral` from Parseval and
the ordered diagonalization. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_hilbert_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2HilbertTraceSpectralDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_rayleigh_trace_theorem hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2RayleighTraceSpectralDataFor.of_hilbert
      hspec)

/-- All-density C9 from Razborov/Reiher and a compact-expansion trace theorem
for the canonical graphon `L²` operator.

This is weaker than asking for a countable Hilbert basis of the whole `L²`
space: the spectral input lists the countable compact modes, supplies the
Bessel/expansion identities needed for Rayleigh domination, and leaves any
orthogonal residual in the zero eigenspace. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_expansion_trace_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactExpansionTraceSpectralDataFor W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_rayleigh_trace_theorem hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2RayleighTraceSpectralDataFor.of_compact_expansion
      hspec)

/-- All-density C9 from Razborov/Reiher and a low-band compact-action trace
theorem for the canonical graphon `L²` operator.

Unlike the signed compact-expansion package, this hypothesis does not ask for
`0 <= eigen 0`: in the only band where it is used, Lean derives that sign
from `1 / 2 < edgeDensity W μ` by evaluating the expansion at the constant
one vector. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_trace_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionTraceSpectralDataForLowBand
        W mu) :
    CycleBound 8 W mu := by
  refine C9_bound_of_razborov_and_countable_spectral_data hW ?_ ?_
  · intro hgt hle
    exact htri hW hgt hle
  · intro hgt hle
    have hp : 0 < edgeDensity W mu := by linarith
    let Saction := Classical.choice (hspec hW hgt hle)
    let Scompact :=
      Saction.toCompactExpansionTraceSpectralData_of_edgeDensity_pos hp
    let Sray := Scompact.toCanonicalL2RayleighTraceSpectralData
    let Sl2 := Sray.toL2RayleighTraceSpectralData
    let Sraw := Sl2.toRawTraceSpectralData
    exact (Sraw.toC9TraceSpectralData hW).toC9SpectralData hW

/-- All-density C9 from Razborov/Reiher and a low-band compact-action trace
theorem without a separate diagonal-action hypothesis. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu := by
  refine C9_bound_of_razborov_and_countable_spectral_data hW ?_ ?_
  · intro hgt hle
    exact htri hW hgt hle
  · intro hgt hle
    have hp : 0 < edgeDensity W mu := by linarith
    let Sraw :=
      (Classical.choice (hspec hW hgt hle)).toRawTraceSpectralData hp
    exact (Sraw.toC9TraceSpectralData hW).toC9SpectralData hW

/-- All-density C9 from Razborov/Reiher and low-band compact-action budget
data without a separate diagonal-action hypothesis.

This endpoint no longer assumes the square trace identity for the canonical
graphon operator; the spectral input supplies the square budget directly. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_budget_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionBudgetTraceSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_budget_spectral_trace_lowband hW htri
    (LowBand.InfiniteSpectral.C9GraphonBudgetTraceSpectralDataForLowBand.of_compact_action_budget_noDiag
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action budget
data without cube/ninth trace assumptions.

The cube and ninth trace identities are derived in Lean from the Hilbert
action expansion by integrating the graphon row-coordinate series. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_budget_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionBudgetSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_budget_trace_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionBudgetTraceSpectralDataNoDiagForLowBand.of_budget_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action finite
budget data without cube/ninth trace assumptions.

Lean derives square summability and the infinite square budget from the finite
initial-segment estimates, and derives cube/ninth trace identities from the
Hilbert action expansion. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_finite_budget_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionFiniteBudgetSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_budget_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionBudgetSpectralDataNoDiagForLowBand.of_finite_budget_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action finite
energy data without cube/ninth trace assumptions. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_energy_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_finite_budget_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionFiniteBudgetSpectralDataNoDiagForLowBand.of_energy_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action row-energy
data without cube/ninth trace assumptions. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_row_energy_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_energy_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagForLowBand.of_row_energy_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and pure low-band compact-action
spectral data without cube/ninth trace, row-energy, or representative
assumptions. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_core_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_row_energy_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForLowBand.of_core_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band padded compact-action
spectral data.

This is the finite-rank-safe compact-action endpoint: zero eigenvalue padding
is allowed, and the square budget, principal bound, and cube/ninth trace
identities are derived in Lean from the padded action expansion. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_padded_core_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_budget_spectral_trace_lowband hW htri
    (LowBand.InfiniteSpectral.C9GraphonBudgetTraceSpectralDataForLowBand.of_padded_core_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action good-row
data without cube/ninth trace assumptions. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_good_row_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionGoodRowSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_row_energy_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagForLowBand.of_good_row_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action finite
budget data without a separate diagonal-action hypothesis.

The infinite square summability and square budget are derived in Lean from the
finite initial-segment estimates. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_finite_budget_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionFiniteBudgetTraceSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_budget_trace_nodiag_lowband hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionBudgetTraceSpectralDataNoDiagForLowBand.of_finite_budget
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action finite
operator-energy data without a separate diagonal-action hypothesis.

The finite eigenvalue-square estimates are derived in Lean from the
orthonormal action expansion and the finite energy estimates for the canonical
graphon operator. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_energy_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_finite_budget_trace_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionFiniteBudgetTraceSpectralDataNoDiagForLowBand.of_energy
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action row-energy
data without a separate diagonal-action hypothesis.

The finite operator-energy estimates are derived in Lean from the row-wise
Hilbert-Schmidt representation and finite Bessel inequalities. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_row_energy_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_energy_trace_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagForLowBand.of_row_energy
      hspec)

/-- All-density C9 from Razborov/Reiher and low-band compact-action data whose
listed modes have bounded representatives. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_good_row_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionGoodRowTraceSpectralDataNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_row_energy_trace_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagForLowBand.of_good_row
      hspec)

/-- All-density C9 from Razborov/Reiher and a low-band compact-action trace
theorem whose trace identities are stated directly as `HasSum`s and which has
no separate diagonal-action hypothesis. -/
theorem C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_trace_hasSum_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityFor W mu)
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagForLowBand
        W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_trace_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagForLowBand.of_hasSum_no_diag
      hspec)

/-- Global all-density C9 assembly from the two named global analytic
theorems: Razborov/Reiher's triangle-density theorem and the raw graphon
spectral trace-data theorem.

This is the clean theorem-level endpoint for the current formalization:
assuming those two graphon-theory theorems, every graphon satisfies the C9
bound in all density ranges. -/
theorem C9_bound_of_global_razborov_and_raw_spectral_trace
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        Nonempty (LowBand.InfiniteSpectral.C9RawTraceSpectralData W' mu')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem hW
    (fun hW hgt hle => htri hW hgt hle)
    (fun hW => hspec hW)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
budget trace theorem. -/
theorem C9_bound_of_global_razborov_and_budget_spectral_trace_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty (LowBand.InfiniteSpectral.C9BudgetTraceSpectralData W' mu')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_budget_spectral_trace_lowband hW
    (fun hW hgt hle => htri hW hgt hle)
    (fun hW hgt hle => hspec hW hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the canonical
`L²` graphon-operator spectral theorem. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_rayleigh_trace
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2RayleighTraceSpectralData hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_rayleigh_trace_theorem hW
    (fun hW hgt hle => htri hW hgt hle)
    (fun hW => hspec hW)

/-- Global all-density C9 assembly from Razborov/Reiher and a countable
Hilbert eigenbasis trace theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_hilbert_trace
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2HilbertTraceSpectralData hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_hilbert_trace_theorem hW
    (fun hW hgt hle => htri hW hgt hle)
    (fun hW => hspec hW)

/-- Global all-density C9 assembly from Razborov/Reiher and a compact spectral
expansion theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_expansion_trace
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactExpansionTraceSpectralData
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_expansion_trace_theorem hW
    (fun hW hgt hle => htri hW hgt hle)
    (fun hW => hspec hW)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
no-sign compact-action spectral theorem for the canonical graphon `L²`
operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_trace_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionTraceSpectralData
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_trace_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
no-diagonal compact-action spectral theorem for the canonical graphon `L²`
operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionTraceSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_trace_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action budget theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_budget_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionBudgetTraceSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_budget_trace_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action budget theorem without cube/ninth trace assumptions. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_budget_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionBudgetSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_budget_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action finite-budget theorem without cube/ninth trace assumptions. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_finite_budget_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionFiniteBudgetSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_finite_budget_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action finite-energy theorem without cube/ninth trace assumptions. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_energy_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionEnergySpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_energy_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action row-energy theorem without cube/ninth trace assumptions. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_row_energy_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionRowEnergySpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_row_energy_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the pure low-band
compact-action spectral theorem without cube/ninth trace, row-energy, or
representative assumptions. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_core_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionCoreSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_core_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the padded
low-band compact-action spectral theorem.

This uses the finite-rank-safe padded spectral interface rather than the older
full `Nat`-orthonormal core interface. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_padded_core_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionPaddedCoreSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_padded_core_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action good-row theorem without cube/ninth trace assumptions. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_good_row_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionGoodRowSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_good_row_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action finite-budget theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_finite_budget_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionFiniteBudgetTraceSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_finite_budget_trace_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action finite-energy theorem for the canonical graphon `L²`
operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_energy_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionEnergyTraceSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_energy_trace_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action row-energy theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_row_energy_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_row_energy_trace_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
compact-action theorem with bounded mode representatives. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_good_row_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionGoodRowTraceSpectralDataNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_good_row_trace_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- Global all-density C9 assembly from Razborov/Reiher and the low-band
direct-`HasSum`, no-diagonal compact-action spectral theorem for the canonical
graphon `L²` operator. -/
theorem C9_bound_of_global_razborov_and_canonical_l2_compact_action_trace_hasSum_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        IsGraphon W' mu' ->
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W' mu')
    (hspec :
      ∀ {Omega' : Type u} [MeasurableSpace Omega']
        {mu' : Measure Omega'} [IsProbabilityMeasure mu']
        {W' : Omega' -> Omega' -> Real},
        ∀ hW' : IsGraphon W' mu',
        1 / 2 < edgeDensity W' mu' ->
        edgeDensity W' mu' <= 1003 / 2000 ->
        Nonempty
          (LowBand.InfiniteSpectral.C9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag
            hW')) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_canonical_l2_compact_action_trace_hasSum_nodiag_lowband hW
    (fun hW' hgt hle =>
      htri (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)
    (fun hW' hgt hle =>
      hspec (Omega' := Omega) (mu' := mu) (W' := W) hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
raw countable graphon trace theorem.

This is the same conditional endpoint as
`C9_bound_of_global_razborov_and_raw_spectral_trace`, but phrased with the
named theorem propositions from `InfiniteSpectral`.  Taking Razborov as an
axiom elsewhere can be done by supplying the first hypothesis; this file does
not introduce that axiom. -/
theorem C9_bound_of_razborov_theorem_and_raw_spectral_trace
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec : LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_raw_spectral_trace hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' => hspec hW')

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band-only raw graphon spectral trace theorem.

This is the weakest raw trace endpoint currently exposed: it requires the
operator-theoretic trace package only where the C9 proof actually enters the
spectral band. -/
theorem C9_bound_of_razborov_theorem_and_raw_spectral_trace_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonRawTraceSpectralDataLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_raw_spectral_trace_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band budget graphon spectral theorem. -/
theorem C9_bound_of_razborov_theorem_and_budget_spectral_trace_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonBudgetTraceSpectralDataLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_budget_spectral_trace_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem.

The low-band graphon spectral/budget trace side is supplied by the compact
operator spectral expansion formalized in `InfiniteSpectral`. -/
theorem C9_bound_of_razborov_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_budget_spectral_trace_lowband hW htri
    LowBand.InfiniteSpectral.C9GraphonBudgetTraceSpectralDataLowBandTheorem.proved

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
minimal direct-`HasSum` graphon trace theorem. -/
theorem C9_bound_of_razborov_theorem_and_hasSum_spectral_trace
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec : LowBand.InfiniteSpectral.C9GraphonHasSumTraceSpectralDataTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_hasSum_spectral_trace_theorem hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' => hspec hW')

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
grounded low-band compact-action trace theorem for the canonical graphon
`L²` operator.

The spectral hypothesis is countable and compact-operator shaped: it does not
assert that graphons have finitely many non-zero eigenvalues. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_trace_hasSum_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionTraceSpectralDataHasSumNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_trace_hasSum_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
weakest current compact-action low-band theorem for the canonical graphon
`L²` operator.

This assumes no explicit diagonal field and no direct `HasSum` package:
Lean derives the diagonal action, the `HasSum` identities, and coverage of
nonzero eigenvalues from the no-diagonal compact-action data. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionTraceSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_trace_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action budget theorem for the canonical graphon `L²`
operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_budget_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionBudgetTraceSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_budget_trace_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action budget theorem without cube/ninth trace assumptions. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_budget_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionBudgetSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_budget_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action finite-budget theorem without cube/ninth trace
assumptions. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_finite_budget_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionFiniteBudgetSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_finite_budget_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action finite-energy theorem without cube/ninth trace
assumptions. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_energy_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionEnergySpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_energy_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action row-energy theorem without cube/ninth trace
assumptions. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_row_energy_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionRowEnergySpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_row_energy_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
pure low-band compact-action spectral theorem without cube/ninth trace,
row-energy, or representative assumptions. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_core_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_core_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
global pure compact-action spectral theorem. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_core_nodiag
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_core_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionCoreSpectralDataNoDiagLowBandTheorem.of_global
      hspec)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band padded pure compact-action spectral theorem. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_padded_core_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
global padded pure compact-action spectral theorem. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_nodiag
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagLowBandTheorem.of_global
      hspec)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and
direct-principal padded compact-action spectral data.

This is the same compact-action route as the padded theorem above, but its
spectral hypothesis asks directly for the Rayleigh lower bound
`edgeDensity W μ <= eigen 0` instead of a globally sorted padded eigenvalue
enumeration. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_principal_bound_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_budget_spectral_trace_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (LowBand.InfiniteSpectral.C9GraphonBudgetTraceSpectralDataLowBandTheorem.of_padded_core_principal_bound_no_trace
      hspec)

/-- All-density C9 from Razborov/Reiher and the Hilbert-basis nonzero
spectral-subspace theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_nonzero_hilbertBasis_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionNonzeroHilbertBasisSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagLowBandTheorem.of_nonzero_hilbertBasis
      hspec)

/-- All-density C9 from Razborov/Reiher and the Hilbert-basis theorem for
the canonical zero-orthogonal subspace `(eigenspace T 0)ᗮ`. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_hilbertBasis_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagLowBandTheorem.of_zero_orthogonal_hilbertBasis
      hspec)

/-- All-density C9 from Razborov/Reiher and lean eigenbasis data for the
canonical zero-orthogonal subspace `(eigenspace T 0)ᗮ`. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_eigenBasis_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCoreSpectralDataNoDiagLowBandTheorem.of_zero_orthogonal_eigenBasis
      hspec)

/-- All-density C9 from Razborov/Reiher and direct-principal lean eigenbasis
data for the canonical zero-orthogonal subspace `(eigenspace T 0)ᗮ`. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_eigenBasis_principal_bound_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalHilbertBasisEigenPrincipalBoundDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_principal_bound_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagLowBandTheorem.of_zero_orthogonal_eigenBasis_principal_bound
      hspec)

/- All-density C9 from Razborov/Reiher and dense countable orthonormal
eigenmode data for the canonical zero-orthogonal subspace `(eigenspace T 0)ᗮ`.

The bundled Hilbert basis is constructed in Lean from orthonormality and dense
span, so the spectral hypothesis is closer to the usual compact self-adjoint
eigenspace decomposition. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_principal_bound_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_principal_bound_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagLowBandTheorem.of_zero_orthogonal_orthonormal_eigen_principal_bound
      hspec)

/- All-density C9 from Razborov/Reiher and dense countable orthonormal
eigenmode data with Rayleigh domination for the canonical zero-orthogonal
subspace `(eigenspace T 0)ᗮ`. -/
/-- All-density C9 from Razborov/Reiher and the compact positive op-norm
endpoint theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_positiveNormEndpoint_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactPositiveNormEndpointLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_principal_bound_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenPrincipalBoundDataNoDiagLowBandTheorem.of_positiveNormEndpoint
      hspec)

/-- All-density C9 from Razborov/Reiher and compactness of the canonical
graphon `L²` operator in the only remaining low-density band.  The positive
op-norm endpoint is now derived from compactness and graphon positivity. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hcompact :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_positiveNormEndpoint_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactPositiveNormEndpointLowBandTheorem.of_compact
      hcompact)

/-- All-density C9 from Razborov/Reiher and finite-rank Hilbert-Schmidt
approximation of the canonical graphon kernel in the only remaining low-density
band.  The approximation input is used only to prove compactness of the exact
graphon operator; it does not assert finite spectrum for the graphon itself. -/
theorem C9_bound_of_razborov_theorem_and_hilbertSchmidt_finiteRank_approx_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (happrox :
      LowBand.InfiniteSpectral.C9GraphonHilbertSchmidtFiniteRankApproxLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactLowBandTheorem.of_hilbertSchmidt_finiteRank_approx
      happrox)

theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_rayleigh_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_principal_bound_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagLowBandTheorem.of_zero_orthogonal_orthonormal_eigen_rayleigh
      hspec)

/-- All-density C9 from Razborov/Reiher and the global dense orthonormal
eigenmode/Rayleigh theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_rayleigh_nodiag
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_rayleigh_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenRayleighDataNoDiagLowBandTheorem.of_global
      hspec)

/-- All-density C9 from Razborov/Reiher and dense countable orthonormal
eigenmode data whose principal value is the canonical graphon operator norm. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_opNorm_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_padded_core_principal_bound_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionPaddedCorePrincipalBoundSpectralDataNoDiagLowBandTheorem.of_zero_orthogonal_orthonormal_eigen_opNorm
      hspec)

/-- All-density C9 from Razborov/Reiher and the global op-norm-principal dense
orthonormal eigenmode theorem for the canonical graphon `L²` operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_opNorm_nodiag
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_zero_orthogonal_orthonormal_eigen_opNorm_nodiag_lowband
    hW htri
    (LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionZeroOrthogonalOrthonormalEigenOpNormDataNoDiagLowBandTheorem.of_global
      hspec)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action good-row theorem without cube/ninth trace
assumptions. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_good_row_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionGoodRowSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_good_row_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action finite-budget theorem for the canonical graphon `L²`
operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_finite_budget_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionFiniteBudgetTraceSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_finite_budget_trace_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action finite-energy theorem for the canonical graphon `L²`
operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_energy_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionEnergyTraceSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_energy_trace_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action row-energy theorem for the canonical graphon `L²`
operator. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_row_energy_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionRowEnergyTraceSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_row_energy_trace_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
low-band compact-action theorem with bounded mode representatives. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_good_row_trace_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompactActionGoodRowTraceSpectralDataNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_good_row_trace_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle => hspec hW' hgt hle)

/-- All-density C9 from the named Razborov/Reiher triangle theorem and the
complete grounded low-band compact-action trace theorem for the canonical
graphon `L²` operator.

Compared with
`C9_bound_of_razborov_theorem_and_canonical_l2_compact_action_trace_hasSum_nodiag_lowband`,
the spectral theorem assumed here also says the listed sequence covers every
nonzero eigenvalue of the compact graphon operator.  It still does not assert
finite nonzero spectrum. -/
theorem C9_bound_of_razborov_theorem_and_canonical_l2_complete_compact_action_trace_hasSum_nodiag_lowband
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u})
    (hspec :
      LowBand.InfiniteSpectral.C9GraphonCanonicalL2CompleteCompactActionTraceSpectralDataHasSumNoDiagLowBandTheorem.{u}) :
    CycleBound 8 W mu :=
  C9_bound_of_global_razborov_and_canonical_l2_compact_action_trace_hasSum_nodiag_lowband hW
    (fun hW' hgt hle => htri hW' hgt hle)
    (fun hW' hgt hle =>
      ⟨(Classical.choice (hspec hW' hgt hle)).toC9CanonicalL2CompactActionTraceSpectralDataHasSumNoDiag⟩)

/-- All-density C9 from the bundled fixed-graphon analytic inputs. -/
theorem C9_bound_of_analytic_inputs
    (hW : IsGraphon W mu)
    (hanalytic : LowBand.InfiniteSpectral.C9AnalyticInputs W mu) :
    CycleBound 8 W mu :=
  C9_bound_of_razborov_and_graphon_raw_spectral_trace_theorem
    hW hanalytic.razborov hanalytic.spectral

/-- Conditional all-density C11 assembly.

The only non-path input is the spectral/triangle band
`1 / 2 < p <= 103 / 200`. -/
theorem C11_bound_of_gap
    (hW : IsGraphon W mu)
    (hgap : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 103 / 200 ->
      CycleBound 10 W mu) :
    CycleBound 10 W mu := by
  by_cases hlow : edgeDensity W mu <= 1 / 2
  · have htr := trace_compPow_nonneg (W := W) hW 10
    have hrhs := rhs11_nonpos_of_le_half (W := W) hW hlow
    exact le_trans hrhs htr
  · have hgt : 1 / 2 < edgeDensity W mu := by linarith
    by_cases hpath : 103 / 200 <= edgeDensity W mu
    · exact C11_path_bound hW hpath
    · have hle : edgeDensity W mu <= 103 / 200 := by linarith
      exact hgap hgt hle

/-- Conditional all-density C13 assembly.

The hypotheses match the paper's two non-path pieces: the rational
near-bipartite spectral interval `1 / 2 < p <= 51 / 100`, and the frontier
split interval `51 / 100 <= p <= 519 / 1000`. -/
theorem C13_bound_of_gap
    (hW : IsGraphon W mu)
    (hnearbip : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 51 / 100 ->
      CycleBound 12 W mu)
    (hfrontier : 51 / 100 <= edgeDensity W mu -> edgeDensity W mu <= 519 / 1000 ->
      CycleBound 12 W mu) :
    CycleBound 12 W mu := by
  by_cases hlow : edgeDensity W mu <= 1 / 2
  · have htr := trace_compPow_nonneg (W := W) hW 12
    have hrhs := rhs13_nonpos_of_le_half (W := W) hW hlow
    exact le_trans hrhs htr
  · have hgt : 1 / 2 < edgeDensity W mu := by linarith
    by_cases hpath : 519 / 1000 <= edgeDensity W mu
    · exact C13_path_bound hW hpath
    · have hbelowPath : edgeDensity W mu <= 519 / 1000 := by linarith
      by_cases hnear : edgeDensity W mu <= 51 / 100
      · exact hnearbip hgt hnear
      · have hfrontLow : 51 / 100 <= edgeDensity W mu := by linarith
        exact hfrontier hfrontLow hbelowPath

end OddCycleBound
