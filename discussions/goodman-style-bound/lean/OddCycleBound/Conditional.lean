import OddCycleBound.BasicBounds
import OddCycleBound.C9
import OddCycleBound.C11
import OddCycleBound.C13
import OddCycleBound.LowBand.C9Scalar
import OddCycleBound.LowBand.C11Scalar
import OddCycleBound.LowBand.C13Scalar
import OddCycleBound.LowBand.C9Spectral

/-!
# Conditional all-density assembly for C9, C11, and C13

The path-certificate theorems in `Main.lean` prove the high-density ranges.
This file records the exact remaining Lean interfaces needed to turn those
path certificates into all-density theorems.  C9 is complete modulo the named
Razborov/Reiher triangle-density theorem and the graphon spectral package in
`LowBand.C9Spectral`; C11 and C13 still expose their low-band/frontier gaps as
ordinary hypotheses.
-/

open MeasureTheory

namespace OddCycleBound

universe u

variable {Omega : Type u} [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- `CycleBound n W μ` is the normalized odd-cycle lower bound in the shifted
indexing used by `compPow`: for cycle length `n + 1`, it states
`t(C_{n+1}, W) >= p^(n+1) - p*(1-p)^n`, where `p = edgeDensity W μ`. -/
abbrev CycleBound (n : Nat) (W : Omega -> Omega -> Real) (mu : Measure Omega) : Prop :=
  trace mu (compPow mu W n) >=
    edgeDensity W mu ^ (n + 1) - edgeDensity W mu * (1 - edgeDensity W mu) ^ n

private theorem c9_path_bound_for_conditional (hW : IsGraphon W mu)
    (hp : 1003 / 2000 <= edgeDensity W mu) :
    CycleBound 8 W mu := by
  have hq : edgeDensity (compl W) mu <= 997 / 2000 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C9_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
  rw [e] at h
  exact h

private theorem c11_path_bound_for_conditional (hW : IsGraphon W mu)
    (hp : 103 / 200 <= edgeDensity W mu) :
    CycleBound 10 W mu := by
  have hq : edgeDensity (compl W) mu <= 97 / 200 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C11_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
  rw [e] at h
  exact h

private theorem c13_path_bound_for_conditional (hW : IsGraphon W mu)
    (hp : 519 / 1000 <= edgeDensity W mu) :
    CycleBound 12 W mu := by
  have hq : edgeDensity (compl W) mu <= 481 / 1000 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C13_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
  rw [e] at h
  exact h

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
    · exact c9_path_bound_for_conditional hW hpath
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

/-- All-density C9 from the named Razborov/Reiher triangle theorem.

The low-band graphon spectral/budget trace side is supplied by the compact
operator spectral expansion formalized in `C9Spectral`. -/
theorem C9_bound_of_razborov_theorem
    (hW : IsGraphon W mu)
    (htri : LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.{u}) :
    CycleBound 8 W mu := by
  refine C9_bound_of_razborov_and_countable_spectral_data hW ?_ ?_
  · intro hgt hle
    exact htri hW hgt hle
  · intro hgt hle
    exact (Classical.choice
      (LowBand.InfiniteSpectral.c9GraphonBudgetTraceSpectralData_lowBand
        hW hgt hle)).toC9SpectralData hW

/-- Conditional all-density C11 assembly from the spectral negative-mass
estimate on the low band.

The low-band hypothesis is the analytic output expected from the
Razborov/Reiher triangle-density theorem plus the Hilbert--Schmidt spectral
layer: a principal value `ell`, a negative eleventh-power mass `N11`, and the
two inequalities `trace >= ell^11 - N11` and
`N11 <= ell^11 - p^11 + p*q^10`. -/
theorem C11_bound_of_negative_mass_gap
    (hW : IsGraphon W mu)
    (hgap : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 103 / 200 ->
      ∃ ell N11 q : Real,
        q = 1 - edgeDensity W mu ∧
        ell ^ 11 - N11 <= trace mu (compPow mu W 10) ∧
        N11 <= ell ^ 11 - edgeDensity W mu ^ 11 +
          edgeDensity W mu * q ^ 10) :
    CycleBound 10 W mu := by
  by_cases hlow : edgeDensity W mu <= 1 / 2
  · have htr := trace_compPow_nonneg (W := W) hW 10
    have hrhs := rhs11_nonpos_of_le_half (W := W) hW hlow
    exact le_trans hrhs htr
  · have hgt : 1 / 2 < edgeDensity W mu := by linarith
    by_cases hpath : 103 / 200 <= edgeDensity W mu
    · exact c11_path_bound_for_conditional hW hpath
    · have hle : edgeDensity W mu <= 103 / 200 := by linarith
      rcases hgap hgt hle with ⟨ell, N11, q, hq, htrace, hN11⟩
      exact LowBand.C11.cycle_bound_of_negative_mass_bound hq htrace hN11

/-- Conditional all-density C13 assembly from the near-bipartite spectral
negative-mass estimate and a frontier-band input.

The near-bipartite hypothesis is the rational Razborov/spectral interval
`1 / 2 < p <= 51 / 100`, phrased as the corresponding negative
thirteenth-power mass estimate.  The frontier interval remains an explicit
condition for now. -/
theorem C13_bound_of_nearbipartite_negative_mass_and_frontier
    (hW : IsGraphon W mu)
    (hnearbip : 1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 51 / 100 ->
      ∃ ell N13 q : Real,
        q = 1 - edgeDensity W mu ∧
        ell ^ 13 - N13 <= trace mu (compPow mu W 12) ∧
        N13 <= ell ^ 13 - edgeDensity W mu ^ 13 +
          edgeDensity W mu * q ^ 12)
    (hfrontier : 51 / 100 <= edgeDensity W mu -> edgeDensity W mu <= 519 / 1000 ->
      CycleBound 12 W mu) :
    CycleBound 12 W mu := by
  by_cases hlow : edgeDensity W mu <= 1 / 2
  · have htr := trace_compPow_nonneg (W := W) hW 12
    have hrhs := rhs13_nonpos_of_le_half (W := W) hW hlow
    exact le_trans hrhs htr
  · have hgt : 1 / 2 < edgeDensity W mu := by linarith
    by_cases hpath : 519 / 1000 <= edgeDensity W mu
    · exact c13_path_bound_for_conditional hW hpath
    · have hbelowPath : edgeDensity W mu <= 519 / 1000 := by linarith
      by_cases hnear : edgeDensity W mu <= 51 / 100
      · rcases hnearbip hgt hnear with ⟨ell, N13, q, hq, htrace, hN13⟩
        exact LowBand.C13.cycle_bound_of_negative_mass_bound hq htrace hN13
      · have hfrontLow : 51 / 100 <= edgeDensity W mu := by linarith
        exact hfrontier hfrontLow hbelowPath

end OddCycleBound
