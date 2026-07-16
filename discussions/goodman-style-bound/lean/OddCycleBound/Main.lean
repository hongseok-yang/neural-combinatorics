import OddCycleBound.BoundsC5C7
import OddCycleBound.BasicBounds
import OddCycleBound.C9
import OddCycleBound.C11
import OddCycleBound.C13
import OddCycleBound.HighDensity.MomentExpansion
import OddCycleBound.LowBand.C9Spectral
import OddCycleBound.Conditional
import OddCycleBound.RegionII.LargeOdd
import OddCycleBound.RegionII.C13Frontier

/-!
# Main graphon-facing results

This is the theorem-only public facade.  Names follow these conventions:

* Ck_bound: unconditional at every edge density;
* Ck_path_bound: unconditional on a stated density range;
* Ck_conditional_bound: every density, under an external hypothesis;
* Ck_path_conditional_bound: a stated density range, under an external
  hypothesis;
* odd_cycle_..._bound: a result uniform in the odd cycle length.
-/

open MeasureTheory

namespace OddCycleBound

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}
variable {m : Nat}

/-- Unconditional C3 Goodman-type bound at every edge density. -/
theorem C3_bound (hW : IsGraphon W mu) :
    trace mu (compPow mu W 2) >=
      edgeDensity W mu ^ 3 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 2 := by
  simpa [cycleDensity] using
    (HighDensity.cycle_bound_three hW)

/-- Unconditional C5 Goodman-type bound at every edge density. -/
theorem C5_bound (hW : IsGraphon W mu) :
    trace mu (compPow mu W 4) >=
      edgeDensity W mu ^ 5 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 4 := by
  have h := C5_integral (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
  rw [e] at h
  exact h

/-- Unconditional C7 Goodman-type bound at every edge density. -/
theorem C7_bound (hW : IsGraphon W mu) :
    trace mu (compPow mu W 6) >=
      edgeDensity W mu ^ 7 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 6 := by
  have h := C7_integral_all (isGraphon_compl hW)
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
  rw [e] at h
  exact h

/-- Unconditional C9 bound on the path-certificate range
1003 / 2000 <= p. -/
theorem C9_path_bound
    (hW : IsGraphon W mu)
    (hp : 1003 / 2000 <= edgeDensity W mu) :
    trace mu (compPow mu W 8) >=
      edgeDensity W mu ^ 9 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 := by
  have hq : edgeDensity (compl W) mu <= 997 / 2000 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C9_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
  rw [e] at h
  exact h

/-- Unconditional C11 bound on the path-certificate range
103 / 200 <= p. -/
theorem C11_path_bound
    (hW : IsGraphon W mu)
    (hp : 103 / 200 <= edgeDensity W mu) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  have hq : edgeDensity (compl W) mu <= 97 / 200 := by
    rw [edgeDensity_compl hW]
    linarith
  have h := C11_path_integral (isGraphon_compl hW) hq
  rw [compl_compl, edgeDensity_compl hW] at h
  have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
  rw [e] at h
  exact h

/-- Unconditional C13 bound on the complete currently proved range
51 / 100 <= p.  The certified frontier window and the high-density path
certificate meet at 519 / 1000. -/
theorem C13_path_bound
    (hW : IsGraphon W mu)
    (hp : 51 / 100 <= edgeDensity W mu) :
    trace mu (compPow mu W 12) >=
      edgeDensity W mu ^ 13 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 12 := by
  by_cases hfront : edgeDensity W mu <= 519 / 1000
  · exact RegionII.C13_frontier_bound hW hp hfront
  · have hq : edgeDensity (compl W) mu <= 481 / 1000 := by
      rw [edgeDensity_compl hW]
      linarith
    have h := C13_path_integral (isGraphon_compl hW) hq
    rw [compl_compl, edgeDensity_compl hW] at h
    have e : 1 - (1 - edgeDensity W mu) = edgeDensity W mu := by ring
    rw [e] at h
    exact h

/-- Conditional all-density C9 bound.  The sole external input is the direct
Razborov--Reiher triangle-density branch up to 1003 / 2000. -/
theorem C9_conditional_bound
    (hW : IsGraphon W mu)
    (htri : TriangleDensityLowerBoundUpTo.{u} (1003 / 2000)) :
    trace mu (compPow mu W 8) >=
      edgeDensity W mu ^ 9 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 8 := by
  have htriDirect :
      LowBand.InfiniteSpectral.C9RazborovTriangleDensityDirectTheorem.{u} := by
    intro Omega' _ mu' _ W' hW' hgt' hle'
    exact htri hW' hgt' hle'
  by_cases hlow : edgeDensity W mu <= 1 / 2
  · have htr := trace_compPow_nonneg (W := W) hW 8
    have hrhs := rhs9_nonpos_of_le_half (W := W) hW hlow
    exact le_trans hrhs htr
  · have hgt : 1 / 2 < edgeDensity W mu := by linarith
    by_cases hpath : 1003 / 2000 <= edgeDensity W mu
    · exact C9_path_bound hW hpath
    · have hle : edgeDensity W mu <= 1003 / 2000 := by linarith
      let S :=
        (Classical.choice
          (LowBand.InfiniteSpectral.c9GraphonBudgetTraceSpectralData_lowBand
            hW hgt hle)).toC9SpectralData hW
      have htriParam :
          LowBand.InfiniteSpectral.RazborovTriangleLower W mu :=
        LowBand.InfiniteSpectral.C9RazborovTriangleDensityTheorem.of_direct
          htriDirect hW hgt hle
      exact S.c9_cycle_bound_of_razborov htriParam hgt hle

/-- Conditional all-density C11 bound.  The sole external input is the direct
Razborov--Reiher triangle-density branch up to 103 / 200. -/
theorem C11_conditional_bound
    (hW : IsGraphon W mu)
    (htri : TriangleDensityLowerBoundUpTo.{u} (103 / 200)) :
    trace mu (compPow mu W 10) >=
      edgeDensity W mu ^ 11 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 10 := by
  have htriParam :
      1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 103 / 200 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W mu := by
    intro hgt hle
    let p := edgeDensity W mu
    let c := (1 - Real.sqrt (4 - 6 * p)) / 3
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (103 : Real) / 200 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      have hs_sq_le_one : (Real.sqrt (4 - 6 * p)) ^ 2 <= (1 : Real) ^ 2 := by
        rw [hs_sq]
        nlinarith
      have hs_le_one : Real.sqrt (4 - 6 * p) <= 1 := by
        nlinarith [Real.sqrt_nonneg (4 - 6 * p),
          sq_nonneg (Real.sqrt (4 - 6 * p) - 1)]
      dsimp [c]
      nlinarith
    · have hs0 : 0 <= Real.sqrt (4 - 6 * p) := Real.sqrt_nonneg _
      dsimp [c]
      nlinarith
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (103 : Real) / 200 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      dsimp [c, p]
      nlinarith
    · dsimp [c, p]
      exact htri hW hgt hle
  exact C11_bound_of_razborov_theorem hW htriParam

/-- Conditional C13 bound on the complementary partial range p <= 51 / 100.
Together with C13_path_bound this yields the all-density conditional result. -/
theorem C13_path_conditional_bound
    (hW : IsGraphon W mu)
    (htri : TriangleDensityLowerBoundUpTo.{u} (51 / 100))
    (hnear : edgeDensity W mu <= 51 / 100) :
    trace mu (compPow mu W 12) >=
      edgeDensity W mu ^ 13 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 12 := by
  have htriParam :
      1 / 2 < edgeDensity W mu -> edgeDensity W mu <= 51 / 100 ->
        LowBand.InfiniteSpectral.RazborovTriangleLower W mu := by
    intro hgt hle
    let p := edgeDensity W mu
    let c := (1 - Real.sqrt (4 - 6 * p)) / 3
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (51 : Real) / 100 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      have hs_sq_le_one : (Real.sqrt (4 - 6 * p)) ^ 2 <= (1 : Real) ^ 2 := by
        rw [hs_sq]
        nlinarith
      have hs_le_one : Real.sqrt (4 - 6 * p) <= 1 := by
        nlinarith [Real.sqrt_nonneg (4 - 6 * p),
          sq_nonneg (Real.sqrt (4 - 6 * p) - 1)]
      dsimp [c]
      nlinarith
    · have hs0 : 0 <= Real.sqrt (4 - 6 * p) := Real.sqrt_nonneg _
      dsimp [c]
      nlinarith
    · have harg0 : 0 <= 4 - 6 * p := by
        nlinarith [hle, (show (51 : Real) / 100 < 2 / 3 by norm_num)]
      have hs_sq : (Real.sqrt (4 - 6 * p)) ^ 2 = 4 - 6 * p :=
        Real.sq_sqrt harg0
      dsimp [c, p]
      nlinarith
    · dsimp [c, p]
      exact htri hW hgt hle
  exact C13_nearbipartite_bound_of_razborov_theorem hW htriParam hnear

/-- Conditional all-density C13 bound. -/
theorem C13_conditional_bound
    (hW : IsGraphon W mu)
    (htri : TriangleDensityLowerBoundUpTo.{u} (51 / 100)) :
    trace mu (compPow mu W 12) >=
      edgeDensity W mu ^ 13 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 12 := by
  by_cases hnear : edgeDensity W mu <= 51 / 100
  · exact C13_path_conditional_bound hW htri hnear
  · exact C13_path_bound hW (by linarith)

/-- Unconditional Region II theorem, uniform over every odd m >= 15. -/
theorem odd_cycle_regionII_large_bound
    (hW : IsGraphon W mu)
    (hm : Odd m) (hm15 : 15 <= m)
    (hp_lo : 1 / 2 < edgeDensity W mu)
    (hp_hi : edgeDensity W mu < 2 / 3) :
    trace mu (compPow mu W (m - 1)) >=
      edgeDensity W mu ^ m -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) :=
  RegionII.regionII_large_odd_bound hW hm hm15 hp_lo hp_hi

/-- Conditional Region II theorem, uniform over every odd m >= 3.

The only external input is TriangleDensityLowerBoundUpTo (103 / 200). -/
theorem odd_cycle_regionII_conditional_bound
    (hW : IsGraphon W mu)
    (htri : TriangleDensityLowerBoundUpTo.{u} (103 / 200))
    (hm : Odd m) (hm3 : 3 <= m)
    (hp_lo : 1 / 2 < edgeDensity W mu)
    (hp_hi : edgeDensity W mu < 2 / 3) :
    trace mu (compPow mu W (m - 1)) >=
      edgeDensity W mu ^ m -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) := by
  have hmCases :
      m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 9 ∨ m = 11 ∨ m = 13 ∨ 15 <= m := by
    obtain ⟨k, hk⟩ := hm
    omega
  rcases hmCases with rfl | rfl | rfl | rfl | rfl | rfl | hm15
  · simpa using C3_bound hW
  · simpa using C5_bound hW
  · simpa using C7_bound hW
  · have htri9 :
        TriangleDensityLowerBoundUpTo.{u} (1003 / 2000) :=
      htri.mono (by norm_num)
    simpa using C9_conditional_bound hW htri9
  · simpa using C11_conditional_bound hW htri
  · have htri13 :
        TriangleDensityLowerBoundUpTo.{u} (51 / 100) :=
      htri.mono (by norm_num)
    simpa using C13_conditional_bound hW htri13
  · exact odd_cycle_regionII_large_bound hW hm hm15 hp_lo hp_hi

end OddCycleBound
