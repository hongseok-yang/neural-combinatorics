import OddCycleBound.RegionII.C13FrontierAtoms

/-!
# Positivity of the C13 frontier moment polynomial

The exact Bernstein certificates are pointwise statements.  This file lifts
them through the finite frontier-plus-Krylov atomic measure and then transfers
the result back to the complemented graphon's spectral moments.
-/

open scoped BigOperators

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity
open OddCycleBound.RegionII.Certificate

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- The support predicate used by the C13 frontier certificates. -/
def IsC13FrontierAtom (alpha x : ℝ) : Prop :=
  x = alpha ∨ x ∈ Set.Icc (-(1 : ℝ) / 2) (7 / 50)

private theorem c13_multiKernel_two_swap (q x y : ℝ) :
    multiKernel 13 2 q [x, y] = multiKernel 13 2 q [y, x] := by
  rw [multiKernel_expand (by norm_num) (by norm_num),
    multiKernel_expand (by norm_num) (by norm_num)]
  norm_num [hsym, Finset.sum_range_succ]
  ring

private theorem c13_frontier_kernel_one_nonneg
    {q alpha : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (halphaLo : q ≤ alpha) (halphaHi : alpha ≤ 1 / 2)
    {L : List ℝ} (hLlen : L.length = 1)
    (hL : ∀ x ∈ L, IsC13FrontierAtom alpha x) :
    0 ≤ multiKernel 13 1 q L := by
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hLlen
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL x rfl with rfl | hsafe
  · simpa [diagKernel_eq_multiKernel] using
      c13_linear_frontier_nonneg hqlo hqhi halphaLo halphaHi
  · simpa [diagKernel_eq_multiKernel] using
      c13_linear_safe_nonneg hqlo hqhi (by linarith [hsafe.1]) hsafe.2

private theorem c13_frontier_kernel_two_nonneg
    {q alpha : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (halphaLo : q ≤ alpha) (halphaHi : alpha ≤ 1 / 2)
    {L : List ℝ} (hLlen : L.length = 2)
    (hL : ∀ x ∈ L, IsC13FrontierAtom alpha x) :
    0 ≤ multiKernel 13 2 q L := by
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hLlen
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL x (Or.inl rfl) with hx | hx
  · rcases hL y (Or.inr rfl) with hy | hy
    · subst x; subst y
      exact c13_quadratic_frontier_frontier_nonneg hqlo hqhi halphaLo halphaHi
    · subst x
      exact c13_quadratic_frontier_safe_nonneg hqlo hqhi halphaLo halphaHi
        (by linarith [hy.1]) hy.2
  · rcases hL y (Or.inr rfl) with hy | hy
    · subst y
      rw [c13_multiKernel_two_swap]
      exact c13_quadratic_frontier_safe_nonneg hqlo hqhi halphaLo halphaHi
        (by linarith [hx.1]) hx.2
    · exact c13_quadratic_safe_safe_nonneg hqlo hqhi
        (by linarith [hx.1]) hx.2 (by linarith [hy.1]) hy.2

private theorem c13_frontier_kernel_nonneg
    {q alpha : ℝ}
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (halphaLo : q ≤ alpha) (halphaHi : alpha ≤ 1 / 2) :
    ∀ r ∈ Finset.Icc 1 6, ∀ L : List ℝ,
      L.length = r → (∀ x ∈ L, IsC13FrontierAtom alpha x) →
        0 ≤ multiKernel 13 r q L := by
  intro r hr L hlen hL
  have hq0 : 0 ≤ q := by linarith
  have hqhalf : q ≤ 1 / 2 := by linarith
  have hhalf : ∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
    intro x hx
    rcases hL x hx with rfl | hs
    · exact ⟨by linarith, halphaHi⟩
    · exact ⟨hs.1, by linarith [hs.2]⟩
  simp only [Finset.mem_Icc] at hr
  have hrCases : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  rcases hrCases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact c13_frontier_kernel_one_nonneg hqlo hqhi halphaLo halphaHi hlen hL
  · exact c13_frontier_kernel_two_nonneg hqlo hqhi halphaLo halphaHi hlen hL
  · exact c13_multiKernel_three_nonneg hq0 hqhalf hlen hhalf
  · exact c13_multiKernel_four_nonneg hq0 hqhalf hlen hhalf
  · exact c13_multiKernel_five_nonneg hq0 hqhalf hlen hhalf
  · exact c13_multiKernel_six_nonneg hlen hhalf

/-- Positivity of the complete C13 moment polynomial for a finite atomic
measure with one frontier value and all remaining values in the safe band. -/
theorem c13_momentPhi_atomic_nonneg
    {ι : Type*} [Fintype ι]
    {q alpha : ℝ} (w lam : ι → ℝ)
    (hqlo : 481 / 1000 ≤ q) (hqhi : q ≤ 49 / 100)
    (halphaLo : q ≤ alpha) (halphaHi : alpha ≤ 1 / 2)
    (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, IsC13FrontierAtom alpha (lam i)) :
    0 ≤ momentPhi 13 q (atomicMoment w lam) := by
  rw [momentPhi_eq_atomicKernelExpansion (by decide) (by norm_num)]
  unfold atomicKernelExpansion
  apply Finset.sum_nonneg
  intro k hk
  unfold atomicKernelTerm
  apply atomicIntegral_nonneg_of w lam hw (IsC13FrontierAtom alpha)
  · intro L hlen hsupport
    apply c13_frontier_kernel_nonneg hqlo hqhi halphaLo halphaHi (k + 1)
    · simp only [Finset.mem_Icc]
      constructor
      · omega
      · have hklt := Finset.mem_range.mp hk
        norm_num at hklt
        omega
    · exact hlen
    · exact hsupport
  · exact hlam

/-- The C13 moment defect of the complemented graphon is nonnegative in the
frontier branch throughout the certified density window. -/
theorem c13_momentPhi_specMoment_compl_nonneg
    (hW : IsGraphon W μ) (i : CenteredEigenIndex hW)
    (hqlo : 481 / 1000 ≤ 1 - edgeDensity W μ)
    (hqhi : 1 - edgeDensity W μ ≤ 49 / 100)
    (hfront : 1 - edgeDensity W μ < complementEigenvalue hW i) :
    0 ≤ momentPhi 13 (1 - edgeDensity W μ) (specMoment (compl W) μ) := by
  have hqthird : (1 : ℝ) / 3 < 1 - edgeDensity W μ := by linarith
  have halphaHi : complementEigenvalue hW i ≤ (1 : ℝ) / 2 :=
    (complement_frontier_lt_half hW i hqthird hfront).le
  rw [momentPhi_congr_of_le (1 - edgeDensity W μ)
    (fun j hj => specMoment_compl_eq_c13FrontierAtomicMoment hW i hj)]
  exact c13_momentPhi_atomic_nonneg
    (c13FrontierAtomWeight hW i) (c13FrontierAtomEigenvalue hW i)
    hqlo hqhi hfront.le halphaHi (c13FrontierAtomWeight_nonneg hW i)
    (fun k => c13FrontierAtomEigenvalue_frontier_or_safe hW i hqlo hfront k)

end OddCycleBound.RegionII
