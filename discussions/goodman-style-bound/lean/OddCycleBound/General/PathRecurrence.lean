import OddCycleBound.Necklace

/-!
# A general-`m` path-density recurrence

`PathDensity.lean` proves the path-density formulae `x₂ … x₆` by hand, one explicit
`decompₙ`/`pathDensityₙ` lemma at a time.  Here we prove the **general recurrence** once, by a scalar
inner-product argument that avoids any function-valued (`Pi`) sum plumbing:

  `x_{n+1} = q·xₙ + Σ_{i<n} sᵢ·x_{n−1−i}`.

The engine is the family `W k n = ⟨hₖ, kernelOpⁿ1⟩`, which satisfies
`W k 0 = 0`, `W k (n+1) = sₖ·xₙ + W (k+1) n`, hence
`W k n = Σ_{i<n} s_{k+i}·x_{n−1−i}`; specialising `k = 0` and using
`x_{n+1} = q·xₙ + W 0 n` gives the recurrence.  From it `x₇, x₈` (and later `x₉ … x₁₂`)
follow mechanically.  The closed forms are exactly Lemma 2.4 of `paper.tex`.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}


/-- **(A)** `x_{n+1} = q·xₙ + ⟨h₀, kernelOpⁿ1⟩` (`h₀ = g`), via self-adjointness of `kernelOp`. -/
lemma pathDensity_succ_aux (hU : IsGraphon U μ) (n : ℕ) :
    pathDensity U μ (n + 1) = edgeDensity U μ * pathDensity U μ n + pairing μ (compressIter U μ 0) (pathIter U μ n) := by
  have e1 : mean μ (kernelOp U μ (pathIter U μ n)) = ∫ x, pathIter U μ n x * degree U μ x ∂μ := by
    show ∫ x, kernelOp U μ (pathIter U μ n) x ∂μ = _
    rw [show (∫ x, kernelOp U μ (pathIter U μ n) x ∂μ) = ∫ x, kernelOp U μ (pathIter U μ n) x * 1 ∂μ from by simp,
      kernelOp_selfadj hU (good_pathIter hU n) good_one, kernelOp_one hU]
  show mean μ (kernelOp U μ (pathIter U μ n)) = _
  rw [e1]
  have e2 : ∀ x, pathIter U μ n x * degree U μ x
      = edgeDensity U μ * pathIter U μ n x + pathIter U μ n x * compressIter U μ 0 x := fun x => by
    rw [degree_eq']; ring
  rw [integral_congr_ae (ae_of_all _ e2),
    integral_add ((good_pathIter hU n).integrable.const_mul _)
      ((good_pathIter hU n).mul (good_compressIter hU 0)).integrable,
    integral_const_mul]
  congr 1
  show ∫ x, pathIter U μ n x * compressIter U μ 0 x ∂μ = pairing μ (compressIter U μ 0) (pathIter U μ n)
  simp only [pairing]; exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- **(C)** `⟨hₖ, kernelOp⁰1⟩ = ⟨hₖ, 1⟩ = mean hₖ = 0`. -/
lemma pairing_compressIter_pathIter_zero (hU : IsGraphon U μ) (k : ℕ) :
    pairing μ (compressIter U μ k) (pathIter U μ 0) = 0 := by
  show ∫ x, compressIter U μ k x * pathIter U μ 0 x ∂μ = 0
  rw [integral_congr_ae (ae_of_all _ fun x => by
    show compressIter U μ k x * pathIter U μ 0 x = compressIter U μ k x; show compressIter U μ k x * 1 = _; ring)]
  exact mean_compressIter hU k

/-- **(B)** `⟨hₖ, kernelOp^{n+1}1⟩ = sₖ·xₙ + ⟨h_{k+1}, kernelOpⁿ1⟩`. -/
lemma pairing_compressIter_pathIter_succ (hU : IsGraphon U μ) (k n : ℕ) :
    pairing μ (compressIter U μ k) (pathIter U μ (n + 1))
      = specMoment U μ k * pathDensity U μ n + pairing μ (compressIter U μ (k + 1)) (pathIter U μ n) := by
  have hT : pairing μ (compressIter U μ k) (pathIter U μ (n + 1))
      = ∫ x, kernelOp U μ (compressIter U μ k) x * pathIter U μ n x ∂μ := by
    show ∫ x, compressIter U μ k x * kernelOp U μ (pathIter U μ n) x ∂μ = _
    exact (kernelOp_selfadj hU (good_compressIter hU k) (good_pathIter hU n)).symm
  rw [hT]
  have e : ∀ x, kernelOp U μ (compressIter U μ k) x * pathIter U μ n x
      = specMoment U μ k * pathIter U μ n x + compressIter U μ (k + 1) x * pathIter U μ n x := fun x => by
    rw [kernelOp_compressIter' hU k]; ring
  rw [integral_congr_ae (ae_of_all _ e),
    integral_add ((good_pathIter hU n).integrable.const_mul _)
      ((good_compressIter hU (k + 1)).mul (good_pathIter hU n)).integrable,
    integral_const_mul]
  rfl

/-- **(D)** the closed form `⟨hₖ, kernelOpⁿ1⟩ = Σ_{i<n} s_{k+i}·x_{n−1−i}`. -/
lemma pairing_compressIter_pathIter_closed (hU : IsGraphon U μ) : ∀ (n k : ℕ),
    pairing μ (compressIter U μ k) (pathIter U μ n)
      = ∑ i ∈ Finset.range n, specMoment U μ (k + i) * pathDensity U μ (n - 1 - i) := by
  intro n
  induction n with
  | zero => intro k; simp [pairing_compressIter_pathIter_zero hU k]
  | succ n ih =>
      intro k
      rw [pairing_compressIter_pathIter_succ hU k n, ih (k + 1),
        Finset.sum_range_succ' (fun i => specMoment U μ (k + i) * pathDensity U μ (n + 1 - 1 - i)) n]
      have hcong : ∀ i ∈ Finset.range n,
          specMoment U μ (k + (i + 1)) * pathDensity U μ (n + 1 - 1 - (i + 1))
            = specMoment U μ (k + 1 + i) * pathDensity U μ (n - 1 - i) := by
        intro i _
        have a1 : k + (i + 1) = k + 1 + i := by omega
        have a2 : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
        rw [a1, a2]
      rw [Finset.sum_congr rfl hcong]
      have b1 : n + 1 - 1 - 0 = n := by omega
      simp only [Nat.add_zero, b1]
      ring

/-- **The general path-density recurrence** `x_{n+1} = q·xₙ + Σ_{i<n} sᵢ·x_{n−1−i}`. -/
lemma pathDensity_succ (hU : IsGraphon U μ) (n : ℕ) :
    pathDensity U μ (n + 1)
      = edgeDensity U μ * pathDensity U μ n + ∑ i ∈ Finset.range n, specMoment U μ i * pathDensity U μ (n - 1 - i) := by
  rw [pathDensity_succ_aux hU n, pairing_compressIter_pathIter_closed hU n 0]
  simp only [Nat.zero_add]

/-! ### `x₇, x₈` (needed for `C₉`), as instances of the recurrence -/

lemma pathDensity_seven (hU : IsGraphon U μ) :
    pathDensity U μ 7 = edgeDensity U μ ^ 7 + 6 * edgeDensity U μ ^ 5 * specMoment U μ 0 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 1
      + 10 * edgeDensity U μ ^ 3 * specMoment U μ 0 ^ 2 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 2
      + 12 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 1 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 3
      + 4 * edgeDensity U μ * specMoment U μ 0 ^ 3 + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 2
      + 3 * edgeDensity U μ * specMoment U μ 1 ^ 2 + 2 * edgeDensity U μ * specMoment U μ 4
      + 3 * specMoment U μ 0 ^ 2 * specMoment U μ 1 + 2 * specMoment U μ 0 * specMoment U μ 3
      + 2 * specMoment U μ 1 * specMoment U μ 2 + specMoment U μ 5 := by
  have e : pathDensity U μ 7 = edgeDensity U μ * pathDensity U μ 6
      + (specMoment U μ 0 * pathDensity U μ 5 + specMoment U μ 1 * pathDensity U μ 4 + specMoment U μ 2 * pathDensity U μ 3
        + specMoment U μ 3 * pathDensity U μ 2 + specMoment U μ 4 * pathDensity U μ 1 + specMoment U μ 5 * pathDensity U μ 0) := by
    have h := pathDensity_succ hU 6
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, pathDensity_six hU, pathDensity_five hU, pathDensity_four hU, pathDensity_three hU, pathDensity_two hU,
    show pathDensity U μ 1 = edgeDensity U μ from pathDensity_one hU, pathDensity_zero]
  ring

lemma pathDensity_eight (hU : IsGraphon U μ) :
    pathDensity U μ 8 = edgeDensity U μ ^ 8 + 7 * edgeDensity U μ ^ 6 * specMoment U μ 0 + 6 * edgeDensity U μ ^ 5 * specMoment U μ 1
      + 15 * edgeDensity U μ ^ 4 * specMoment U μ 0 ^ 2 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 2
      + 20 * edgeDensity U μ ^ 3 * specMoment U μ 0 * specMoment U μ 1 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 3
      + 10 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 3 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 2
      + 6 * edgeDensity U μ ^ 2 * specMoment U μ 1 ^ 2 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 4
      + 12 * edgeDensity U μ * specMoment U μ 0 ^ 2 * specMoment U μ 1 + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 3
      + 6 * edgeDensity U μ * specMoment U μ 1 * specMoment U μ 2 + 2 * edgeDensity U μ * specMoment U μ 5
      + specMoment U μ 0 ^ 4 + 3 * specMoment U μ 0 ^ 2 * specMoment U μ 2 + 3 * specMoment U μ 0 * specMoment U μ 1 ^ 2
      + 2 * specMoment U μ 0 * specMoment U μ 4 + 2 * specMoment U μ 1 * specMoment U μ 3 + specMoment U μ 2 ^ 2 + specMoment U μ 6 := by
  have e : pathDensity U μ 8 = edgeDensity U μ * pathDensity U μ 7
      + (specMoment U μ 0 * pathDensity U μ 6 + specMoment U μ 1 * pathDensity U μ 5 + specMoment U μ 2 * pathDensity U μ 4
        + specMoment U μ 3 * pathDensity U μ 3 + specMoment U μ 4 * pathDensity U μ 2 + specMoment U μ 5 * pathDensity U μ 1
        + specMoment U μ 6 * pathDensity U μ 0) := by
    have h := pathDensity_succ hU 7
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, pathDensity_seven hU, pathDensity_six hU, pathDensity_five hU, pathDensity_four hU, pathDensity_three hU, pathDensity_two hU,
    show pathDensity U μ 1 = edgeDensity U μ from pathDensity_one hU, pathDensity_zero]
  ring

/-! ### `x₉ … x₁₂` (needed for `C₁₁` and `C₁₃`), as further instances of the recurrence -/

lemma pathDensity_nine (hU : IsGraphon U μ) :
    pathDensity U μ 9 = edgeDensity U μ ^ 9 + 8 * edgeDensity U μ ^ 7 * specMoment U μ 0 + 7 * edgeDensity U μ ^ 6 * specMoment U μ 1 + 21 * edgeDensity U μ ^ 5 * specMoment U μ 0 ^ 2 + 6 * edgeDensity U μ ^ 5 * specMoment U μ 2 + 30 * edgeDensity U μ ^ 4 * specMoment U μ 0 * specMoment U μ 1 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 0 ^ 3 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 3 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 0 * specMoment U μ 2 + 10 * edgeDensity U μ ^ 3 * specMoment U μ 1 ^ 2 + 30 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 2 * specMoment U μ 1 + 5 * edgeDensity U μ * specMoment U μ 0 ^ 4 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 4 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 3 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 1 * specMoment U μ 2 + 12 * edgeDensity U μ * specMoment U μ 0 ^ 2 * specMoment U μ 2 + 12 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 1 ^ 2 + 4 * specMoment U μ 0 ^ 3 * specMoment U μ 1 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 5 + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 4 + 6 * edgeDensity U μ * specMoment U μ 1 * specMoment U μ 3 + 3 * edgeDensity U μ * specMoment U μ 2 ^ 2 + 3 * specMoment U μ 0 ^ 2 * specMoment U μ 3 + 6 * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 2 + specMoment U μ 1 ^ 3 + 2 * edgeDensity U μ * specMoment U μ 6 + 2 * specMoment U μ 0 * specMoment U μ 5 + 2 * specMoment U μ 1 * specMoment U μ 4 + 2 * specMoment U μ 2 * specMoment U μ 3 + specMoment U μ 7 := by
  have e : pathDensity U μ 9 = edgeDensity U μ * pathDensity U μ 8
      + (specMoment U μ 0 * pathDensity U μ 7 + specMoment U μ 1 * pathDensity U μ 6 + specMoment U μ 2 * pathDensity U μ 5 + specMoment U μ 3 * pathDensity U μ 4 + specMoment U μ 4 * pathDensity U μ 3 + specMoment U μ 5 * pathDensity U μ 2 + specMoment U μ 6 * pathDensity U μ 1 + specMoment U μ 7 * pathDensity U μ 0) := by
    have h := pathDensity_succ hU 8
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, pathDensity_eight hU, pathDensity_seven hU, pathDensity_six hU, pathDensity_five hU, pathDensity_four hU, pathDensity_three hU, pathDensity_two hU,
    show pathDensity U μ 1 = edgeDensity U μ from pathDensity_one hU, pathDensity_zero]
  ring

lemma pathDensity_ten (hU : IsGraphon U μ) :
    pathDensity U μ 10 = edgeDensity U μ ^ 10 + 9 * edgeDensity U μ ^ 8 * specMoment U μ 0 + 8 * edgeDensity U μ ^ 7 * specMoment U μ 1 + 28 * edgeDensity U μ ^ 6 * specMoment U μ 0 ^ 2 + 7 * edgeDensity U μ ^ 6 * specMoment U μ 2 + 42 * edgeDensity U μ ^ 5 * specMoment U μ 0 * specMoment U μ 1 + 35 * edgeDensity U μ ^ 4 * specMoment U μ 0 ^ 3 + 6 * edgeDensity U μ ^ 5 * specMoment U μ 3 + 30 * edgeDensity U μ ^ 4 * specMoment U μ 0 * specMoment U μ 2 + 15 * edgeDensity U μ ^ 4 * specMoment U μ 1 ^ 2 + 60 * edgeDensity U μ ^ 3 * specMoment U μ 0 ^ 2 * specMoment U μ 1 + 15 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 4 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 4 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 0 * specMoment U μ 3 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 1 * specMoment U μ 2 + 30 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 2 * specMoment U μ 2 + 30 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 1 ^ 2 + 20 * edgeDensity U μ * specMoment U μ 0 ^ 3 * specMoment U μ 1 + specMoment U μ 0 ^ 5 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 5 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 4 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 1 * specMoment U μ 3 + 6 * edgeDensity U μ ^ 2 * specMoment U μ 2 ^ 2 + 12 * edgeDensity U μ * specMoment U μ 0 ^ 2 * specMoment U μ 3 + 24 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 2 + 4 * edgeDensity U μ * specMoment U μ 1 ^ 3 + 4 * specMoment U μ 0 ^ 3 * specMoment U μ 2 + 6 * specMoment U μ 0 ^ 2 * specMoment U μ 1 ^ 2 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 6 + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 5 + 6 * edgeDensity U μ * specMoment U μ 1 * specMoment U μ 4 + 6 * edgeDensity U μ * specMoment U μ 2 * specMoment U μ 3 + 3 * specMoment U μ 0 ^ 2 * specMoment U μ 4 + 6 * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 3 + 3 * specMoment U μ 0 * specMoment U μ 2 ^ 2 + 3 * specMoment U μ 1 ^ 2 * specMoment U μ 2 + 2 * edgeDensity U μ * specMoment U μ 7 + 2 * specMoment U μ 0 * specMoment U μ 6 + 2 * specMoment U μ 1 * specMoment U μ 5 + 2 * specMoment U μ 2 * specMoment U μ 4 + specMoment U μ 3 ^ 2 + specMoment U μ 8 := by
  have e : pathDensity U μ 10 = edgeDensity U μ * pathDensity U μ 9
      + (specMoment U μ 0 * pathDensity U μ 8 + specMoment U μ 1 * pathDensity U μ 7 + specMoment U μ 2 * pathDensity U μ 6 + specMoment U μ 3 * pathDensity U μ 5 + specMoment U μ 4 * pathDensity U μ 4 + specMoment U μ 5 * pathDensity U μ 3 + specMoment U μ 6 * pathDensity U μ 2 + specMoment U μ 7 * pathDensity U μ 1 + specMoment U μ 8 * pathDensity U μ 0) := by
    have h := pathDensity_succ hU 9
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, pathDensity_nine hU, pathDensity_eight hU, pathDensity_seven hU, pathDensity_six hU, pathDensity_five hU, pathDensity_four hU, pathDensity_three hU, pathDensity_two hU,
    show pathDensity U μ 1 = edgeDensity U μ from pathDensity_one hU, pathDensity_zero]
  ring

lemma pathDensity_eleven (hU : IsGraphon U μ) :
    pathDensity U μ 11 = edgeDensity U μ ^ 11 + 10 * edgeDensity U μ ^ 9 * specMoment U μ 0 + 9 * edgeDensity U μ ^ 8 * specMoment U μ 1 + 36 * edgeDensity U μ ^ 7 * specMoment U μ 0 ^ 2 + 8 * edgeDensity U μ ^ 7 * specMoment U μ 2 + 56 * edgeDensity U μ ^ 6 * specMoment U μ 0 * specMoment U μ 1 + 56 * edgeDensity U μ ^ 5 * specMoment U μ 0 ^ 3 + 7 * edgeDensity U μ ^ 6 * specMoment U μ 3 + 42 * edgeDensity U μ ^ 5 * specMoment U μ 0 * specMoment U μ 2 + 21 * edgeDensity U μ ^ 5 * specMoment U μ 1 ^ 2 + 105 * edgeDensity U μ ^ 4 * specMoment U μ 0 ^ 2 * specMoment U μ 1 + 35 * edgeDensity U μ ^ 3 * specMoment U μ 0 ^ 4 + 6 * edgeDensity U μ ^ 5 * specMoment U μ 4 + 30 * edgeDensity U μ ^ 4 * specMoment U μ 0 * specMoment U μ 3 + 30 * edgeDensity U μ ^ 4 * specMoment U μ 1 * specMoment U μ 2 + 60 * edgeDensity U μ ^ 3 * specMoment U μ 0 ^ 2 * specMoment U μ 2 + 60 * edgeDensity U μ ^ 3 * specMoment U μ 0 * specMoment U μ 1 ^ 2 + 60 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 3 * specMoment U μ 1 + 6 * edgeDensity U μ * specMoment U μ 0 ^ 5 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 5 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 0 * specMoment U μ 4 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 1 * specMoment U μ 3 + 10 * edgeDensity U μ ^ 3 * specMoment U μ 2 ^ 2 + 30 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 2 * specMoment U μ 3 + 60 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 2 + 10 * edgeDensity U μ ^ 2 * specMoment U μ 1 ^ 3 + 20 * edgeDensity U μ * specMoment U μ 0 ^ 3 * specMoment U μ 2 + 30 * edgeDensity U μ * specMoment U μ 0 ^ 2 * specMoment U μ 1 ^ 2 + 5 * specMoment U μ 0 ^ 4 * specMoment U μ 1 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 6 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 5 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 1 * specMoment U μ 4 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 2 * specMoment U μ 3 + 12 * edgeDensity U μ * specMoment U μ 0 ^ 2 * specMoment U μ 4 + 24 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 3 + 12 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 2 ^ 2 + 12 * edgeDensity U μ * specMoment U μ 1 ^ 2 * specMoment U μ 2 + 4 * specMoment U μ 0 ^ 3 * specMoment U μ 3 + 12 * specMoment U μ 0 ^ 2 * specMoment U μ 1 * specMoment U μ 2 + 4 * specMoment U μ 0 * specMoment U μ 1 ^ 3 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 7 + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 6 + 6 * edgeDensity U μ * specMoment U μ 1 * specMoment U μ 5 + 6 * edgeDensity U μ * specMoment U μ 2 * specMoment U μ 4 + 3 * edgeDensity U μ * specMoment U μ 3 ^ 2 + 3 * specMoment U μ 0 ^ 2 * specMoment U μ 5 + 6 * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 4 + 6 * specMoment U μ 0 * specMoment U μ 2 * specMoment U μ 3 + 3 * specMoment U μ 1 ^ 2 * specMoment U μ 3 + 3 * specMoment U μ 1 * specMoment U μ 2 ^ 2 + 2 * edgeDensity U μ * specMoment U μ 8 + 2 * specMoment U μ 0 * specMoment U μ 7 + 2 * specMoment U μ 1 * specMoment U μ 6 + 2 * specMoment U μ 2 * specMoment U μ 5 + 2 * specMoment U μ 3 * specMoment U μ 4 + specMoment U μ 9 := by
  have e : pathDensity U μ 11 = edgeDensity U μ * pathDensity U μ 10
      + (specMoment U μ 0 * pathDensity U μ 9 + specMoment U μ 1 * pathDensity U μ 8 + specMoment U μ 2 * pathDensity U μ 7 + specMoment U μ 3 * pathDensity U μ 6 + specMoment U μ 4 * pathDensity U μ 5 + specMoment U μ 5 * pathDensity U μ 4 + specMoment U μ 6 * pathDensity U μ 3 + specMoment U μ 7 * pathDensity U μ 2 + specMoment U μ 8 * pathDensity U μ 1 + specMoment U μ 9 * pathDensity U μ 0) := by
    have h := pathDensity_succ hU 10
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, pathDensity_ten hU, pathDensity_nine hU, pathDensity_eight hU, pathDensity_seven hU, pathDensity_six hU, pathDensity_five hU, pathDensity_four hU, pathDensity_three hU, pathDensity_two hU,
    show pathDensity U μ 1 = edgeDensity U μ from pathDensity_one hU, pathDensity_zero]
  ring

lemma pathDensity_twelve (hU : IsGraphon U μ) :
    pathDensity U μ 12 = edgeDensity U μ ^ 12 + 11 * edgeDensity U μ ^ 10 * specMoment U μ 0 + 10 * edgeDensity U μ ^ 9 * specMoment U μ 1 + 45 * edgeDensity U μ ^ 8 * specMoment U μ 0 ^ 2 + 9 * edgeDensity U μ ^ 8 * specMoment U μ 2 + 72 * edgeDensity U μ ^ 7 * specMoment U μ 0 * specMoment U μ 1 + 84 * edgeDensity U μ ^ 6 * specMoment U μ 0 ^ 3 + 8 * edgeDensity U μ ^ 7 * specMoment U μ 3 + 56 * edgeDensity U μ ^ 6 * specMoment U μ 0 * specMoment U μ 2 + 28 * edgeDensity U μ ^ 6 * specMoment U μ 1 ^ 2 + 168 * edgeDensity U μ ^ 5 * specMoment U μ 0 ^ 2 * specMoment U μ 1 + 70 * edgeDensity U μ ^ 4 * specMoment U μ 0 ^ 4 + 7 * edgeDensity U μ ^ 6 * specMoment U μ 4 + 42 * edgeDensity U μ ^ 5 * specMoment U μ 0 * specMoment U μ 3 + 42 * edgeDensity U μ ^ 5 * specMoment U μ 1 * specMoment U μ 2 + 105 * edgeDensity U μ ^ 4 * specMoment U μ 0 ^ 2 * specMoment U μ 2 + 105 * edgeDensity U μ ^ 4 * specMoment U μ 0 * specMoment U μ 1 ^ 2 + 140 * edgeDensity U μ ^ 3 * specMoment U μ 0 ^ 3 * specMoment U μ 1 + 21 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 5 + 6 * edgeDensity U μ ^ 5 * specMoment U μ 5 + 30 * edgeDensity U μ ^ 4 * specMoment U μ 0 * specMoment U μ 4 + 30 * edgeDensity U μ ^ 4 * specMoment U μ 1 * specMoment U μ 3 + 15 * edgeDensity U μ ^ 4 * specMoment U μ 2 ^ 2 + 60 * edgeDensity U μ ^ 3 * specMoment U μ 0 ^ 2 * specMoment U μ 3 + 120 * edgeDensity U μ ^ 3 * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 2 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 1 ^ 3 + 60 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 3 * specMoment U μ 2 + 90 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 2 * specMoment U μ 1 ^ 2 + 30 * edgeDensity U μ * specMoment U μ 0 ^ 4 * specMoment U μ 1 + specMoment U μ 0 ^ 6 + 5 * edgeDensity U μ ^ 4 * specMoment U μ 6 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 0 * specMoment U μ 5 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 1 * specMoment U μ 4 + 20 * edgeDensity U μ ^ 3 * specMoment U μ 2 * specMoment U μ 3 + 30 * edgeDensity U μ ^ 2 * specMoment U μ 0 ^ 2 * specMoment U μ 4 + 60 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 3 + 30 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 2 ^ 2 + 30 * edgeDensity U μ ^ 2 * specMoment U μ 1 ^ 2 * specMoment U μ 2 + 20 * edgeDensity U μ * specMoment U μ 0 ^ 3 * specMoment U μ 3 + 60 * edgeDensity U μ * specMoment U μ 0 ^ 2 * specMoment U μ 1 * specMoment U μ 2 + 20 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 1 ^ 3 + 5 * specMoment U μ 0 ^ 4 * specMoment U μ 2 + 10 * specMoment U μ 0 ^ 3 * specMoment U μ 1 ^ 2 + 4 * edgeDensity U μ ^ 3 * specMoment U μ 7 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 0 * specMoment U μ 6 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 1 * specMoment U μ 5 + 12 * edgeDensity U μ ^ 2 * specMoment U μ 2 * specMoment U μ 4 + 6 * edgeDensity U μ ^ 2 * specMoment U μ 3 ^ 2 + 12 * edgeDensity U μ * specMoment U μ 0 ^ 2 * specMoment U μ 5 + 24 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 4 + 24 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 2 * specMoment U μ 3 + 12 * edgeDensity U μ * specMoment U μ 1 ^ 2 * specMoment U μ 3 + 12 * edgeDensity U μ * specMoment U μ 1 * specMoment U μ 2 ^ 2 + 4 * specMoment U μ 0 ^ 3 * specMoment U μ 4 + 12 * specMoment U μ 0 ^ 2 * specMoment U μ 1 * specMoment U μ 3 + 6 * specMoment U μ 0 ^ 2 * specMoment U μ 2 ^ 2 + 12 * specMoment U μ 0 * specMoment U μ 1 ^ 2 * specMoment U μ 2 + specMoment U μ 1 ^ 4 + 3 * edgeDensity U μ ^ 2 * specMoment U μ 8 + 6 * edgeDensity U μ * specMoment U μ 0 * specMoment U μ 7 + 6 * edgeDensity U μ * specMoment U μ 1 * specMoment U μ 6 + 6 * edgeDensity U μ * specMoment U μ 2 * specMoment U μ 5 + 6 * edgeDensity U μ * specMoment U μ 3 * specMoment U μ 4 + 3 * specMoment U μ 0 ^ 2 * specMoment U μ 6 + 6 * specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 5 + 6 * specMoment U μ 0 * specMoment U μ 2 * specMoment U μ 4 + 3 * specMoment U μ 0 * specMoment U μ 3 ^ 2 + 3 * specMoment U μ 1 ^ 2 * specMoment U μ 4 + 6 * specMoment U μ 1 * specMoment U μ 2 * specMoment U μ 3 + specMoment U μ 2 ^ 3 + 2 * edgeDensity U μ * specMoment U μ 9 + 2 * specMoment U μ 0 * specMoment U μ 8 + 2 * specMoment U μ 1 * specMoment U μ 7 + 2 * specMoment U μ 2 * specMoment U μ 6 + 2 * specMoment U μ 3 * specMoment U μ 5 + specMoment U μ 4 ^ 2 + specMoment U μ 10 := by
  have e : pathDensity U μ 12 = edgeDensity U μ * pathDensity U μ 11
      + (specMoment U μ 0 * pathDensity U μ 10 + specMoment U μ 1 * pathDensity U μ 9 + specMoment U μ 2 * pathDensity U μ 8 + specMoment U μ 3 * pathDensity U μ 7 + specMoment U μ 4 * pathDensity U μ 6 + specMoment U μ 5 * pathDensity U μ 5 + specMoment U μ 6 * pathDensity U μ 4 + specMoment U μ 7 * pathDensity U μ 3 + specMoment U μ 8 * pathDensity U μ 2 + specMoment U μ 9 * pathDensity U μ 1 + specMoment U μ 10 * pathDensity U μ 0) := by
    have h := pathDensity_succ hU 11
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, pathDensity_eleven hU, pathDensity_ten hU, pathDensity_nine hU, pathDensity_eight hU, pathDensity_seven hU, pathDensity_six hU, pathDensity_five hU, pathDensity_four hU, pathDensity_three hU, pathDensity_two hU,
    show pathDensity U μ 1 = edgeDensity U μ from pathDensity_one hU, pathDensity_zero]
  ring

end OddCycleBound
