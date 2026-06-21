import OddCycleBound.Necklace

/-!
# A general-`m` path-density recurrence

`PathDensity.lean` proves the path-density formulae `x₂ … x₆` by hand, one explicit
`decompₙ`/`xdenₙ` lemma at a time.  Here we prove the **general recurrence** once, by a scalar
inner-product argument that avoids any function-valued (`Pi`) sum plumbing:

  `x_{n+1} = q·xₙ + Σ_{i<n} sᵢ·x_{n−1−i}`.

The engine is the family `W k n = ⟨hₖ, Tⁿ1⟩`, which satisfies
`W k 0 = 0`, `W k (n+1) = sₖ·xₙ + W (k+1) n`, hence
`W k n = Σ_{i<n} s_{k+i}·x_{n−1−i}`; specialising `k = 0` and using
`x_{n+1} = q·xₙ + W 0 n` gives the recurrence.  From it `x₇, x₈` (and later `x₉ … x₁₂`)
follow mechanically.  The closed forms are exactly Lemma 2.4 of `paper.tex`.
-/

open MeasureTheory

namespace OddCycleBound.Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- `x₀ = mean 1 = 1`. -/
lemma xden_zero : xden U μ 0 = 1 := by rw [xden]; exact mean_one

/-- **(A)** `x_{n+1} = q·xₙ + ⟨h₀, Tⁿ1⟩` (`h₀ = g`), via self-adjointness of `T`. -/
lemma xden_succ_aux (hU : IsGraphon U μ) (n : ℕ) :
    xden U μ (n + 1) = qval U μ * xden U μ n + ip μ (hseq U μ 0) (pathFun U μ n) := by
  have e1 : mean μ (T U μ (pathFun U μ n)) = ∫ x, pathFun U μ n x * deg U μ x ∂μ := by
    show ∫ x, T U μ (pathFun U μ n) x ∂μ = _
    rw [show (∫ x, T U μ (pathFun U μ n) x ∂μ) = ∫ x, T U μ (pathFun U μ n) x * 1 ∂μ from by simp,
      T_selfadj hU (good_pathFun hU n) good_one, T_one hU]
  show mean μ (T U μ (pathFun U μ n)) = _
  rw [e1]
  have e2 : ∀ x, pathFun U μ n x * deg U μ x
      = qval U μ * pathFun U μ n x + pathFun U μ n x * hseq U μ 0 x := fun x => by
    rw [deg_eq']; ring
  rw [integral_congr_ae (ae_of_all _ e2),
    integral_add ((good_pathFun hU n).integrable.const_mul _)
      ((good_pathFun hU n).mul (good_h hU 0)).integrable,
    integral_const_mul]
  congr 1
  show ∫ x, pathFun U μ n x * hseq U μ 0 x ∂μ = ip μ (hseq U μ 0) (pathFun U μ n)
  simp only [ip]; exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- **(C)** `⟨hₖ, T⁰1⟩ = ⟨hₖ, 1⟩ = mean hₖ = 0`. -/
lemma ip_hseq_pathFun_zero (hU : IsGraphon U μ) (k : ℕ) :
    ip μ (hseq U μ k) (pathFun U μ 0) = 0 := by
  show ∫ x, hseq U μ k x * pathFun U μ 0 x ∂μ = 0
  rw [integral_congr_ae (ae_of_all _ fun x => by
    show hseq U μ k x * pathFun U μ 0 x = hseq U μ k x; show hseq U μ k x * 1 = _; ring)]
  exact mean_h hU k

/-- **(B)** `⟨hₖ, T^{n+1}1⟩ = sₖ·xₙ + ⟨h_{k+1}, Tⁿ1⟩`. -/
lemma ip_hseq_pathFun_succ (hU : IsGraphon U μ) (k n : ℕ) :
    ip μ (hseq U μ k) (pathFun U μ (n + 1))
      = smom U μ k * xden U μ n + ip μ (hseq U μ (k + 1)) (pathFun U μ n) := by
  have hT : ip μ (hseq U μ k) (pathFun U μ (n + 1))
      = ∫ x, T U μ (hseq U μ k) x * pathFun U μ n x ∂μ := by
    show ∫ x, hseq U μ k x * T U μ (pathFun U μ n) x ∂μ = _
    exact (T_selfadj hU (good_h hU k) (good_pathFun hU n)).symm
  rw [hT]
  have e : ∀ x, T U μ (hseq U μ k) x * pathFun U μ n x
      = smom U μ k * pathFun U μ n x + hseq U μ (k + 1) x * pathFun U μ n x := fun x => by
    rw [T_hseq' hU k]; ring
  rw [integral_congr_ae (ae_of_all _ e),
    integral_add ((good_pathFun hU n).integrable.const_mul _)
      ((good_h hU (k + 1)).mul (good_pathFun hU n)).integrable,
    integral_const_mul]
  rfl

/-- **(D)** the closed form `⟨hₖ, Tⁿ1⟩ = Σ_{i<n} s_{k+i}·x_{n−1−i}`. -/
lemma ip_hseq_pathFun_closed (hU : IsGraphon U μ) : ∀ (n k : ℕ),
    ip μ (hseq U μ k) (pathFun U μ n)
      = ∑ i ∈ Finset.range n, smom U μ (k + i) * xden U μ (n - 1 - i) := by
  intro n
  induction n with
  | zero => intro k; simp [ip_hseq_pathFun_zero hU k]
  | succ n ih =>
      intro k
      rw [ip_hseq_pathFun_succ hU k n, ih (k + 1),
        Finset.sum_range_succ' (fun i => smom U μ (k + i) * xden U μ (n + 1 - 1 - i)) n]
      have hcong : ∀ i ∈ Finset.range n,
          smom U μ (k + (i + 1)) * xden U μ (n + 1 - 1 - (i + 1))
            = smom U μ (k + 1 + i) * xden U μ (n - 1 - i) := by
        intro i _
        have a1 : k + (i + 1) = k + 1 + i := by omega
        have a2 : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
        rw [a1, a2]
      rw [Finset.sum_congr rfl hcong]
      have b1 : n + 1 - 1 - 0 = n := by omega
      simp only [Nat.add_zero, b1]
      ring

/-- **The general path-density recurrence** `x_{n+1} = q·xₙ + Σ_{i<n} sᵢ·x_{n−1−i}`. -/
lemma xden_succ (hU : IsGraphon U μ) (n : ℕ) :
    xden U μ (n + 1)
      = qval U μ * xden U μ n + ∑ i ∈ Finset.range n, smom U μ i * xden U μ (n - 1 - i) := by
  rw [xden_succ_aux hU n, ip_hseq_pathFun_closed hU n 0]
  simp only [Nat.zero_add]

/-! ### `x₇, x₈` (needed for `C₉`), as instances of the recurrence -/

lemma xden_seven (hU : IsGraphon U μ) :
    xden U μ 7 = qval U μ ^ 7 + 6 * qval U μ ^ 5 * smom U μ 0 + 5 * qval U μ ^ 4 * smom U μ 1
      + 10 * qval U μ ^ 3 * smom U μ 0 ^ 2 + 4 * qval U μ ^ 3 * smom U μ 2
      + 12 * qval U μ ^ 2 * smom U μ 0 * smom U μ 1 + 3 * qval U μ ^ 2 * smom U μ 3
      + 4 * qval U μ * smom U μ 0 ^ 3 + 6 * qval U μ * smom U μ 0 * smom U μ 2
      + 3 * qval U μ * smom U μ 1 ^ 2 + 2 * qval U μ * smom U μ 4
      + 3 * smom U μ 0 ^ 2 * smom U μ 1 + 2 * smom U μ 0 * smom U μ 3
      + 2 * smom U μ 1 * smom U μ 2 + smom U μ 5 := by
  have e : xden U μ 7 = qval U μ * xden U μ 6
      + (smom U μ 0 * xden U μ 5 + smom U μ 1 * xden U μ 4 + smom U μ 2 * xden U μ 3
        + smom U μ 3 * xden U μ 2 + smom U μ 4 * xden U μ 1 + smom U μ 5 * xden U μ 0) := by
    have h := xden_succ hU 6
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, xden_six hU, xden_five hU, xden_four hU, xden_three hU, xden_two hU,
    show xden U μ 1 = qval U μ from xden_one hU, xden_zero]
  ring

lemma xden_eight (hU : IsGraphon U μ) :
    xden U μ 8 = qval U μ ^ 8 + 7 * qval U μ ^ 6 * smom U μ 0 + 6 * qval U μ ^ 5 * smom U μ 1
      + 15 * qval U μ ^ 4 * smom U μ 0 ^ 2 + 5 * qval U μ ^ 4 * smom U μ 2
      + 20 * qval U μ ^ 3 * smom U μ 0 * smom U μ 1 + 4 * qval U μ ^ 3 * smom U μ 3
      + 10 * qval U μ ^ 2 * smom U μ 0 ^ 3 + 12 * qval U μ ^ 2 * smom U μ 0 * smom U μ 2
      + 6 * qval U μ ^ 2 * smom U μ 1 ^ 2 + 3 * qval U μ ^ 2 * smom U μ 4
      + 12 * qval U μ * smom U μ 0 ^ 2 * smom U μ 1 + 6 * qval U μ * smom U μ 0 * smom U μ 3
      + 6 * qval U μ * smom U μ 1 * smom U μ 2 + 2 * qval U μ * smom U μ 5
      + smom U μ 0 ^ 4 + 3 * smom U μ 0 ^ 2 * smom U μ 2 + 3 * smom U μ 0 * smom U μ 1 ^ 2
      + 2 * smom U μ 0 * smom U μ 4 + 2 * smom U μ 1 * smom U μ 3 + smom U μ 2 ^ 2 + smom U μ 6 := by
  have e : xden U μ 8 = qval U μ * xden U μ 7
      + (smom U μ 0 * xden U μ 6 + smom U μ 1 * xden U μ 5 + smom U μ 2 * xden U μ 4
        + smom U μ 3 * xden U μ 3 + smom U μ 4 * xden U μ 2 + smom U μ 5 * xden U μ 1
        + smom U μ 6 * xden U μ 0) := by
    have h := xden_succ hU 7
    simpa [Finset.sum_range_succ, Finset.sum_range_zero] using h
  rw [e, xden_seven hU, xden_six hU, xden_five hU, xden_four hU, xden_three hU, xden_two hU,
    show xden U μ 1 = qval U μ from xden_one hU, xden_zero]
  ring

end OddCycleBound.Graphon
