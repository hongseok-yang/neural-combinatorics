import OddCycleBound.Necklace

/-!
# The general-`m` necklace identity

`Necklace.lean` proves the cyclic-complement-trace identity only for the hand-unrolled cases
`complTrace5_necklace` / `complTrace7_necklace`.  Here we prove it once and for all, for every cycle
length, by telescoping the general recursion `mixedTrace_succ` / `mixedTrace_zero` already established there.

The core is `mixedTrace_telescope`, a closed form for `mixedTrace a b` as an alternating sum of the
inner products `pairing (pathIter j) (complIter k)` plus the boundary term `mixedTrace (a+b) 0`.  Specialising
`a = 0`, `b = n` and feeding the peel `complTrace_peel` / `doubleMean_complPow` gives `complTrace_necklace`:

  `trace (complᵒ⁽ⁿ⁺¹⁾) = Σ_{j=0}^{n} (−1)ʲ ⟨pathIter j, complIter (n+1−j)⟩
                     + (−1)ⁿ⁺¹ (x_{n+1} − c_{n+1})`,

with `x_{n+1} = pathDensity (n+1)` the path density and `c_{n+1} = trace (Uᵒ⁽ⁿ⁺¹⁾)` the cycle density.
The hand-unrolled `complTrace5/7_necklace` are recovered as corollaries (regression check).
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- The `j = 0` inner product is just the mean: `⟨pathIter 0, v⟩ = ⟨1, v⟩ = mean v`. -/
lemma pairing_pathIter_zero (v : Ω → ℝ) : pairing μ (pathIter U μ 0) v = mean μ v := by
  simp only [pairing, pathIter, one_mul, mean]

/-- **Telescoping of `mixedTrace`.**  For all `b a`,
`mixedTrace a b = Σ_{i<b} (−1)ⁱ ⟨pathIter (a+1+i), complIter (b−i)⟩ + (−1)ᵇ mixedTrace (a+b) 0`. -/
lemma mixedTrace_telescope (hU : IsGraphon U μ) : ∀ (b a : ℕ),
    mixedTrace U μ a b
      = (∑ i ∈ Finset.range b,
          (-1 : ℝ) ^ i * pairing μ (pathIter U μ (a + 1 + i)) (complIter U μ (b - i)))
        + (-1 : ℝ) ^ b * mixedTrace U μ (a + b) 0 := by
  intro b
  induction b with
  | zero => intro a; simp
  | succ b ih =>
      intro a
      have hsum : ∀ i ∈ Finset.range b,
          (-1 : ℝ) ^ (i + 1) * pairing μ (pathIter U μ (a + 1 + (i + 1))) (complIter U μ (b + 1 - (i + 1)))
            = -((-1 : ℝ) ^ i * pairing μ (pathIter U μ (a + 1 + 1 + i)) (complIter U μ (b - i))) := by
        intro i _
        have e1 : a + 1 + (i + 1) = a + 1 + 1 + i := by omega
        have e2 : b + 1 - (i + 1) = b - i := Nat.succ_sub_succ b i
        rw [e1, e2, pow_succ]; ring
      rw [mixedTrace_succ hU a b, ih (a + 1),
        Finset.sum_range_succ' (fun i =>
          (-1 : ℝ) ^ i * pairing μ (pathIter U μ (a + 1 + i)) (complIter U μ (b + 1 - i))) b,
        Finset.sum_congr rfl hsum, Finset.sum_neg_distrib]
      have eb : a + 1 + b = a + (b + 1) := by omega
      rw [eb, pow_succ]
      simp only [pow_zero, one_mul, Nat.sub_zero, zero_add, Nat.add_zero]
      ring

/-- **The general-`m` necklace identity.**  For every `n`,
`trace (complᵒ⁽ⁿ⁺¹⁾) = Σ_{j=0}^{n} (−1)ʲ ⟨pathIter j, complIter (n+1−j)⟩ + (−1)ⁿ⁺¹ (x_{n+1} − c_{n+1})`. -/
lemma complTrace_necklace (hU : IsGraphon U μ) (n : ℕ) :
    trace μ (compPow μ (compl U) (n + 1))
      = (∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * pairing μ (pathIter U μ j) (complIter U μ (n + 1 - j)))
        + (-1 : ℝ) ^ (n + 1) * (pathDensity U μ (n + 1) - trace μ (compPow μ U (n + 1))) := by
  rw [complTrace_peel hU n, doubleMean_complPow hU n, mixedTrace_telescope hU n 0]
  simp only [Nat.zero_add]
  rw [mixedTrace_zero hU n,
    Finset.sum_range_succ' (fun j =>
      (-1 : ℝ) ^ j * pairing μ (pathIter U μ j) (complIter U μ (n + 1 - j))) n,
    pairing_pathIter_zero]
  have hsum : ∀ i ∈ Finset.range n,
      (-1 : ℝ) ^ (i + 1) * pairing μ (pathIter U μ (i + 1)) (complIter U μ (n + 1 - (i + 1)))
        = -((-1 : ℝ) ^ i * pairing μ (pathIter U μ (1 + i)) (complIter U μ (n - i))) := by
    intro i _
    have e1 : (1 : ℕ) + i = i + 1 := by omega
    have e2 : n + 1 - (i + 1) = n - i := Nat.succ_sub_succ n i
    rw [e1, e2, pow_succ]; ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_neg_distrib, pow_succ]
  simp only [Nat.sub_zero]
  ring

/-! ### Regression: the hand-unrolled `ccomp5/7_necklace` are special cases -/

example (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 4)
      = mean μ (complIter U μ 4) - pairing μ (pathIter U μ 1) (complIter U μ 3)
        + pairing μ (pathIter U μ 2) (complIter U μ 2) - pairing μ (pathIter U μ 3) (complIter U μ 1)
        + pathDensity U μ 4 - trace μ (compPow μ U 4) := by
  have h := complTrace_necklace hU 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pairing_pathIter_zero] at h
  norm_num at h
  rw [h]; ring

example (hU : IsGraphon U μ) :
    trace μ (compPow μ (compl U) 6)
      = mean μ (complIter U μ 6) - pairing μ (pathIter U μ 1) (complIter U μ 5)
        + pairing μ (pathIter U μ 2) (complIter U μ 4) - pairing μ (pathIter U μ 3) (complIter U μ 3)
        + pairing μ (pathIter U μ 4) (complIter U μ 2) - pairing μ (pathIter U μ 5) (complIter U μ 1)
        + pathDensity U μ 6 - trace μ (compPow μ U 6) := by
  have h := complTrace_necklace hU 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pairing_pathIter_zero] at h
  norm_num at h
  rw [h]; ring

end OddCycleBound
