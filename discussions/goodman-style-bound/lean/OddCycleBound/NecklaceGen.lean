import OddCycleBound.Necklace

/-!
# The general-`m` necklace identity

`Necklace.lean` proves the cyclic-complement-trace identity only for the hand-unrolled cases
`ccomp5_necklace` / `ccomp7_necklace`.  Here we prove it once and for all, for every cycle
length, by telescoping the general recursion `Htr_succ` / `Htr_zero` already established there.

The core is `Htr_telescope`, a closed form for `Htr a b` as an alternating sum of the
inner products `ip (pathFun j) (vcomp k)` plus the boundary term `Htr (a+b) 0`.  Specialising
`a = 0`, `b = n` and feeding the peel `ccomp_peel` / `dmean_Wpow` gives `ccomp_necklace`:

  `tr (Wkᵒ⁽ⁿ⁺¹⁾) = Σ_{j=0}^{n} (−1)ʲ ⟨pathFun j, vcomp (n+1−j)⟩
                     + (−1)ⁿ⁺¹ (x_{n+1} − c_{n+1})`,

with `x_{n+1} = xden (n+1)` the path density and `c_{n+1} = tr (Uᵒ⁽ⁿ⁺¹⁾)` the cycle density.
The hand-unrolled `ccomp5/7_necklace` are recovered as corollaries (regression check).
-/

open MeasureTheory

namespace OddCycleBound.Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- The `j = 0` inner product is just the mean: `⟨pathFun 0, v⟩ = ⟨1, v⟩ = mean v`. -/
lemma ip_pathFun_zero (v : Ω → ℝ) : ip μ (pathFun U μ 0) v = mean μ v := by
  simp only [ip, pathFun, one_mul, mean]

/-- **Telescoping of `Htr`.**  For all `b a`,
`Htr a b = Σ_{i<b} (−1)ⁱ ⟨pathFun (a+1+i), vcomp (b−i)⟩ + (−1)ᵇ Htr (a+b) 0`. -/
lemma Htr_telescope (hU : IsGraphon U μ) : ∀ (b a : ℕ),
    Htr U μ a b
      = (∑ i ∈ Finset.range b,
          (-1 : ℝ) ^ i * ip μ (pathFun U μ (a + 1 + i)) (vcomp U μ (b - i)))
        + (-1 : ℝ) ^ b * Htr U μ (a + b) 0 := by
  intro b
  induction b with
  | zero => intro a; simp
  | succ b ih =>
      intro a
      have hsum : ∀ i ∈ Finset.range b,
          (-1 : ℝ) ^ (i + 1) * ip μ (pathFun U μ (a + 1 + (i + 1))) (vcomp U μ (b + 1 - (i + 1)))
            = -((-1 : ℝ) ^ i * ip μ (pathFun U μ (a + 1 + 1 + i)) (vcomp U μ (b - i))) := by
        intro i _
        have e1 : a + 1 + (i + 1) = a + 1 + 1 + i := by omega
        have e2 : b + 1 - (i + 1) = b - i := Nat.succ_sub_succ b i
        rw [e1, e2, pow_succ]; ring
      rw [Htr_succ hU a b, ih (a + 1),
        Finset.sum_range_succ' (fun i =>
          (-1 : ℝ) ^ i * ip μ (pathFun U μ (a + 1 + i)) (vcomp U μ (b + 1 - i))) b,
        Finset.sum_congr rfl hsum, Finset.sum_neg_distrib]
      have eb : a + 1 + b = a + (b + 1) := by omega
      rw [eb, pow_succ]
      simp only [pow_zero, one_mul, Nat.sub_zero, zero_add, Nat.add_zero]
      ring

/-- **The general-`m` necklace identity.**  For every `n`,
`tr (Wkᵒ⁽ⁿ⁺¹⁾) = Σ_{j=0}^{n} (−1)ʲ ⟨pathFun j, vcomp (n+1−j)⟩ + (−1)ⁿ⁺¹ (x_{n+1} − c_{n+1})`. -/
lemma ccomp_necklace (hU : IsGraphon U μ) (n : ℕ) :
    tr μ (Kpow μ (Wk U) (n + 1))
      = (∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * ip μ (pathFun U μ j) (vcomp U μ (n + 1 - j)))
        + (-1 : ℝ) ^ (n + 1) * (xden U μ (n + 1) - tr μ (Kpow μ U (n + 1))) := by
  rw [ccomp_peel hU n, dmean_Wpow hU n, Htr_telescope hU n 0]
  simp only [Nat.zero_add]
  rw [Htr_zero hU n,
    Finset.sum_range_succ' (fun j =>
      (-1 : ℝ) ^ j * ip μ (pathFun U μ j) (vcomp U μ (n + 1 - j))) n,
    ip_pathFun_zero]
  have hsum : ∀ i ∈ Finset.range n,
      (-1 : ℝ) ^ (i + 1) * ip μ (pathFun U μ (i + 1)) (vcomp U μ (n + 1 - (i + 1)))
        = -((-1 : ℝ) ^ i * ip μ (pathFun U μ (1 + i)) (vcomp U μ (n - i))) := by
    intro i _
    have e1 : (1 : ℕ) + i = i + 1 := by omega
    have e2 : n + 1 - (i + 1) = n - i := Nat.succ_sub_succ n i
    rw [e1, e2, pow_succ]; ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_neg_distrib, pow_succ]
  simp only [Nat.sub_zero]
  ring

/-! ### Regression: the hand-unrolled `ccomp5/7_necklace` are special cases -/

example (hU : IsGraphon U μ) :
    tr μ (Kpow μ (Wk U) 4)
      = mean μ (vcomp U μ 4) - ip μ (pathFun U μ 1) (vcomp U μ 3)
        + ip μ (pathFun U μ 2) (vcomp U μ 2) - ip μ (pathFun U μ 3) (vcomp U μ 1)
        + xden U μ 4 - tr μ (Kpow μ U 4) := by
  have h := ccomp_necklace hU 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ip_pathFun_zero] at h
  norm_num at h
  rw [h]; ring

example (hU : IsGraphon U μ) :
    tr μ (Kpow μ (Wk U) 6)
      = mean μ (vcomp U μ 6) - ip μ (pathFun U μ 1) (vcomp U μ 5)
        + ip μ (pathFun U μ 2) (vcomp U μ 4) - ip μ (pathFun U μ 3) (vcomp U μ 3)
        + ip μ (pathFun U μ 4) (vcomp U μ 2) - ip μ (pathFun U μ 5) (vcomp U μ 1)
        + xden U μ 6 - tr μ (Kpow μ U 6) := by
  have h := ccomp_necklace hU 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ip_pathFun_zero] at h
  norm_num at h
  rw [h]; ring

end OddCycleBound.Graphon
