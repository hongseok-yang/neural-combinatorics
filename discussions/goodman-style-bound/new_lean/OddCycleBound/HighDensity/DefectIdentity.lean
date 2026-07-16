/-
# High-density theorem — graphon defect identities (E5b)

This file removes graphon syntax from the remaining E5b coefficient calculation in two steps:

* collapse the triangular double sum in `neckSum_pathDensity` to one convolution;
* identify every graphon path density with the universal recurrence driven by its edge density and
  compression moments.

The remaining E5b core is therefore a finite identity between `pathMoment` and `momentPhi`.
-/

import OddCycleBound.HighDensity.MomentExpansion
import OddCycleBound.HighDensity.Expansion

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.HighDensity

/-! ## A triangular-sum reindexing lemma -/

/-- Summing a function of `j+i` over the triangle `j+i ≤ N` gives `k+1` copies at level `k`. -/
lemma sum_triangle_add (F : ℕ → ℝ) : ∀ N : ℕ,
    (∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N + 1 - j), F (j + i)) =
      ∑ k ∈ Finset.range (N + 1), (k + 1 : ℕ) * F k
  | N => by
      calc
        (∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N + 1 - j), F (j + i)) =
            ∑ k ∈ Finset.range (N + 1), ∑ _j ∈ Finset.range (k + 1), F k := by
          rw [Finset.sum_sigma', Finset.sum_sigma']
          refine Finset.sum_nbij' (fun p => ⟨p.1 + p.2, p.1⟩)
            (fun p => ⟨p.2, p.1 - p.2⟩) ?_ ?_ ?_ ?_ ?_
          · rintro ⟨j, i⟩ hp
            simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
            omega
          · rintro ⟨k, j⟩ hp
            simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
            omega
          · rintro ⟨j, i⟩ hp
            simp only [Finset.mem_sigma, Finset.mem_range] at hp
            show (⟨j, j + i - j⟩ : Σ _ : ℕ, ℕ) = ⟨j, i⟩
            rw [show j + i - j = i by omega]
          · rintro ⟨k, j⟩ hp
            simp only [Finset.mem_sigma, Finset.mem_range] at hp
            show (⟨j + (k - j), j⟩ : Σ _ : ℕ, ℕ) = ⟨k, j⟩
            rw [show j + (k - j) = k by omega]
          · rintro ⟨j, i⟩ _
            rfl
        _ = ∑ k ∈ Finset.range (N + 1), (k + 1 : ℕ) * F k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → ℝ}

/-- **Single-convolution form of the necklace sum.**  For odd `m ≥ 3`, the triangular sum from
`neckSum_pathDensity` has `b+1` identical terms on each diagonal `j+i=b`; its terminal contribution
is `(m-1)·t(P_{m-1},1-W)`. -/
lemma neckSum_pathDensity_single_sum (hW : IsGraphon W mu) {m : ℕ}
    (hm : Odd m) (hm3 : 3 ≤ m) :
    neckSum W mu m =
      (m - 1 : ℕ) * pathDensity (compl W) mu (m - 1) +
        ∑ b ∈ Finset.range (m - 1),
          (b + 1 : ℕ) * ((-1 : ℝ) ^ b *
            (pathDensity W mu (m - 2 - b) * pathDensity (compl W) mu b)) := by
  rw [neckSum_pathDensity hW]
  have hm2 : 2 ≤ m := by omega
  have hev : Even (m - 1) := by
    rcases hm with ⟨t, rfl⟩
    exact ⟨t, by omega⟩
  have hsplit :
      (∑ j ∈ Finset.range (m - 1),
          (-1 : ℝ) ^ j *
            ((∑ i ∈ Finset.range (m - 1 - j),
                (-1 : ℝ) ^ i *
                  (pathDensity W mu (m - 1 - j - 1 - i) *
                    pathDensity (compl W) mu (j + i))) +
              (-1 : ℝ) ^ (m - 1 - j) * pathDensity (compl W) mu (j + (m - 1 - j)))) =
        (∑ j ∈ Finset.range (m - 1),
          ∑ i ∈ Finset.range (m - 1 - j),
            (-1 : ℝ) ^ (j + i) *
              (pathDensity W mu (m - 2 - (j + i)) *
                pathDensity (compl W) mu (j + i))) +
          (m - 1 : ℕ) * pathDensity (compl W) mu (m - 1) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hsign :
          (-1 : ℝ) ^ j * (-1 : ℝ) ^ i = (-1 : ℝ) ^ (j + i) := by
        exact (pow_add (-1 : ℝ) j i).symm
      rw [← mul_assoc, hsign]
      have hidx : m - 1 - j - 1 - i = m - 2 - (j + i) := by
        simp only [Nat.sub_sub]
        congr 1
        omega
      rw [hidx]
    · have hterm : ∀ j ∈ Finset.range (m - 1),
          (-1 : ℝ) ^ j *
              ((-1 : ℝ) ^ (m - 1 - j) * pathDensity (compl W) mu (j + (m - 1 - j))) =
            pathDensity (compl W) mu (m - 1) := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hsign :
            (-1 : ℝ) ^ j * (-1 : ℝ) ^ (m - 1 - j) = 1 := by
          rw [← pow_add, show j + (m - 1 - j) = m - 1 by omega,
            hev.neg_one_pow]
        rw [← mul_assoc, hsign, one_mul,
          show j + (m - 1 - j) = m - 1 by omega]
      calc
        (∑ j ∈ Finset.range (m - 1),
            (-1 : ℝ) ^ j *
              ((-1 : ℝ) ^ (m - 1 - j) *
                pathDensity (compl W) mu (j + (m - 1 - j)))) =
            ∑ _j ∈ Finset.range (m - 1), pathDensity (compl W) mu (m - 1) := by
              exact Finset.sum_congr rfl hterm
        _ = (m - 1 : ℕ) * pathDensity (compl W) mu (m - 1) := by simp
  rw [hsplit]
  have htri := sum_triangle_add (fun b =>
    (-1 : ℝ) ^ b *
      (pathDensity W mu (m - 2 - b) * pathDensity (compl W) mu b)) (m - 2)
  rw [show m - 2 + 1 = m - 1 by omega] at htri
  rw [htri]
  ring

/-! ## Universal path recurrence -/

/-- The path-density sequence determined by hub density `q` and compression moments `s`. -/
def pathMoment (q : ℝ) (s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => q * pathMoment q s n +
      ∑ i ∈ Finset.range n, s i * pathMoment q s (n - 1 - i)

@[simp] lemma pathMoment_zero (q : ℝ) (s : ℕ → ℝ) : pathMoment q s 0 = 1 := by
  simp [pathMoment]

lemma pathMoment_succ (q : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    pathMoment q s (n + 1) = q * pathMoment q s n +
      ∑ i ∈ Finset.range n, s i * pathMoment q s (n - 1 - i) := by
  simp [pathMoment]

/-- Every graphon path density is the universal path recurrence evaluated at its edge density and
compression moments. -/
lemma pathDensity_eq_pathMoment (hW : IsGraphon W mu) (n : ℕ) :
    pathDensity W mu n = pathMoment (edgeDensity W mu) (specMoment W mu) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [pathDensity_zero]
      | succ n =>
          rw [pathDensity_succ hW n, pathMoment_succ]
          rw [ih n (by omega)]
          refine congrArg (edgeDensity W mu * pathMoment (edgeDensity W mu) (specMoment W mu) n + ·)
            (Finset.sum_congr rfl fun i hi => ?_)
          rw [Finset.mem_range] at hi
          rw [ih (n - 1 - i) (by omega)]

/-- Reversing the complement parity: the moments of `W` are the alternating moments of `1-W`. -/
lemma specMoment_eq_sign_mul_compl (hW : IsGraphon W mu) (j : ℕ) :
    specMoment W mu j = (-1 : ℝ) ^ j * specMoment (compl W) mu j := by
  have hcc : compl (compl W) = W := by
    funext x y
    simp only [compl]
    ring
  simpa only [hcc] using specMoment_compl (isGraphon_compl hW) j

/-! ## The graphon defect as a universal finite-sequence expression -/

/-- Alternating a moment sequence, corresponding to replacing a centered compression by its
negative. -/
def signedMoment (s : ℕ → ℝ) (j : ℕ) : ℝ := (-1 : ℝ) ^ j * s j

/-- The operator-free necklace expression driven by the complement density `q` and its compression
moments `s`.  This is the finite algebraic left-hand side of the remaining E5b identity. -/
noncomputable def neckMoment (m : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  (m - 1 : ℕ) * pathMoment q s (m - 1) +
    ∑ b ∈ Finset.range (m - 1),
      (b + 1 : ℕ) * ((-1 : ℝ) ^ b *
        (pathMoment (1 - q) (signedMoment s) (m - 2 - b) * pathMoment q s b))

/-- **Graphon-to-finite-algebra bridge for E5b.**  The actual necklace sum is exactly `neckMoment`
at the complement density and complement compression moments.  No integrals or operators remain on
the right-hand side. -/
theorem neckSum_eq_neckMoment (hW : IsGraphon W mu) {m : ℕ}
    (hm : Odd m) (hm3 : 3 ≤ m) :
    neckSum W mu m =
      neckMoment m (1 - edgeDensity W mu) (specMoment (compl W) mu) := by
  rw [neckSum_pathDensity_single_sum hW hm hm3]
  have hU := isGraphon_compl hW
  have hpathU : ∀ n,
      pathDensity (compl W) mu n =
        pathMoment (1 - edgeDensity W mu) (specMoment (compl W) mu) n := by
    intro n
    rw [pathDensity_eq_pathMoment hU n, edgeDensity_compl hW]
  have hpathW : ∀ n,
      pathDensity W mu n =
        pathMoment (1 - (1 - edgeDensity W mu))
          (signedMoment (specMoment (compl W) mu)) n := by
    intro n
    rw [pathDensity_eq_pathMoment hW n]
    congr 2
    · ring
    · funext j
      exact specMoment_eq_sign_mul_compl hW j
  unfold neckMoment
  simp_rw [hpathU, hpathW]

end OddCycleBound.HighDensity
