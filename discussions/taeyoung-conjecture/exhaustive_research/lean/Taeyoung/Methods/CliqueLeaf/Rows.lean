import Taeyoung.Methods.CliqueLeaf.Target

/-!
# The three catalogue members of the clique common-leaf family

`satisfiesLowerBound_of_cliqueLeaf` needs the chromatic polynomial and chromatic
number of `cliqueLeafGraph s k`.  Both come from the attachment tower, following
the recipe validated on the paw in `Methods/Chromatic/PawExample.lean`: build
`H_{r,k}` as `k` successive `attachVertex`s at a single clique vertex over
`K_r`, give the explicit relabelling onto the `Fin` presentation, and discharge
the adjacency correspondence by `decide`.

The three members the catalogue needs are

| Atlas | member | `s` | `k` | vertices |
|---:|---|---:|---:|---:|
| 45 | `H_{4,1}` | 1 | 1 | 5 |
| 133 | `H_{4,2}` | 1 | 2 | 6 |
| 191 | `H_{5,1}` | 2 | 1 | 6 |

each `verified` on its full required interval.
-/

open Taeyoung Finset Polynomial

namespace Taeyoung.Methods.CliqueLeaf

/-- A singleton is a clique in any graph — vacuously, since it has no two
distinct elements. -/
lemma singleton_isClique' {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V) :
    G.IsClique (({v} : Finset V) : Set V) := by
  intro u hu w hw huw
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hw
  exact absurd (hu.trans hw.symm) huw

/-! ### `H_{4,1}` — Atlas 45 -/

/-- `K₄` with one leaf at vertex `0`. -/
abbrev tower41 : SimpleGraph (Option (Fin 4)) :=
  attachVertex (⊤ : SimpleGraph (Fin 4)) {0}

def equiv41 : Option (Fin 4) ≃ Fin 5 where
  toFun a := match a with
    | none => 4
    | some i => ![0, 1, 2, 3] i
  invFun j := ![some 0, some 1, some 2, some 3, none] j
  left_inv := by decide
  right_inv := by decide

def iso41 : tower41 ≃g cliqueLeafGraph 1 1 where
  toEquiv := equiv41
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom41 :
    IsChromaticPolynomial (cliqueLeafGraph 1 1)
      ((∏ i ∈ range (1 + 3), (X - C (i : ℝ))) * (X - C 1) ^ 1) := by
  have h := isChromaticPolynomial_of_attachIso iso41 (singleton_isClique' _ 0)
    (isChromaticPolynomial_top 4)
  simp only [Finset.card_singleton, Nat.cast_one] at h
  have hpoly : (∏ i ∈ range (1 + 3), (X - C (i : ℝ))) * (X - C 1) ^ 1 =
      (X - C 1) * ∏ i ∈ range 4, (X - C (i : ℝ)) := by
    rw [show (1 : ℕ) + 3 = 4 from rfl, pow_one]
    ring
  rw [hpoly]
  exact h

theorem count41 (n : ℕ) :
    properAssignmentCount (cliqueLeafGraph 1 1) n = (n - 1) * n.descFactorial 4 := by
  rw [properAssignmentCount_of_attachIso iso41 (singleton_isClique' _ 0) n,
    properAssignmentCount_top]
  simp

theorem num41 : IsChromaticNumber (cliqueLeafGraph 1 1) (1 + 3) where
  positive := by
    rw [count41]
    decide
  zero_below n hn := by
    rw [count41, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < 4), Nat.mul_zero]

theorem satisfiesLowerBound_41 : Taeyoung.SatisfiesLowerBound (cliqueLeafGraph 1 1) :=
  satisfiesLowerBound_of_cliqueLeaf 1 1 chrom41 num41

/-! ### `H_{4,2}` — Atlas 133 -/

/-- `K₄` with two leaves at the same vertex `0`. -/
abbrev tower42 : SimpleGraph (Option (Option (Fin 4))) :=
  attachVertex tower41 {some 0}

def equiv42 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some i) => ![0, 1, 2, 3] i
  invFun j := ![some (some 0), some (some 1), some (some 2), some (some 3),
    some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso42 : tower42 ≃g cliqueLeafGraph 1 2 where
  toEquiv := equiv42
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom42 :
    IsChromaticPolynomial (cliqueLeafGraph 1 2)
      ((∏ i ∈ range (1 + 3), (X - C (i : ℝ))) * (X - C 1) ^ 2) := by
  have h := isChromaticPolynomial_of_attachIso iso42
    (singleton_isClique' _ (some 0))
    (isChromaticPolynomial_attachVertex (singleton_isClique' _ 0)
      (isChromaticPolynomial_top 4))
  simp only [Finset.card_singleton, Nat.cast_one] at h
  have hpoly : (∏ i ∈ range (1 + 3), (X - C (i : ℝ))) * (X - C 1) ^ 2 =
      (X - C 1) * ((X - C 1) * ∏ i ∈ range 4, (X - C (i : ℝ))) := by
    rw [show (1 : ℕ) + 3 = 4 from rfl]
    ring
  rw [hpoly]
  exact h

theorem count42 (n : ℕ) :
    properAssignmentCount (cliqueLeafGraph 1 2) n =
      (n - 1) * ((n - 1) * n.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso iso42 (singleton_isClique' _ (some 0)) n,
    properAssignmentCount_attachVertex (singleton_isClique' _ 0),
    properAssignmentCount_top]
  simp

theorem num42 : IsChromaticNumber (cliqueLeafGraph 1 2) (1 + 3) where
  positive := by
    rw [count42]
    decide
  zero_below n hn := by
    rw [count42, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < 4),
      Nat.mul_zero, Nat.mul_zero]

theorem satisfiesLowerBound_42 : Taeyoung.SatisfiesLowerBound (cliqueLeafGraph 1 2) :=
  satisfiesLowerBound_of_cliqueLeaf 1 2 chrom42 num42

/-! ### `H_{5,1}` — Atlas 191 -/

/-- `K₅` with one leaf at vertex `0`. -/
abbrev tower51 : SimpleGraph (Option (Fin 5)) :=
  attachVertex (⊤ : SimpleGraph (Fin 5)) {0}

def equiv51 : Option (Fin 5) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some i => ![0, 1, 2, 3, 4] i
  invFun j := ![some 0, some 1, some 2, some 3, some 4, none] j
  left_inv := by decide
  right_inv := by decide

def iso51 : tower51 ≃g cliqueLeafGraph 2 1 where
  toEquiv := equiv51
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom51 :
    IsChromaticPolynomial (cliqueLeafGraph 2 1)
      ((∏ i ∈ range (2 + 3), (X - C (i : ℝ))) * (X - C 1) ^ 1) := by
  have h := isChromaticPolynomial_of_attachIso iso51 (singleton_isClique' _ 0)
    (isChromaticPolynomial_top 5)
  simp only [Finset.card_singleton, Nat.cast_one] at h
  have hpoly : (∏ i ∈ range (2 + 3), (X - C (i : ℝ))) * (X - C 1) ^ 1 =
      (X - C 1) * ∏ i ∈ range 5, (X - C (i : ℝ)) := by
    rw [show (2 : ℕ) + 3 = 5 from rfl, pow_one]
    ring
  rw [hpoly]
  exact h

theorem count51 (n : ℕ) :
    properAssignmentCount (cliqueLeafGraph 2 1) n = (n - 1) * n.descFactorial 5 := by
  rw [properAssignmentCount_of_attachIso iso51 (singleton_isClique' _ 0) n,
    properAssignmentCount_top]
  simp

theorem num51 : IsChromaticNumber (cliqueLeafGraph 2 1) (2 + 3) where
  positive := by
    rw [count51]
    decide
  zero_below n hn := by
    rw [count51, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < 5), Nat.mul_zero]

theorem satisfiesLowerBound_51 : Taeyoung.SatisfiesLowerBound (cliqueLeafGraph 2 1) :=
  satisfiesLowerBound_of_cliqueLeaf 2 1 chrom51 num51

end Taeyoung.Methods.CliqueLeaf
