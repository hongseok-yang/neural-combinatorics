import OddCycleBound.Fisher.CliqueCounts

/-!
# Module 2 — Dependence polynomial and the derivative identity

Corresponds to `fisher.tex`, Definition (dependence polynomial) and
Lemma `lem:derivative-identity`; Module 2 of the blueprint.

* `depPoly G := ∑ₖ (-1)^k · c_k(G) · Xᵏ ∈ ℝ[X]`   (a Mathlib `Polynomial ℝ`).
* Derivative identity:
  `D_G^{(j)} = (-1)^j · j! · ∑_{S : j-clique} D_{G[N_G(S)]}`.

This module is purely finite combinatorics plus polynomial differentiation
(`Polynomial.derivative`).  No analysis is required here.
-/

namespace Fisher

open SimpleGraph Finset Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The dependence polynomial `D_G(z) = ∑ₖ (-1)^k c_k(G) z^k`. -/
noncomputable def depPoly : Polynomial ℝ :=
  ∑ k ∈ Finset.range (Fintype.card V + 1),
    Polynomial.C ((-1) ^ k * (cliqueCount G k : ℝ)) * Polynomial.X ^ k

/-- The coefficient formula defining the dependence polynomial, valid in every
degree (above `|V|`, both sides vanish). -/
theorem depPoly_coeff (k : ℕ) :
    (depPoly G).coeff k = (-1) ^ k * (cliqueCount G k : ℝ) := by
  classical
  rw [depPoly, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hk : k < Fintype.card V + 1
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)]
    · simp
    · intro b hb hbk
      simp [hbk.symm]
  · have hkcard : Fintype.card V < k := by omega
    have hc : cliqueCount G k = 0 := cliqueCount_eq_zero_of_card_lt G hkcard
    rw [hc, Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hbcard : b ≤ Fintype.card V := by simpa using hb
    have hkb : k ≠ b := by omega
    simp [hkb]

/-- The dependence polynomial is invariant under graph isomorphism. -/
theorem depPoly_iso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (f : G ≃g H) :
    depPoly G = depPoly H := by
  ext k
  rw [depPoly_coeff, depPoly_coeff, cliqueCount_iso G f k]

/-- `D_G(0) = 1` (only the empty clique contributes at `z = 0`). -/
theorem depPoly_eval_zero : (depPoly G).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  classical
  rw [depPoly, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single_of_mem 0 (by simp)]
  · simp [cliqueCount_zero]
  · intro b hb hb0
    simp [Ne.symm hb0]

/-- Low-order coefficients: `D_G(z) = 1 - n z + e z² - T z³ + c₄ z⁴ - ⋯`. -/
theorem depPoly_coeff_zero : (depPoly G).coeff 0 = 1 := by
  classical
  rw [depPoly, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single_of_mem 0 (by simp)]
  · simp [cliqueCount_zero]
  · intro b hb hb0
    simp [Ne.symm hb0]

theorem depPoly_coeff_one : (depPoly G).coeff 1 = -(cliqueCount G 1 : ℝ) := by
  classical
  rw [depPoly, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hV : 0 < Fintype.card V
  · rw [Finset.sum_eq_single_of_mem 1 (by simp; omega)]
    · norm_num
    · intro b hb hb1
      simp [hb1.symm]
  · have hc : cliqueCount G 1 = 0 :=
      cliqueCount_eq_zero_of_card_lt G (by omega)
    simp [hc, show Fintype.card V = 0 by omega]

theorem depPoly_coeff_two : (depPoly G).coeff 2 = (cliqueCount G 2 : ℝ) := by
  classical
  rw [depPoly, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hV : 2 ≤ Fintype.card V
  · rw [Finset.sum_eq_single_of_mem 2 (by simp; omega)]
    · norm_num
    · intro b hb hb2
      simp [hb2.symm]
  · have hc : cliqueCount G 2 = 0 :=
      cliqueCount_eq_zero_of_card_lt G (by omega)
    rw [hc, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hb_le : b ≤ Fintype.card V := by simpa using hb
    have hb_ne : 2 ≠ b := by omega
    simp [hb_ne]

theorem depPoly_coeff_three : (depPoly G).coeff 3 = -(cliqueCount G 3 : ℝ) := by
  classical
  rw [depPoly, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hV : 3 ≤ Fintype.card V
  · rw [Finset.sum_eq_single_of_mem 3 (by simp; omega)]
    · norm_num
    · intro b hb hb3
      simp [hb3.symm]
  · have hc : cliqueCount G 3 = 0 :=
      cliqueCount_eq_zero_of_card_lt G (by omega)
    rw [hc, Nat.cast_zero, neg_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hb_le : b ≤ Fintype.card V := by simpa using hb
    have hb_ne : 3 ≠ b := by omega
    simp [hb_ne]

/-- Partition the nonempty cliques according to whether they contain a fixed
vertex.  The second summand is the clique count in its common neighbourhood. -/
theorem cliqueCount_succ_delete_vertex (v : V) (m : ℕ) :
    cliqueCount G (m + 1) =
      cliqueCount (G.induce (↑(Finset.univ.erase v) : Set V)) (m + 1) +
        cliqueCount (G.induce (↑(commonNbhd G {v}) : Set V)) m := by
  classical
  let A := G.cliqueFinset (m + 1)
  have hdelete :
      cliqueCount (G.induce (↑(Finset.univ.erase v) : Set V)) (m + 1) =
        (A.filter fun T => v ∉ T).card := by
    rw [cliqueCount_induce]
    congr 1
    ext T
    simp [A]
  have hlink :
      cliqueCount (G.induce (↑(commonNbhd G {v}) : Set V)) m =
        (A.filter fun T => v ∈ T).card := by
    rw [cliqueCount_commonNbhd_eq_filter G
      (j := 1) (S := {v}) (by simp [SimpleGraph.isNClique_singleton]) m]
    congr 1
    ext T
    simp [A, Nat.add_comm]
  rw [hdelete, hlink]
  change A.card = (A.filter fun T => v ∉ T).card + (A.filter fun T => v ∈ T).card
  have hpartition :=
    Finset.card_filter_add_card_filter_not (s := A) (fun T => v ∈ T)
  omega

/-- Vertex-deletion recurrence for the dependence polynomial. -/
theorem depPoly_delete_vertex (v : V) :
    depPoly G =
      depPoly (G.induce (↑(Finset.univ.erase v) : Set V)) -
        Polynomial.X * depPoly (G.induce (↑(commonNbhd G {v}) : Set V)) := by
  classical
  ext k
  cases k with
  | zero =>
      simp [depPoly_coeff_zero]
  | succ m =>
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_mul, depPoly_coeff,
        depPoly_coeff, depPoly_coeff, cliqueCount_succ_delete_vertex G v m]
      push_cast
      simp only [Nat.succ_eq_add_one, pow_succ]
      ring

/-- First derivative form of the clique-link double count:
`D'_G = -∑_v D_{G[N(v)]}`. -/
theorem depPoly_derivative :
    (depPoly G).derivative =
      -∑ v : V, depPoly (G.induce (↑(G.neighborFinset v) : Set V)) := by
  classical
  ext m
  rw [Polynomial.coeff_derivative, depPoly_coeff, Polynomial.coeff_neg,
    Polynomial.finsetSum_coeff]
  simp_rw [depPoly_coeff]
  have hinc := congrArg (fun z : ℕ ↦ (z : ℝ)) (sum_cliqueCount_neighbor G m)
  push_cast at hinc
  rw [← Finset.mul_sum]
  rw [hinc]
  norm_num [pow_succ]
  ring

/-- **Derivative identity** (`lem:derivative-identity`).  The `j`-th derivative of
the dependence polynomial is `(-1)^j · j!` times the sum, over `j`-cliques `S`,
of the dependence polynomials of their induced common-neighborhood graphs. -/
theorem depPoly_derivative_identity (j : ℕ) :
    Polynomial.derivative^[j] (depPoly G) =
      Polynomial.C (((-1 : ℝ) ^ j) * (Nat.factorial j : ℝ)) *
        ∑ S ∈ G.cliqueFinset j,
          depPoly (G.induce (↑(commonNbhd G S) : Set V)) := by
  classical
  ext m
  rw [Polynomial.coeff_iterate_derivative, depPoly_coeff,
    Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
  simp_rw [depPoly_coeff]
  have hinc := congrArg (fun z : ℕ ↦ (z : ℝ))
    (sum_cliqueCount_commonNbhd G j m)
  push_cast at hinc
  rw [← Finset.mul_sum, hinc, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [pow_add]
  ring

end Fisher
