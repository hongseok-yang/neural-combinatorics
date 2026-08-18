import Taeyoung.Methods.OddCycleC5.DensityBridge

/-!
# The chromatic polynomial of the five-cycle

`SatisfiesLowerBound` quantifies over every polynomial satisfying
`IsChromaticPolynomial`, so the analytic bound of `DensityBridge.lean` cannot
discharge the `C₅` Atlas row on its own: we must exhibit the chromatic
polynomial, i.e. count proper colourings for **every** number of colours.

The count is reduced to two products.  Summing the innermost coordinate gives
`k - |{a₀, a₃}|`, which splits the five-fold sum into

* a path count `#{a₀≠a₁, a₁≠a₂, a₂≠a₃} = k(k-1)³`, weighted by `k-2`; and
* a triangle count `#{a₀≠a₁, a₁≠a₂, a₂≠a₀} = k(k-1)(k-2)`.

Both are products of independent choices, so no cycle recursion is needed.
-/

open MeasureTheory Finset

namespace Taeyoung.Methods.OddCycleC5

open Taeyoung

/-! ### Reading a colouring off as a tuple -/

/-- Reading the five coordinates identifies assignments with `5`-tuples. -/
def tupleEquiv (k : ℕ) :
    (Fin 5 → Fin k) ≃ Fin k × Fin k × Fin k × Fin k × Fin k where
  toFun x := (x 0, x 1, x 2, x 3, x 4)
  invFun t := ![t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv t := rfl

/-- Proper assignments of `c5` are exactly the five inequalities along the
cycle. -/
lemma isProperAssignment_c5_iff {k : ℕ} (x : Fin 5 → Fin k) :
    IsProperAssignment c5 x ↔
      x 0 ≠ x 1 ∧ x 1 ≠ x 2 ∧ x 2 ≠ x 3 ∧ x 3 ≠ x 4 ∧ x 4 ≠ x 0 := by
  constructor
  · intro h
    exact ⟨h (by decide), h (by decide), h (by decide), h (by decide),
      h (by decide)⟩
  · rintro ⟨h01, h12, h23, h34, h40⟩ u v huv
    revert huv
    fin_cases u <;> fin_cases v <;> intro huv <;>
      first
        | exact absurd huv (by decide)
        | assumption
        | exact h01.symm
        | exact h12.symm
        | exact h23.symm
        | exact h34.symm
        | exact h40.symm

/-! ### Elementary cardinalities -/

variable {k : ℕ}

lemma card_filter_ne (a : Fin k) :
    (univ.filter fun b : Fin k => b ≠ a).card = k - 1 := by
  classical
  rw [Finset.filter_ne', Finset.card_erase_of_mem (mem_univ a)]
  simp

/-- The number of colours avoiding two given ones, as a single formula valid in
both the equal and the distinct case. -/
lemma card_filter_ne_two (hk : 2 ≤ k) (a b : Fin k) :
    (univ.filter fun c : Fin k => c ≠ a ∧ c ≠ b).card =
      k - 2 + (if a = b then 1 else 0) := by
  classical
  have hset : (univ.filter fun c : Fin k => c ≠ a ∧ c ≠ b) =
      univ \ {a, b} := by
    ext c
    simp
  rw [hset, Finset.card_sdiff, Finset.inter_univ]
  simp only [Finset.card_univ, Fintype.card_fin]
  by_cases hab : a = b
  · subst hab
    rw [Finset.insert_eq_self.mpr (Finset.mem_singleton_self a),
      Finset.card_singleton, if_pos rfl]
    omega
  · rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton,
      if_neg hab]
    omega

/-! ### The five-fold nested sum -/

/-- `properAssignmentCount` of `c5` as five nested sums over the colours. -/
lemma properAssignmentCount_c5_sum (k : ℕ) :
    properAssignmentCount c5 k =
      ∑ a0 : Fin k, ∑ a1 : Fin k, ∑ a2 : Fin k, ∑ a3 : Fin k, ∑ a4 : Fin k,
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a4 ≠ a3 ∧ a4 ≠ a0 then 1 else 0 := by
  classical
  have h0 : properAssignmentCount c5 k =
      ∑ x : Fin 5 → Fin k, if IsProperAssignment c5 x then 1 else 0 := by
    simp only [properAssignmentCount, Finset.card_filter]
  rw [h0, ← Equiv.sum_comp (tupleEquiv k).symm]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a0 _ ↦ Finset.sum_congr rfl fun a1 _ ↦
    Finset.sum_congr rfl fun a2 _ ↦ Finset.sum_congr rfl fun a3 _ ↦
      Finset.sum_congr rfl fun a4 _ ↦ ?_
  have : IsProperAssignment c5 ((tupleEquiv k).symm (a0, a1, a2, a3, a4)) ↔
      (a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a4 ≠ a3 ∧ a4 ≠ a0) := by
    rw [isProperAssignment_c5_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h2, h3, Ne.symm h4, h5⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h2, h3, Ne.symm h4, h5⟩
  simp only [this]

/-! ### Evaluating the sum -/

/-- The innermost sum: the fifth colour avoids the third and the zeroth. -/
lemma sum_a4 (hk : 2 ≤ k) (a0 a1 a2 a3 : Fin k) :
    (∑ a4 : Fin k,
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a4 ≠ a3 ∧ a4 ≠ a0 then 1 else 0) =
      (if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 then k - 2 else 0) +
        (if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a3 = a0 then 1 else 0) := by
  classical
  by_cases hA : a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3
  · have hsum : (∑ a4 : Fin k,
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a4 ≠ a3 ∧ a4 ≠ a0 then 1 else 0) =
        ∑ a4 : Fin k, if a4 ≠ a3 ∧ a4 ≠ a0 then 1 else 0 := by
      refine Finset.sum_congr rfl fun a4 _ ↦ ?_
      simp [hA.1, hA.2.1, hA.2.2]
    rw [hsum, ← Finset.card_filter, card_filter_ne_two hk a3 a0, if_pos hA]
    congr 1
    by_cases h30 : a3 = a0
    · rw [if_pos h30, if_pos ⟨hA.1, hA.2.1, hA.2.2, h30⟩]
    · rw [if_neg h30, if_neg fun h ↦ h30 h.2.2.2]
  · have hzero : (∑ a4 : Fin k,
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a4 ≠ a3 ∧ a4 ≠ a0 then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun a4 _ ↦ ?_
      rw [if_neg]
      rintro ⟨h1, h2, h3, _, _⟩
      exact hA ⟨h1, h2, h3⟩
    rw [hzero, if_neg hA, if_neg fun h ↦ hA ⟨h.1, h.2.1, h.2.2.1⟩]

/-- Summing a colour that must avoid one given colour. -/
lemma sum_ite_ne (P : Prop) [Decidable P] (a : Fin k) (c : ℕ) :
    (∑ b : Fin k, if P ∧ a ≠ b then c else 0) = if P then (k - 1) * c else 0 := by
  classical
  by_cases hP : P
  · rw [if_pos hP]
    have hiff : ∀ b : Fin k, (P ∧ a ≠ b) ↔ (b ≠ a) := by
      intro b
      exact ⟨fun h ↦ Ne.symm h.2, fun h ↦ ⟨hP, Ne.symm h⟩⟩
    simp only [hiff]
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_ne, smul_eq_mul]
  · rw [if_neg hP]
    exact Finset.sum_eq_zero fun b _ ↦ if_neg fun h ↦ hP h.1

/-- The path count `#{a₀≠a₁, a₁≠a₂, a₂≠a₃} = k(k-1)³`. -/
lemma sum_path (k : ℕ) :
    (∑ a0 : Fin k, ∑ a1 : Fin k, ∑ a2 : Fin k, ∑ a3 : Fin k,
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 then 1 else 0) =
      k * ((k - 1) * ((k - 1) * (k - 1))) := by
  classical
  have h3 : ∀ a0 a1 a2 : Fin k,
      (∑ a3 : Fin k, if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 then (1 : ℕ) else 0) =
        if a0 ≠ a1 ∧ a1 ≠ a2 then (k - 1) * 1 else 0 := by
    intro a0 a1 a2
    rw [← sum_ite_ne (a0 ≠ a1 ∧ a1 ≠ a2) a2 1]
    refine Finset.sum_congr rfl fun a3 _ ↦ ?_
    congr 1
    exact propext ⟨fun h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h ↦ ⟨h.1.1, h.1.2, h.2⟩⟩
  have h2 : ∀ a0 a1 : Fin k,
      (∑ a2 : Fin k, if a0 ≠ a1 ∧ a1 ≠ a2 then (k - 1) * 1 else 0) =
        if a0 ≠ a1 then (k - 1) * ((k - 1) * 1) else 0 :=
    fun a0 a1 ↦ sum_ite_ne (a0 ≠ a1) a1 ((k - 1) * 1)
  have h1 : ∀ a0 : Fin k,
      (∑ a1 : Fin k, if a0 ≠ a1 then (k - 1) * ((k - 1) * 1) else 0) =
        (k - 1) * ((k - 1) * ((k - 1) * 1)) := by
    intro a0
    have := sum_ite_ne (k := k) True a0 ((k - 1) * ((k - 1) * 1))
    simp only [true_and, if_pos trivial] at this
    rw [← this]
  simp only [h3, h2, h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- Summing a colour that must avoid two given distinct colours. -/
lemma sum_ite_ne_two (hk : 2 ≤ k) {a0 a1 : Fin k} (h01 : a0 ≠ a1) (c : ℕ) :
    (∑ a2 : Fin k, if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a0 then c else 0) =
      (k - 2) * c := by
  classical
  have hiff : ∀ a2 : Fin k,
      (a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a0) ↔ (a2 ≠ a1 ∧ a2 ≠ a0) := by
    intro a2
    exact ⟨fun h ↦ ⟨Ne.symm h.2.1, h.2.2⟩, fun h ↦ ⟨h01, Ne.symm h.1, h.2⟩⟩
  simp only [hiff]
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_ne_two hk a1 a0,
    if_neg (Ne.symm h01), smul_eq_mul]
  simp

/-- The triangle count `#{a₀≠a₁, a₁≠a₂, a₂≠a₃, a₃=a₀} = k(k-1)(k-2)`. -/
lemma sum_triangle (hk : 2 ≤ k) :
    (∑ a0 : Fin k, ∑ a1 : Fin k, ∑ a2 : Fin k, ∑ a3 : Fin k,
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a3 = a0 then 1 else 0) =
      k * ((k - 1) * ((k - 2) * 1)) := by
  classical
  have h3 : ∀ a0 a1 a2 : Fin k,
      (∑ a3 : Fin k, if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a3 = a0 then (1 : ℕ) else 0) =
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a0 then 1 else 0 := by
    intro a0 a1 a2
    have hstep : ∀ a3 : Fin k,
        (if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a3 = a0 then (1 : ℕ) else 0) =
          if a3 = a0 then (if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a0 then 1 else 0) else 0 := by
      intro a3
      by_cases h : a3 = a0
      · subst h
        simp
      · rw [if_neg h, if_neg fun hc ↦ h hc.2.2.2]
    simp only [hstep]
    rw [Finset.sum_ite_eq' univ a0 (fun _ ↦ _)]
    simp
  have h2 : ∀ a0 a1 : Fin k,
      (∑ a2 : Fin k, if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a0 then (1 : ℕ) else 0) =
        if a0 ≠ a1 then (k - 2) * 1 else 0 := by
    intro a0 a1
    by_cases h01 : a0 ≠ a1
    · rw [if_pos h01, sum_ite_ne_two hk h01 1]
    · rw [if_neg h01]
      exact Finset.sum_eq_zero fun a2 _ ↦ if_neg fun h ↦ h01 h.1
  have h1 : ∀ a0 : Fin k,
      (∑ a1 : Fin k, if a0 ≠ a1 then (k - 2) * 1 else 0) =
        (k - 1) * ((k - 2) * 1) := by
    intro a0
    have := sum_ite_ne (k := k) True a0 ((k - 2) * 1)
    simp only [true_and, if_pos trivial] at this
    rw [← this]
  simp only [h3, h2, h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The chromatic count of the five-cycle.** -/
lemma properAssignmentCount_c5 (hk : 2 ≤ k) :
    properAssignmentCount c5 k = k * (k - 1) * (k - 2) * ((k - 1) ^ 2 + 1) := by
  classical
  rw [properAssignmentCount_c5_sum]
  have hinner : ∀ a0 a1 a2 a3 : Fin k,
      (∑ a4 : Fin k,
        if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a4 ≠ a3 ∧ a4 ≠ a0 then (1 : ℕ) else 0) =
        (k - 2) * (if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 then 1 else 0) +
          (if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3 ∧ a3 = a0 then 1 else 0) := by
    intro a0 a1 a2 a3
    rw [sum_a4 hk]
    congr 1
    by_cases hA : a0 ≠ a1 ∧ a1 ≠ a2 ∧ a2 ≠ a3
    · rw [if_pos hA, if_pos hA, mul_one]
    · rw [if_neg hA, if_neg hA, mul_zero]
  simp only [hinner, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_path, sum_triangle hk]
  have h1 : 1 ≤ k := by omega
  have h2 : 2 ≤ k := hk
  set m := k - 1 with hm
  set n := k - 2 with hn
  ring

/-- With at most one colour there is no proper colouring of a graph with an
edge. -/
lemma properAssignmentCount_c5_small (hk : k ≤ 1) :
    properAssignmentCount c5 k = 0 := by
  classical
  have hsub : Subsingleton (Fin k) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h | h <;> subst h <;>
      infer_instance
  rw [properAssignmentCount_c5_sum]
  refine Finset.sum_eq_zero fun a0 _ ↦ Finset.sum_eq_zero fun a1 _ ↦
    Finset.sum_eq_zero fun a2 _ ↦ Finset.sum_eq_zero fun a3 _ ↦
      Finset.sum_eq_zero fun a4 _ ↦ ?_
  exact if_neg fun h ↦ h.1 (Subsingleton.elim a0 a1)

/-! ### The chromatic specifications -/

open Polynomial in
/-- **The chromatic polynomial of the five-cycle** is `(X-1)^5 - (X-1)`. -/
theorem isChromaticPolynomial_c5 :
    IsChromaticPolynomial c5 ((X - 1) ^ 5 - (X - 1)) := by
  intro k
  by_cases hk : k ≤ 1
  · rw [properAssignmentCount_c5_small hk]
    interval_cases k <;> norm_num
  · have hk2 : 2 ≤ k := by omega
    have hc1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 :=
      Nat.cast_sub (by omega) |>.trans (by norm_num)
    have hc2 : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 :=
      Nat.cast_sub hk2 |>.trans (by norm_num)
    rw [properAssignmentCount_c5 hk2]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    push_cast [hc1, hc2]
    ring

/-- The five-cycle is `3`-chromatic. -/
theorem isChromaticNumber_c5 : IsChromaticNumber c5 3 where
  positive := by
    rw [properAssignmentCount_c5 (by norm_num)]
    norm_num
  zero_below k hk := by
    interval_cases k
    · exact properAssignmentCount_c5_small (by norm_num)
    · exact properAssignmentCount_c5_small (by norm_num)
    · rw [properAssignmentCount_c5 (by norm_num)]
      norm_num

/-! ### The catalogue proposition -/

open Polynomial in
/-- **The five-cycle satisfies the common catalogue proposition.** -/
theorem c5_satisfiesLowerBound : Taeyoung.SatisfiesLowerBound c5 := by
  intro P r hP hr Ω instM μ instP W hp
  have hPeq : P = (X - 1) ^ 5 - (X - 1) :=
    IsChromaticPolynomial.unique (H := c5) hP isChromaticPolynomial_c5
  have hreq : r = 3 :=
    IsChromaticNumber.unique (H := c5) hr isChromaticNumber_c5
  subst hPeq
  subst hreq
  have hbound := c5_homDensity_bound W
  change chromaticTarget (V := Fin 5) _ (cliqueDensity 2 W) ≤ homDensity c5 W
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hbound
    simpa using hbound
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc :
        (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 5) *
            Polynomial.eval (1 / (1 - cliqueDensity 2 W))
              (((X : ℝ[X]) - 1) ^ 5 - (X - 1)) =
          cliqueDensity 2 W ^ 5 -
            cliqueDensity 2 W * (1 - cliqueDensity 2 W) ^ 4 := by
      simp only [Fintype.card_fin, eval_sub, eval_pow, eval_X, eval_one]
      field_simp
      ring
    rw [hcalc]
    exact hbound

end Taeyoung.Methods.OddCycleC5
