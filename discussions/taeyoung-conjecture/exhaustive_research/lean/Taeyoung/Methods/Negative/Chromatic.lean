import Taeyoung.Methods.Negative.ProperCount

/-!
# The chromatic polynomial from finitely many surjective counts

`IsChromaticPolynomial H P` quantifies over **every** `k`, so no amount of
`decide +kernel` evaluation establishes it directly: computed values pin the
coefficients only once one already knows the count is a polynomial.  This file
supplies the missing step, once and for all graphs.

Split a proper colouring by the set of colours it actually uses.  For a fixed
`j`-element `S ⊆ Fin k`, relabelling `S` by `Fin j` identifies the proper
colourings with image exactly `S` with the *surjective* proper colourings
`V → Fin j`; there are `k.choose j` such `S`; so

```
properAssignmentCount H k = ∑ⱼ (k choose j) · surjCount H j,
```

with `surjCount H j` independent of `k` and zero once `j > |V|`.  Since
`k.descFactorial j = j!·(k choose j)`, the right-hand side is the evaluation at
`k` of

```
P = ∑ⱼ (surjCount H j / j!) · ∏_{i<j} (X - i),
```

a polynomial with real coefficients — no divisibility argument is needed,
because `IsChromaticPolynomial` is stated over `ℝ`.

So a negative row now needs only the `|V|+1` numbers `surjCount H j`, each a
`decide +kernel` away through `Methods/Negative/ProperCount.lean`.  For a
six-vertex graph the largest is `j = 6`, i.e. `6^6 = 46656` functions.
-/

open Finset Polynomial

set_option maxRecDepth 100000

namespace Taeyoung.Methods.Negative

open Taeyoung

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The number of proper colourings `V → Fin j` that use **every** colour. -/
def surjCount (j : ℕ) : ℕ :=
  ((univ : Finset (V → Fin j)).filter
    (fun y ↦ IsProper H y ∧ Function.Surjective y)).card

/-- With more colours than vertices there is no surjection at all. -/
theorem surjCount_eq_zero {j : ℕ} (hj : Fintype.card V < j) : surjCount H j = 0 := by
  rw [surjCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ hy
  have := Fintype.card_le_of_surjective y hy.2
  simp only [Fintype.card_fin] at this
  omega

/-- **The top surjective count is free.**  A surjection between finite types of
equal cardinality is injective, and an injective assignment separates *every*
pair, so it is proper for any graph whatsoever.  The count is therefore the
number of bijections, `n!`, independently of `H`.

This matters for cost, not just tidiness: `j = n` is the largest sweep, and for
a six-vertex row `decide +kernel` on its `6⁶ = 46656` functions takes about two
and a half minutes.  Discharging it by this lemma leaves `j = n - 1` as the
worst case, an eighth of the work. -/
theorem surjCount_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    surjCount G n = n.factorial := by
  classical
  have hinj : surjCount G n = properAssignmentCount (⊤ : SimpleGraph (Fin n)) n := by
    rw [surjCount, properAssignmentCount]
    congr 1
    refine Finset.filter_congr fun y _ ↦ ?_
    constructor
    · rintro ⟨-, hs⟩
      have hy : Function.Injective y :=
        ((Fintype.bijective_iff_surjective_and_card y).mpr ⟨hs, by simp⟩).1
      intro u v huv hc
      exact ((SimpleGraph.top_adj u v).mp huv) (hy hc)
    · intro hp
      have hy : Function.Injective y := by
        intro u v hc
        by_contra hne
        exact hp (by simpa using hne) hc
      exact ⟨fun _ _ huv hc ↦ huv.ne (hy hc),
        ((Fintype.bijective_iff_injective_and_card y).mpr ⟨hy, by simp⟩).2⟩
  rw [hinj, properAssignmentCount_top, Nat.descFactorial_self]

/-! ### The relabelling bijection -/

/-- **Proper colourings with a prescribed colour set are surjective proper
colourings on a smaller palette.** -/
theorem card_image_fiber (k : ℕ) (S : Finset (Fin k)) :
    (((univ : Finset (V → Fin k)).filter (IsProper H)).filter
        (fun x ↦ Finset.image x univ = S)).card = surjCount H S.card := by
  classical
  set e : S ≃ Fin S.card := S.equivFin with he
  -- the map back: read a colour of `Fin S.card` as an element of `S ⊆ Fin k`
  refine (Finset.card_bij (fun y _ ↦ (fun v ↦ ((e.symm (y v) : S) : Fin k)))
    ?_ ?_ ?_).symm
  · -- it lands in the fiber
    intro y hy
    simp only [surjCount, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨hprop, hsurj⟩ := hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro u v huv hcon
      refine hprop u v huv ?_
      have : (e.symm (y u) : S) = e.symm (y v) := Subtype.ext hcon
      simpa using congrArg e this
    · ext c
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, rfl⟩
        exact (e.symm (y v)).2
      · intro hc
        obtain ⟨v, hv⟩ := hsurj (e ⟨c, hc⟩)
        exact ⟨v, by rw [hv, Equiv.symm_apply_apply]⟩
  · -- it is injective
    intro y₁ h₁ y₂ h₂ hEq
    funext v
    have hv : ((e.symm (y₁ v) : S) : Fin k) = ((e.symm (y₂ v) : S) : Fin k) :=
      congrFun hEq v
    have : (e.symm (y₁ v) : S) = e.symm (y₂ v) := Subtype.ext hv
    simpa using congrArg e this
  · -- it hits every element of the fiber
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hprop, himg⟩ := hx
    have hmem : ∀ v : V, x v ∈ S := by
      intro v
      rw [← himg]
      exact Finset.mem_image_of_mem x (Finset.mem_univ v)
    refine ⟨fun v ↦ e ⟨x v, hmem v⟩, ?_, ?_⟩
    · simp only [surjCount, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro u v huv hcon
        refine hprop u v huv ?_
        have := congrArg e.symm hcon
        simpa using congrArg Subtype.val this
      · intro c
        obtain ⟨v, _, hv⟩ : ∃ v ∈ (univ : Finset V), x v = (e.symm c : S) := by
          have : ((e.symm c : S) : Fin k) ∈ Finset.image x univ := by
            rw [himg]; exact (e.symm c).2
          simpa using this
        refine ⟨v, ?_⟩
        show e ⟨x v, hmem v⟩ = c
        rw [show (⟨x v, hmem v⟩ : S) = e.symm c from Subtype.ext hv,
          Equiv.apply_symm_apply]
    · funext v
      simp

/-! ### The sum, and the polynomial -/

/-- **The count splits by colour-set size.** -/
theorem properAssignmentCount_eq_sum (k : ℕ) :
    properAssignmentCount H k =
      ∑ j ∈ range (Fintype.card V + 1), k.choose j * surjCount H j := by
  classical
  have hfib : properCount H k =
      ∑ S ∈ (univ : Finset (Fin k)).powerset, surjCount H S.card := by
    rw [properCount, Finset.powerset_univ]
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : V → Fin k ↦ Finset.image x univ)
      (t := (univ : Finset (Finset (Fin k)))) (fun x _ ↦ Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun S _ ↦ card_image_fiber H k S
  rw [properAssignmentCount_eq, hfib, Finset.sum_powerset_apply_card
    (f := fun j ↦ surjCount H j)]
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- both index ranges agree: `choose` vanishes above `k`, `surjCount` above `|V|`
  rcases le_total (Fintype.card V) k with hle | hle
  · refine (Finset.sum_subset (by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega) ?_).symm
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [surjCount_eq_zero H (by omega), Nat.mul_zero]
  · refine Finset.sum_subset (by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega) ?_
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]

/-- **The chromatic polynomial, from the surjective counts.** -/
theorem isChromaticPolynomial_of_surjCount :
    IsChromaticPolynomial H
      (∑ j ∈ range (Fintype.card V + 1),
        C ((surjCount H j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) := by
  intro k
  rw [eval_finset_sum, properAssignmentCount_eq_sum H k]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdesc : Polynomial.eval (k : ℝ) (∏ i ∈ range j, (X - C (i : ℝ))) =
      (k.descFactorial j : ℝ) := by
    have h := isChromaticPolynomial_top j k
    rwa [properAssignmentCount_top] at h
  rw [eval_mul, eval_C, hdesc, Nat.descFactorial_eq_factorial_mul_choose]
  have hfac : ((j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  push_cast
  field_simp

/-! ### A worked instance

Atlas 129 again.  Its surjective counts are `0,0,0,42,384,960,720`, and the
bridge then reproduces the colouring counts `0,0,0,42,552,3300,13080` — for
instance `552 = C(4,3)·42 + C(4,4)·384`.

Only the two cheap ones are checked here.  The cost is `j^6` functions, and the
measured `decide +kernel` times on this machine are: `j = 4` (4096) and below,
seconds; `j = 5` (15625), seconds; `j = 6` (46656), about 2 min 37 s.  So a
*complete* chromatic polynomial for one six-vertex row costs roughly three
minutes of build time, and all 19 negatives would add about an hour.  That is
affordable but not free, which is why the full counts belong in the generated
Atlas modules rather than here. -/

section Worked

theorem surjCount_graph129_three : surjCount graph129 3 = 42 := by decide +kernel

theorem surjCount_graph129_four : surjCount graph129 4 = 384 := by decide +kernel

end Worked

end Taeyoung.Methods.Negative
