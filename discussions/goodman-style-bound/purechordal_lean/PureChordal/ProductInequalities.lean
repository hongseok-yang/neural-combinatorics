import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Elementary finite-product inequalities

The main lemma says that, for independent events with success probabilities in
`[0,1]`, the probability of exactly one failure is at most the probability of
at least one failure.  Summed over the vertices of a clique, this gives the
pointwise inequality used in the direct graphon Moon--Moser proof.
-/

open scoped BigOperators

namespace PureChordal

lemma sum_one_sub_mul_prod_erase_le_one_sub_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i)
    (ha1 : ∀ i ∈ s, a i ≤ 1) :
    (∑ i ∈ s, (1 - a i) * ∏ j ∈ s.erase i, a j)
      ≤ 1 - ∏ i ∈ s, a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
      have hae0 := ha0 e (Finset.mem_insert_self e s)
      have hae1 := ha1 e (Finset.mem_insert_self e s)
      have ha0s : ∀ i ∈ s, 0 ≤ a i :=
        fun i hi ↦ ha0 i (Finset.mem_insert_of_mem hi)
      have ha1s : ∀ i ∈ s, a i ≤ 1 :=
        fun i hi ↦ ha1 i (Finset.mem_insert_of_mem hi)
      have hprod0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg ha0s
      have hprod1 : (∏ i ∈ s, a i) ≤ 1 := Finset.prod_le_one ha0s ha1s
      have hsum :
          (∑ i ∈ insert e s, (1 - a i) * ∏ j ∈ (insert e s).erase i, a j)
            =
          (1 - a e) * (∏ j ∈ s, a j) +
            a e * ∑ i ∈ s, (1 - a i) * ∏ j ∈ s.erase i, a j := by
        rw [Finset.sum_insert he]
        congr 1
        · simp [he]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hie : i ≠ e := fun h ↦ he (h ▸ hi)
          have heerase : e ∉ s.erase i :=
            fun h ↦ he (Finset.erase_subset i s h)
          rw [Finset.erase_insert_of_ne hie.symm, Finset.prod_insert heerase]
          ring
      rw [hsum, Finset.prod_insert he]
      calc
        (1 - a e) * (∏ j ∈ s, a j) +
            a e * ∑ i ∈ s, (1 - a i) * ∏ j ∈ s.erase i, a j
            ≤
          (1 - a e) * 1 + a e * (1 - ∏ i ∈ s, a i) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hprod1 (sub_nonneg.mpr hae1))
              (mul_le_mul_of_nonneg_left (ih ha0s ha1s) hae0)
        _ = 1 - a e * ∏ i ∈ s, a i := by ring

lemma sum_prod_erase_sub_prod_le_prod_sdiff_sub_prod
    {ι : Type*} [DecidableEq ι] (E I : Finset ι) (hIE : I ⊆ E)
    (a : ι → ℝ)
    (ha0 : ∀ i ∈ E, 0 ≤ a i)
    (ha1 : ∀ i ∈ E, a i ≤ 1) :
    (∑ e ∈ I, ((∏ f ∈ E.erase e, a f) - ∏ f ∈ E, a f))
      ≤ (∏ f ∈ E \ I, a f) - ∏ f ∈ E, a f := by
  let O := E \ I
  have hOI : Disjoint O I := Finset.sdiff_disjoint
  have hOunionI : O ∪ I = E := Finset.sdiff_union_of_subset hIE
  have hO0 : ∀ f ∈ O, 0 ≤ a f := by
    intro f hf
    change f ∈ E \ I at hf
    exact ha0 f (Finset.mem_sdiff.mp hf).1
  have hI0 : ∀ f ∈ I, 0 ≤ a f :=
    fun f hf ↦ ha0 f (hIE hf)
  have hI1 : ∀ f ∈ I, a f ≤ 1 :=
    fun f hf ↦ ha1 f (hIE hf)
  have hOprod0 : 0 ≤ ∏ f ∈ O, a f := Finset.prod_nonneg hO0
  have hfull :
      (∏ f ∈ E, a f) = (∏ f ∈ O, a f) * ∏ f ∈ I, a f := by
    rw [← Finset.prod_union hOI, hOunionI]
  have hterm : ∀ e ∈ I,
      ((∏ f ∈ E.erase e, a f) - ∏ f ∈ E, a f)
        =
      (∏ f ∈ O, a f) * ((1 - a e) * ∏ f ∈ I.erase e, a f) := by
    intro e he
    have heE : e ∈ E := hIE he
    have heO : e ∉ O := by simp [O, he]
    have hset : E.erase e = O ∪ I.erase e := by
      dsimp [O]
      ext f
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hf
        by_cases hfI : f ∈ I
        · exact Or.inr ⟨hf.1, hfI⟩
        · exact Or.inl ⟨hf.2, hfI⟩
      · rintro (hf | hf)
        · exact ⟨fun h ↦ hf.2 (h ▸ he), hf.1⟩
        · exact ⟨hf.1, hIE hf.2⟩
    have hdis : Disjoint O (I.erase e) := hOI.mono_right (Finset.erase_subset e I)
    rw [hset, Finset.prod_union hdis, hfull]
    have hIprod := Finset.mul_prod_erase I a he
    rw [← hIprod]
    ring
  calc
    (∑ e ∈ I, ((∏ f ∈ E.erase e, a f) - ∏ f ∈ E, a f))
        =
      (∏ f ∈ O, a f) *
        ∑ e ∈ I, ((1 - a e) * ∏ f ∈ I.erase e, a f) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hterm
    _ ≤ (∏ f ∈ O, a f) * (1 - ∏ f ∈ I, a f) :=
      mul_le_mul_of_nonneg_left
        (sum_one_sub_mul_prod_erase_le_one_sub_prod I a hI0 hI1) hOprod0
    _ = (∏ f ∈ E \ I, a f) - ∏ f ∈ E, a f := by
      change (∏ f ∈ O, a f) * (1 - ∏ f ∈ I, a f) =
        (∏ f ∈ O, a f) - ∏ f ∈ E, a f
      rw [hfull]
      ring

lemma two_mul_sum_prod_erase_le_vertex_deleted_sum
    {V ι : Type*} [Fintype V] [DecidableEq ι]
    (E : Finset ι) (I : V → Finset ι)
    (hIE : ∀ v, I v ⊆ E)
    (hdouble : ∀ f : ι → ℝ,
      (∑ v, ∑ e ∈ I v, f e) = 2 * ∑ e ∈ E, f e)
    (a : ι → ℝ)
    (ha0 : ∀ e ∈ E, 0 ≤ a e)
    (ha1 : ∀ e ∈ E, a e ≤ 1) :
    2 * (∑ e ∈ E, ∏ f ∈ E.erase e, a f)
      ≤
    (∑ v, ∏ f ∈ E \ I v, a f) +
      (2 * (E.card : ℝ) - (Fintype.card V : ℝ)) * ∏ f ∈ E, a f := by
  let K : ℝ := ∏ f ∈ E, a f
  let B : ℝ := ∑ e ∈ E, ∏ f ∈ E.erase e, a f
  let S : ℝ := ∑ v, ∏ f ∈ E \ I v, a f
  have hv (v : V) :
      (∑ e ∈ I v, ((∏ f ∈ E.erase e, a f) - K))
        ≤ (∏ f ∈ E \ I v, a f) - K := by
    exact sum_prod_erase_sub_prod_le_prod_sdiff_sub_prod
      E (I v) (hIE v) a ha0 ha1
  have hsum :
      (∑ v, ∑ e ∈ I v, ((∏ f ∈ E.erase e, a f) - K))
        ≤ ∑ v, ((∏ f ∈ E \ I v, a f) - K) :=
    Finset.sum_le_sum fun v _ ↦ hv v
  rw [hdouble] at hsum
  have hleft :
      (∑ e ∈ E, ((∏ f ∈ E.erase e, a f) - K))
        = B - (E.card : ℝ) * K := by
    rw [Finset.sum_sub_distrib]
    simp [B]
  have hright :
      (∑ v, ((∏ f ∈ E \ I v, a f) - K))
        = S - (Fintype.card V : ℝ) * K := by
    rw [Finset.sum_sub_distrib]
    simp [S]
  rw [hleft, hright] at hsum
  change 2 * B ≤ S +
    (2 * (E.card : ℝ) - (Fintype.card V : ℝ)) * K
  calc
    2 * B =
        2 * (B - (E.card : ℝ) * K) + 2 * (E.card : ℝ) * K := by ring
    _ ≤
        (S - (Fintype.card V : ℝ) * K) + 2 * (E.card : ℝ) * K :=
      by simpa [add_comm] using add_le_add_right hsum (2 * (E.card : ℝ) * K)
    _ = S + (2 * (E.card : ℝ) - (Fintype.card V : ℝ)) * K := by ring

end PureChordal
