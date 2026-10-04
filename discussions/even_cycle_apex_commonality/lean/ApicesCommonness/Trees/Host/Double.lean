import ApicesCommonness.Trees.Host.ProbHost
import ApicesCommonness.Trees.Graph.RecTree

/-!
# Two colours on one host: the doubled host (plan T-D8)

The paper forms a graphon `U` on `[0,1]` with two half-size blocks carrying `W` and `1 − W`
(`eq:disjoint-union`) and uses `t(F, U) = 2^{−v(F)} m(F, W)` for connected `F`
(`eq:connected-blocks`).  On a host this is a finite construction: `K.double` lives on `Bool × V`,
with weights `w/2` on both copies, kernel `M` on the `true` block, `1 − M` on the `false` block and
`0` across.

`hostDens_double_of_connected`: for connected `F` on `v` vertices,
`t(F, K.double) = m(F, K) / 2^v` where `m(F, K) = t(F, M) + t(F, 1 − M)` (`Mh`).  The sum over
`Fin v → Bool × V` splits into colourings `c : Fin v → Bool` and vertex maps; a non-constant
colouring has a bichromatic edge (`Walk.exists_boundary_dart`), whose kernel value is `0`.
-/

open Finset SimpleGraph

namespace ApicesCommonness

namespace ProbHost

variable {V : Type*} [Fintype V] (K : ProbHost V)

/-- The complementary kernel `1 − M`. -/
def Mc : V → V → ℝ := fun x y => 1 - K.M x y

/-- `m(F) = t(F, M) + t(F, 1 − M)` on the host. -/
noncomputable def Mh {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] : ℝ :=
  hostDens K.w F K.M + hostDens K.w F K.Mc

/-- The colour kernel: `M` on `true`, `1 − M` on `false`. -/
def colM (b : Bool) : V → V → ℝ := if b then K.M else K.Mc

lemma colM_symm (b : Bool) (x y : V) : K.colM b x y = K.colM b y x := by
  cases b <;> simp [colM, Mc, K.M_symm x y]

lemma colM_nonneg (b : Bool) (x y : V) : 0 ≤ K.colM b x y := by
  cases b <;> simp [colM, Mc, K.M_nonneg, K.M_le_one]

lemma colM_le_one (b : Bool) (x y : V) : K.colM b x y ≤ 1 := by
  cases b <;> simp [colM, Mc, K.M_nonneg, K.M_le_one]

/-- The complementary host (kernel `1 − M`). -/
def compl : ProbHost V where
  w := K.w
  w_nonneg := K.w_nonneg
  w_sum := K.w_sum
  M := K.Mc
  M_symm x y := by simp [Mc, K.M_symm x y]
  M_nonneg x y := by simp [Mc, K.M_le_one]
  M_le_one x y := by simp [Mc, K.M_nonneg]

/-- **The doubled host** on `Bool × V`. -/
noncomputable def double : ProbHost (Bool × V) where
  w p := K.w p.2 / 2
  w_nonneg p := div_nonneg (K.w_nonneg _) zero_le_two
  w_sum := by
    rw [Fintype.sum_prod_type]
    simp only [← sum_div, K.w_sum, sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul]
    norm_num
  M p q := if p.1 = q.1 then K.colM p.1 p.2 q.2 else 0
  M_symm p q := by
    by_cases h : p.1 = q.1
    · rw [if_pos h, if_pos h.symm, h, K.colM_symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  M_nonneg p q := by
    split_ifs
    · exact K.colM_nonneg _ _ _
    · exact le_rfl
  M_le_one p q := by
    split_ifs
    · exact K.colM_le_one _ _ _
    · exact zero_le_one

/-- A non-constant colouring of a connected graph has a bichromatic edge. -/
lemma exists_bichromatic_edge {v : ℕ} {F : SimpleGraph (Fin v)} [DecidableRel F.Adj]
    (hF : F.Connected) {c : Fin v → Bool} (h₁ : c ≠ fun _ => true) (h₂ : c ≠ fun _ => false) :
    ∃ p ∈ edgePairs F, c p.1 ≠ c p.2 := by
  obtain ⟨i, hi⟩ : ∃ i, c i = true := by
    by_contra h
    push Not at h
    exact h₂ (funext fun i => by simpa using h i)
  obtain ⟨i', hi'⟩ : ∃ i', c i' = false := by
    by_contra h
    push Not at h
    exact h₁ (funext fun i => by simpa using h i)
  obtain ⟨p⟩ := hF.preconnected i i'
  obtain ⟨d, -, hd₁, hd₂⟩ := p.exists_boundary_dart {t | c t = true} hi (by simp [hi'])
  simp only [Set.mem_setOf_eq] at hd₁ hd₂
  refine ⟨sortPair d.fst d.snd, sortPair_mem_edgePairs d.adj, ?_⟩
  unfold sortPair
  split_ifs
  · rw [hd₁]; exact Ne.symm (by simpa using hd₂)
  · rw [hd₁]; simpa using hd₂

/-- **`eq:connected-blocks`, host form**: `t(F, K.double) = m(F, K) / 2^v` for connected `F`. -/
theorem hostDens_double_of_connected {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (hF : F.Connected) : hostDens K.double.w F K.double.M = K.Mh F / 2 ^ v := by
  haveI : Nonempty (Fin v) := hF.nonempty
  unfold hostDens
  rw [← (Equiv.arrowProdEquivProdArrow (Fin v) (fun _ => Bool) (fun _ => V)).symm.sum_comp,
    Fintype.sum_prod_type]
  have hne : (fun _ : Fin v => true) ≠ fun _ => false := by
    intro h
    have := congrFun h (Classical.arbitrary _)
    simp at this
  rw [Fintype.sum_eq_add (fun _ => true) (fun _ => false) hne]
  · simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, double, if_true, colM,
      Bool.false_eq_true, if_false, prod_div_distrib, prod_const, card_univ, Fintype.card_fin,
      div_mul_eq_mul_div, ← sum_div, Mh, add_div]
    rfl
  · rintro c ⟨h₁, h₂⟩
    obtain ⟨p, hp, hc⟩ := exists_bichromatic_edge hF h₁ h₂
    refine sum_eq_zero fun x _ => ?_
    refine mul_eq_zero_of_right _ (prod_eq_zero hp ?_)
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, double]
    exact if_neg hc

end ProbHost

end ApicesCommonness
