import TreeApex.Entropy.RelEnt
import TreeApex.Graph.RecTree

/-!
# Extension along a tree, in relative-entropy form

Paper `lem:tree-extension` (plan §2.5), for an arbitrary finite law.  Let `Q` be a law of
`(S, X, Y)` on finite types with `Q(s, x, y) = Q(s, y, x)` (`eq:exchangeability`), let
`μ(s, x) = ∑_y Q(s, x, y)` be its `(S, X)` marginal (`marg`) and `K(s, x, y) = Q(s, x, y) / μ(s, x)`
the transition kernel (`kern`; rows at states of mass zero are zero and are never visited).
Along the recursive tree `par` (vertex `i + 1` attached to `parV par i`) the **tree law** is

```
  P₀(s, x) = μ(s, x₀),      P_{m+1}(s, snoc x y) = P_m(s, x) · K(s, x_{par m}, y)     (eq:tree-law)
```

so `P₁ = Q`.  Reference weights `ρ_m(s, x) = ρ_S(s) ∏_u ν(s, x_u) ∏_i η(x_{parV i}, x_{i+1})` are
attached to the same tree; for the host they are the weights of `T^{+k}`.  With
`g = ∑_{s,a} μ(s, a) relEnt (ν(s,·) η(a,·)) (K(s, a, ·))` (the weighted `H(Y | S, X)`):

* `treeLaw_sum` — `P_m` is a law (TE1);
* `treeLaw_marginal` — every vertex has marginal `μ`, tested against arbitrary functions (TE2);
* `treeLaw_support` — `P_m ≠ 0 ⇒ ρ_m ≠ 0` (TE5);
* `relEnt_treeLaw` — `relEnt ρ_{m+1} P_{m+1} = relEnt ρ_B Q + m g` (`eq:tree-entropy`, TE4), where
  `ρ_B(s, x, y) = ρ_S(s) ν(s, x) ν(s, y) η(x, y)`;
* `relEnt_book_add_le_log` — with Gibbs: `relEnt ρ_B Q + m g ≤ log ∑ ρ_{m+1}`.

The paper's edge marginals (TE3) are not needed: the support is proved directly.
-/

open Finset

namespace TreeApex

/-- A law of `(S, X, Y)` that is symmetric in `X` and `Y`. -/
structure SymLaw (S X : Type*) [Fintype S] [Fintype X] where
  Q : S → X → X → ℝ
  nonneg : ∀ s x y, 0 ≤ Q s x y
  sum_eq : ∑ s, ∑ x, ∑ y, Q s x y = 1
  symm : ∀ s x y, Q s x y = Q s y x

/-- Reference factors: `ρ_S` on `S`, `ν` on vertices, `η` on edges; nonnegative, and nonzero
wherever `Q` is. -/
structure RefFactors {S X : Type*} [Fintype S] [Fintype X] (L : SymLaw S X) where
  ρS : S → ℝ
  ν : S → X → ℝ
  η : X → X → ℝ
  ρS_nonneg : ∀ s, 0 ≤ ρS s
  ν_nonneg : ∀ s x, 0 ≤ ν s x
  η_nonneg : ∀ x y, 0 ≤ η x y
  supp : ∀ s x y, L.Q s x y ≠ 0 → ρS s ≠ 0 ∧ ν s x ≠ 0 ∧ ν s y ≠ 0 ∧ η x y ≠ 0

variable {S X : Type*} [Fintype S] [Fintype X] (L : SymLaw S X)

namespace SymLaw

/-- The `(S, X)` marginal `μ(s, x) = ∑_y Q(s, x, y)`. -/
noncomputable def marg (s : S) (x : X) : ℝ := ∑ y, L.Q s x y

/-- The transition kernel `K(s, x, y) = Q(s, x, y) / μ(s, x)`. -/
noncomputable def kern (s : S) (x y : X) : ℝ := L.Q s x y / L.marg s x

lemma marg_nonneg (s : S) (x : X) : 0 ≤ L.marg s x := sum_nonneg fun y _ => L.nonneg s x y

lemma kern_nonneg (s : S) (x y : X) : 0 ≤ L.kern s x y :=
  div_nonneg (L.nonneg s x y) (L.marg_nonneg s x)

lemma Q_le_marg (s : S) (x y : X) : L.Q s x y ≤ L.marg s x :=
  single_le_sum (fun z _ => L.nonneg s x z) (mem_univ y)

lemma marg_ne_zero_of_Q {s : S} {x y : X} (h : L.Q s x y ≠ 0) : L.marg s x ≠ 0 :=
  ((L.nonneg s x y).lt_of_ne h.symm |>.trans_le (L.Q_le_marg s x y)).ne'

lemma Q_eq_zero_of_marg {s : S} {x : X} (h : L.marg s x = 0) (y : X) : L.Q s x y = 0 := by
  by_contra hy
  exact L.marg_ne_zero_of_Q hy h

/-- `μ(s, x) K(s, x, y) = Q(s, x, y)`, also when `μ(s, x) = 0`. -/
lemma marg_mul_kern (s : S) (x y : X) : L.marg s x * L.kern s x y = L.Q s x y := by
  by_cases h : L.marg s x = 0
  · rw [h, zero_mul, L.Q_eq_zero_of_marg h]
  · rw [kern, mul_div_cancel₀ _ h]

lemma sum_kern {s : S} {x : X} (h : L.marg s x ≠ 0) : ∑ y, L.kern s x y = 1 := by
  simp only [kern]
  rw [← sum_div]
  exact div_self h

lemma Q_ne_zero_of_kern {s : S} {x y : X} (h : L.kern s x y ≠ 0) : L.Q s x y ≠ 0 :=
  fun hQ => h (by rw [kern, hQ, zero_div])

lemma sum_marg : ∑ s, ∑ x, L.marg s x = 1 := L.sum_eq

end SymLaw

/-! ### Snoc bookkeeping -/

/-- `(S × (Fin (m+1) → X)) × X ≃ S × (Fin (m+2) → X)`, adding a last vertex. -/
def snocEquiv' (S X : Type*) (m : ℕ) : (S × (Fin (m + 1) → X)) × X ≃ S × (Fin (m + 2) → X) where
  toFun p := (p.1.1, Fin.snoc p.1.2 p.2)
  invFun q := ((q.1, Fin.init q.2), q.2 (Fin.last _))
  left_inv := by rintro ⟨⟨s, x⟩, y⟩; simp [Fin.init_snoc, Fin.snoc_last]
  right_inv := by rintro ⟨s, x⟩; simp [Fin.snoc_init_self]

lemma sum_snoc {M : Type*} [AddCommMonoid M] {m : ℕ} (f : S × (Fin (m + 2) → X) → M) :
    ∑ q, f q = ∑ s, ∑ x : Fin (m + 1) → X, ∑ y, f (s, Fin.snoc x y) := by
  rw [← (snocEquiv' S X m).sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
  rfl

lemma sum_fin_one {M : Type*} [AddCommMonoid M] (f : S × (Fin 1 → X) → M) :
    ∑ q, f q = ∑ s, ∑ a, f (s, fun _ => a) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  exact ((Equiv.funUnique (Fin 1) X).symm.sum_comp fun x => f (s, x)).symm

/-- The parent of the new vertex `m + 1`, as an old vertex. -/
def parOld (par : ℕ → ℕ) (m : ℕ) : Fin (m + 1) := ⟨min (par m) m, by omega⟩

lemma parV_last (par : ℕ → ℕ) (m : ℕ) : parV par (Fin.last m) = (parOld par m).castSucc :=
  Fin.ext rfl

lemma parV_castSucc (par : ℕ → ℕ) {m : ℕ} (i : Fin m) :
    parV par i.castSucc = (parV par i).castSucc :=
  Fin.ext rfl

/-! ### The tree law and its reference weights -/

namespace SymLaw

/-- **The tree law** (`eq:tree-law`) along the recursive tree `par`. -/
noncomputable def treeLaw (par : ℕ → ℕ) : (m : ℕ) → S × (Fin (m + 1) → X) → ℝ
  | 0 => fun q => L.marg q.1 (q.2 0)
  | m + 1 => fun q => treeLaw par m (q.1, Fin.init q.2) *
      L.kern q.1 (Fin.init q.2 (parOld par m)) (q.2 (Fin.last _))

end SymLaw

variable {L}

/-- Reference weights `ρ_S(s) ∏_u ν(s, x_u) ∏_i η(x_{parV i}, x_{i+1})` of the tree. -/
noncomputable def RefFactors.treeWeight (R : RefFactors L) (par : ℕ → ℕ) (m : ℕ)
    (q : S × (Fin (m + 1) → X)) : ℝ :=
  R.ρS q.1 * (∏ u, R.ν q.1 (q.2 u)) * ∏ i : Fin m, R.η (q.2 (parV par i)) (q.2 i.succ)

/-- The book reference `ρ_B(s, x, y) = ρ_S(s) ν(s, x) ν(s, y) η(x, y)`. -/
noncomputable def RefFactors.bookWeight (R : RefFactors L) (q : S × X × X) : ℝ :=
  R.ρS q.1 * R.ν q.1 q.2.1 * R.ν q.1 q.2.2 * R.η q.2.1 q.2.2

variable (L)

namespace SymLaw

/-- The weighted `H(Y | S, X)`: `g = ∑_{s,a} μ(s, a) relEnt (ν(s,·) η(a,·)) (K(s, a, ·))`. -/
noncomputable def condRelEnt (R : RefFactors L) : ℝ :=
  ∑ s, ∑ a, L.marg s a * relEnt (fun y => R.ν s y * R.η a y) (L.kern s a)

lemma treeLaw_snoc (par : ℕ → ℕ) {m : ℕ} (s : S) (x : Fin (m + 1) → X) (y : X) :
    L.treeLaw par (m + 1) (s, Fin.snoc x y) = L.treeLaw par m (s, x) * L.kern s (x (parOld par m)) y := by
  simp only [treeLaw, Fin.init_snoc, Fin.snoc_last]

lemma treeWeight_snoc (R : RefFactors L) (par : ℕ → ℕ) {m : ℕ} (s : S) (x : Fin (m + 1) → X)
    (y : X) :
    R.treeWeight par (m + 1) (s, Fin.snoc x y)
      = R.treeWeight par m (s, x) * (R.ν s y * R.η (x (parOld par m)) y) := by
  have h1 : ∏ u : Fin (m + 2), R.ν s ((Fin.snoc x y : Fin (m + 2) → X) u)
      = (∏ u : Fin (m + 1), R.ν s (x u)) * R.ν s y := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have h2 : ∏ i : Fin (m + 1), R.η ((Fin.snoc x y : Fin (m + 2) → X) (parV par i))
        ((Fin.snoc x y : Fin (m + 2) → X) i.succ)
      = (∏ i : Fin m, R.η (x (parV par i)) (x i.succ)) * R.η (x (parOld par m)) y := by
    rw [Fin.prod_univ_castSucc]
    simp only [parV_castSucc, parV_last, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_castSucc,
      Fin.snoc_last]
  simp only [RefFactors.treeWeight]
  rw [h1, h2]
  ring

lemma treeLaw_nonneg (par : ℕ → ℕ) : ∀ (m : ℕ) (q : S × (Fin (m + 1) → X)), 0 ≤ L.treeLaw par m q
  | 0, _ => L.marg_nonneg _ _
  | m + 1, _ => mul_nonneg (treeLaw_nonneg par m _) (L.kern_nonneg _ _ _)

lemma treeWeight_nonneg (R : RefFactors L) (par : ℕ → ℕ) (m : ℕ) (q : S × (Fin (m + 1) → X)) :
    0 ≤ R.treeWeight par m q :=
  mul_nonneg (mul_nonneg (R.ρS_nonneg _) (prod_nonneg fun _ _ => R.ν_nonneg _ _))
    (prod_nonneg fun _ _ => R.η_nonneg _ _)

/-- **Support of the tree law** (TE5, with the marginal support used by TE1). -/
lemma treeLaw_support (R : RefFactors L) (par : ℕ → ℕ) :
    ∀ (m : ℕ) (s : S) (x : Fin (m + 1) → X), L.treeLaw par m (s, x) ≠ 0 →
      (∀ u, L.marg s (x u) ≠ 0) ∧ R.treeWeight par m (s, x) ≠ 0
  | 0, s, x, h => by
    have h0 : L.marg s (x 0) ≠ 0 := h
    obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero h0
    obtain ⟨h1, h2, -, -⟩ := R.supp s (x 0) y hy
    refine ⟨fun u => by rwa [Subsingleton.elim (α := Fin 1) u 0], ?_⟩
    simp only [RefFactors.treeWeight, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    exact mul_ne_zero h1 h2
  | m + 1, s, x, h => by
    rw [← Fin.snoc_init_self x] at h ⊢
    set x' := Fin.init x
    set y := x (Fin.last _)
    rw [treeLaw_snoc] at h
    obtain ⟨hP, hK⟩ := mul_ne_zero_iff.mp h
    obtain ⟨hm, hw⟩ := treeLaw_support R par m s x' hP
    have hQ := L.Q_ne_zero_of_kern hK
    obtain ⟨-, -, hν, hη⟩ := R.supp s _ _ hQ
    refine ⟨fun u => ?_, ?_⟩
    · induction u using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        exact L.marg_ne_zero_of_Q (by rwa [L.symm] at hQ)
      | cast u => rw [Fin.snoc_castSucc]; exact hm u
    · rw [treeWeight_snoc]
      exact mul_ne_zero hw (mul_ne_zero hν hη)

/-- Summing out the last vertex gives back the previous tree law (pointwise). -/
lemma treeLaw_sum_last (R : RefFactors L) (par : ℕ → ℕ) {m : ℕ} (s : S) (x : Fin (m + 1) → X) :
    ∑ y, L.treeLaw par (m + 1) (s, Fin.snoc x y) = L.treeLaw par m (s, x) := by
  simp only [treeLaw_snoc, ← mul_sum]
  by_cases h : L.treeLaw par m (s, x) = 0
  · rw [h, zero_mul]
  · rw [L.sum_kern ((treeLaw_support L R par m s x h).1 _), mul_one]

/-- **The tree law is a law** (TE1). -/
theorem treeLaw_sum (R : RefFactors L) (par : ℕ → ℕ) :
    ∀ m : ℕ, ∑ q, L.treeLaw par m q = 1
  | 0 => by
    rw [sum_fin_one]
    exact L.sum_marg
  | m + 1 => by
    rw [sum_snoc]
    simp only [treeLaw_sum_last L R par]
    rw [← treeLaw_sum R par m, Fintype.sum_prod_type]

/-- **Vertex marginals** (TE2): every vertex of the tree has the `(S, X)` marginal `μ`, tested
against an arbitrary function. -/
theorem treeLaw_marginal (R : RefFactors L) (par : ℕ → ℕ) :
    ∀ (m : ℕ) (u : Fin (m + 1)) (f : S → X → ℝ),
      ∑ q, L.treeLaw par m q * f q.1 (q.2 u) = ∑ s, ∑ a, L.marg s a * f s a
  | 0, u, f => by
    rw [sum_fin_one]
    rfl
  | m + 1, u, f => by
    rw [sum_snoc]
    induction u using Fin.lastCases with
    | cast u =>
      simp only [Fin.snoc_castSucc]
      have h : ∀ s (x : Fin (m + 1) → X), ∑ y, L.treeLaw par (m + 1) (s, Fin.snoc x y) * f s (x u)
          = L.treeLaw par m (s, x) * f s (x u) := fun s x => by
        rw [← sum_mul, treeLaw_sum_last L R par]
      simp only [h]
      rw [← treeLaw_marginal R par m u f, Fintype.sum_prod_type]
    | last =>
      simp only [Fin.snoc_last, treeLaw_snoc]
      have h : ∀ s (x : Fin (m + 1) → X),
          ∑ y, L.treeLaw par m (s, x) * L.kern s (x (parOld par m)) y * f s y
            = L.treeLaw par m (s, x) * (∑ y, L.kern s (x (parOld par m)) y * f s y) :=
        fun s x => by rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
      simp only [h]
      have hIH := treeLaw_marginal R par m (parOld par m) fun s b => ∑ y, L.kern s b y * f s y
      rw [Fintype.sum_prod_type] at hIH
      rw [hIH]
      simp only [mul_sum, ← mul_assoc, L.marg_mul_kern]
      refine sum_congr rfl fun s _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      rw [SymLaw.marg, sum_mul]
      exact sum_congr rfl fun b _ => by rw [L.symm]

/-- **One leaf adds `g`** to the relative entropy (the inductive step of `eq:tree-entropy`). -/
theorem relEnt_treeLaw_succ (R : RefFactors L) (par : ℕ → ℕ) (m : ℕ) :
    relEnt (R.treeWeight par (m + 1)) (L.treeLaw par (m + 1))
      = relEnt (R.treeWeight par m) (L.treeLaw par m) + L.condRelEnt R := by
  rw [← relEnt_equiv (snocEquiv' S X m)]
  have hp : L.treeLaw par (m + 1) ∘ snocEquiv' S X m
      = fun q => L.treeLaw par m q.1 * L.kern q.1.1 (q.1.2 (parOld par m)) q.2 := by
    funext ⟨⟨s, x⟩, y⟩; exact L.treeLaw_snoc par s x y
  have hρ : R.treeWeight par (m + 1) ∘ snocEquiv' S X m
      = fun q => R.treeWeight par m q.1 * (R.ν q.1.1 q.2 * R.η (q.1.2 (parOld par m)) q.2) := by
    funext ⟨⟨s, x⟩, y⟩; exact L.treeWeight_snoc R par s x y
  rw [hp, hρ, relEnt_prod (R.treeWeight par m) (L.treeLaw par m)
    (fun q y => R.ν q.1 y * R.η (q.2 (parOld par m)) y) (fun q y => L.kern q.1 (q.2 (parOld par m)) y)]
  · congr 1
    exact treeLaw_marginal L R par m (parOld par m)
      (fun s a => relEnt (fun y => R.ν s y * R.η a y) (L.kern s a))
  · rintro ⟨s, x⟩ h
    exact L.sum_kern ((treeLaw_support L R par m s x h).1 _)
  · rintro ⟨s, x⟩ h
    exact (treeLaw_support L R par m s x h).2
  · rintro ⟨s, x⟩ y - hK
    obtain ⟨-, -, hν, hη⟩ := R.supp s _ _ (L.Q_ne_zero_of_kern hK)
    exact mul_ne_zero hν hη

/-- The one-edge tree law is `Q`, with the book reference: `relEnt ρ₁ P₁ = relEnt ρ_B Q`. -/
theorem relEnt_treeLaw_one (R : RefFactors L) (par : ℕ → ℕ) :
    relEnt (R.treeWeight par 1) (L.treeLaw par 1)
      = relEnt R.bookWeight (fun q : S × X × X => L.Q q.1 q.2.1 q.2.2) := by
  rw [← relEnt_equiv ((Equiv.refl S).prodCongr (piFinTwoEquiv fun _ => X)) R.bookWeight]
  congr 1
  · funext ⟨s, x⟩
    simp only [Function.comp_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id,
      piFinTwoEquiv_apply, RefFactors.bookWeight, RefFactors.treeWeight, Fin.prod_univ_succ,
      Fin.prod_univ_zero, mul_one]
    have hp : parV par (0 : Fin 1) = 0 := Fin.ext (by simp [parV])
    rw [hp]
    simp only [Fin.succ_zero_eq_one]
    ring
  · funext ⟨s, x⟩
    simp only [Function.comp_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id,
      piFinTwoEquiv_apply, treeLaw]
    have h0 : (Fin.init x) 0 = x 0 := rfl
    have hp : (Fin.init x) (parOld par 0) = x 0 := by
      rw [show parOld par 0 = 0 from Fin.ext (by simp [parOld])]; rfl
    rw [h0, hp]
    exact L.marg_mul_kern s (x 0) (x (Fin.last 1))

/-- **`eq:tree-entropy`, weighted** (TE4): `relEnt ρ_{m+1} P_{m+1} = relEnt ρ_B Q + m g`. -/
theorem relEnt_treeLaw (R : RefFactors L) (par : ℕ → ℕ) :
    ∀ m : ℕ, relEnt (R.treeWeight par (m + 1)) (L.treeLaw par (m + 1))
      = relEnt R.bookWeight (fun q : S × X × X => L.Q q.1 q.2.1 q.2.2) + m * L.condRelEnt R
  | 0 => by rw [relEnt_treeLaw_one, Nat.cast_zero, zero_mul, add_zero]
  | m + 1 => by
    rw [relEnt_treeLaw_succ, relEnt_treeLaw R par m, Nat.cast_succ]
    ring

/-- **The support bound along the tree** (`eq:support-global` with `eq:tree-entropy`):
`relEnt ρ_B Q + m g ≤ log ∑ ρ_{m+1}`. -/
theorem relEnt_book_add_le_log (R : RefFactors L) (par : ℕ → ℕ) (m : ℕ) :
    relEnt R.bookWeight (fun q : S × X × X => L.Q q.1 q.2.1 q.2.2) + m * L.condRelEnt R
      ≤ Real.log (∑ q, R.treeWeight par (m + 1) q) := by
  rw [← relEnt_treeLaw L R par m]
  refine relEnt_le_log_sum (L.treeLaw_nonneg par (m + 1)) (L.treeLaw_sum R par (m + 1))
    (L.treeWeight_nonneg R par (m + 1)) ?_
  rintro ⟨s, x⟩ h
  exact (L.treeLaw_support R par (m + 1) s x h).2

/-- The total reference weight is positive whenever `Q` is a law. -/
theorem sum_treeWeight_pos (R : RefFactors L) (par : ℕ → ℕ) (m : ℕ) :
    0 < ∑ q, R.treeWeight par m q :=
  sum_pos_of_support (L.treeLaw_sum R par m) (L.treeWeight_nonneg R par m) fun ⟨s, x⟩ h =>
    (L.treeLaw_support R par m s x h).2

end SymLaw

end TreeApex
