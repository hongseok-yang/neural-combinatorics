import EvenCycleApex.Certificate.Mask

/-!
# Rooted quadratic forms and their expansion

Blueprint `def:rooted-features`, `lem:rooted-positivity`, `lem:rooted-expansion`.

A block has `r` roots and features on `r + k` formal vertices (roots `0, …, r − 1`, then `k` new
vertices).  Its two copies live on `Fin (r + (k + (k + p)))` — roots, first copy, second copy,
padding; for the certificate's shapes this is `Fin 6`:

* `emb1 = Fin.castLE` puts a feature on the roots and the first copy;
* `emb2` puts it on the roots and the second copy (new vertices shifted by `k`).

`edgeDensity_rooted_split` (the one generic splitting lemma of plan §2.5): if `F_a, F_b` have no
root–root edge, the density of `T ∪ emb1(F_a) ∪ emb2(F_b)` is
`∑_z ∏ w(zᵢ) ∏_{e ∈ T} U(z_e) · Φ_a(z) Φ_b(z)`, where `Φ_F(z)` integrates out the new vertices
(`featDensity`); the padding integrates to one.
-/

open Finset

namespace EvenCycleApex

variable {d r k p : ℕ}

/-- A root, in the two-copy vertex set. -/
def rootV (r k p : ℕ) (i : Fin r) : Fin (r + (k + (k + p))) := Fin.castAdd (k + (k + p)) i

/-- A vertex of the first copy. -/
def copy1V (r k p : ℕ) (j : Fin k) : Fin (r + (k + (k + p))) :=
  Fin.natAdd r (Fin.castAdd (k + p) j)

/-- A vertex of the second copy. -/
def copy2V (r k p : ℕ) (j : Fin k) : Fin (r + (k + (k + p))) :=
  Fin.natAdd r (Fin.natAdd k (Fin.castAdd p j))

/-- A feature vertex placed in the first copy. -/
def emb1 (r k p : ℕ) (v : Fin (r + k)) : Fin (r + (k + (k + p))) := Fin.addCases (rootV r k p) (copy1V r k p) v

/-- A feature vertex placed in the second copy. -/
def emb2 (r k p : ℕ) (v : Fin (r + k)) : Fin (r + (k + (k + p))) := Fin.addCases (rootV r k p) (copy2V r k p) v

lemma val_emb1 (v : Fin (r + k)) : (emb1 r k p v : ℕ) = v := by
  induction v using Fin.addCases <;> simp [emb1, rootV, copy1V]

lemma val_emb2 (v : Fin (r + k)) :
    (emb2 r k p v : ℕ) = if (v : ℕ) < r then (v : ℕ) else (v : ℕ) + k := by
  induction v using Fin.addCases with
  | left i => simp [emb2, rootV, i.isLt]
  | right j => simp [emb2, copy2V]; omega

lemma emb1_injective : Function.Injective (emb1 r k p) := fun a b h => by
  have := congrArg Fin.val h
  rw [val_emb1, val_emb1] at this
  exact Fin.ext this

lemma emb2_injective : Function.Injective (emb2 r k p) := fun a b h => by
  have := congrArg Fin.val h
  rw [val_emb2, val_emb2] at this
  have ha := a.isLt; have hb := b.isLt
  refine Fin.ext ?_
  split_ifs at this <;> omega

/-- The density of a feature `F` over the new vertices, at the root values `z`. -/
def featDensity (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) (F : Finset (Fin (r + k) × Fin (r + k)))
    (z : Fin r → Fin d) : ℝ :=
  ∑ y : Fin k → Fin d, (∏ j, w (y j)) * ∏ e ∈ F, L (Fin.append z y e.1) (Fin.append z y e.2)

/-- A feature has no root–root edge. -/
def NoRootEdge (r : ℕ) {k : ℕ} (F : Finset (Fin (r + k) × Fin (r + k))) : Prop :=
  ∀ e ∈ F, r ≤ (e.1 : ℕ) ∨ r ≤ (e.2 : ℕ)

/-- The two-copy edge set `T ∪ emb1(F_a) ∪ emb2(F_b)`. -/
def rootedEdges (r k p : ℕ) (T : Finset (Fin r × Fin r)) (Fa Fb : Finset (Fin (r + k) × Fin (r + k))) :
    Finset (Fin (r + (k + (k + p))) × Fin (r + (k + (k + p)))) :=
  T.image (fun e => (rootV r k p e.1, rootV r k p e.2)) ∪
    Fa.image (fun e => (emb1 r k p e.1, emb1 r k p e.2)) ∪
    Fb.image (fun e => (emb2 r k p e.1, emb2 r k p e.2))

section Split

variable {α : Type*} (z : Fin r → α) (y1 y2 : Fin k → α) (q : Fin p → α)

/-- The assembled vertex map of roots, two copies and padding. -/
def assemble : Fin (r + (k + (k + p))) → α := Fin.append z (Fin.append y1 (Fin.append y2 q))

lemma assemble_rootV (i : Fin r) : assemble z y1 y2 q (rootV r k p i) = z i := by
  simp [assemble, rootV]

lemma assemble_emb1 (v : Fin (r + k)) : assemble z y1 y2 q (emb1 r k p v) = Fin.append z y1 v := by
  induction v using Fin.addCases <;> simp [assemble, emb1, rootV, copy1V]

lemma assemble_emb2 (v : Fin (r + k)) : assemble z y1 y2 q (emb2 r k p v) = Fin.append z y2 v := by
  induction v using Fin.addCases <;> simp [assemble, emb2, rootV, copy2V]

end Split

/-- Summing over the assembled vertex maps. -/
lemma sum_assemble {M : Type*} [AddCommMonoid M] (f : (Fin (r + (k + (k + p))) → Fin d) → M) :
    ∑ x, f x = ∑ z : Fin r → Fin d, ∑ y1 : Fin k → Fin d, ∑ y2 : Fin k → Fin d,
      ∑ q : Fin p → Fin d, f (assemble z y1 y2 q) := by
  rw [← (appendEquiv r (k + (k + p)) (Fin d)).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun z _ => ?_
  rw [← (appendEquiv k (k + p) (Fin d)).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun y1 _ => ?_
  rw [← (appendEquiv k p (Fin d)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma prod_weights_assemble (w : Fin d → ℝ) (z : Fin r → Fin d) (y1 y2 : Fin k → Fin d)
    (q : Fin p → Fin d) :
    ∏ v, w (assemble z y1 y2 q v)
      = (∏ i, w (z i)) * (∏ j, w (y1 j)) * (∏ j, w (y2 j)) * ∏ j, w (q j) := by
  simp only [assemble, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  ring

lemma rootedEdges_disjoint₁ (T : Finset (Fin r × Fin r)) {Fa : Finset (Fin (r + k) × Fin (r + k))}
    (hFa : NoRootEdge r Fa) :
    Disjoint (T.image fun e => (rootV r k p e.1, rootV r k p e.2))
      (Fa.image fun e => (emb1 r k p e.1, emb1 r k p e.2)) := by
  rw [disjoint_left]
  intro x hx hy
  obtain ⟨e, _, rfl⟩ := mem_image.mp hx
  obtain ⟨f, hf, hfe⟩ := mem_image.mp hy
  have h1 := congrArg (fun x : Fin _ × Fin _ => (x.1 : ℕ)) hfe
  have h2 := congrArg (fun x : Fin _ × Fin _ => (x.2 : ℕ)) hfe
  simp only [val_emb1, rootV, Fin.val_castAdd] at h1 h2
  have := e.1.isLt; have := e.2.isLt
  rcases hFa f hf with h | h <;> omega

lemma rootedEdges_disjoint₂ (T : Finset (Fin r × Fin r)) (Fa : Finset (Fin (r + k) × Fin (r + k)))
    {Fb : Finset (Fin (r + k) × Fin (r + k))} (hFb : NoRootEdge r Fb) :
    Disjoint ((T.image fun e => (rootV r k p e.1, rootV r k p e.2)) ∪
        Fa.image fun e => (emb1 r k p e.1, emb1 r k p e.2))
      (Fb.image fun e => (emb2 r k p e.1, emb2 r k p e.2)) := by
  rw [disjoint_left]
  intro x hx hy
  obtain ⟨f, hf, rfl⟩ := mem_image.mp hy
  have hbig : r + k ≤ (emb2 r k p f.1 : ℕ) ∨ r + k ≤ (emb2 r k p f.2 : ℕ) := by
    rw [val_emb2, val_emb2]
    rcases hFb f hf with h | h
    · left; rw [if_neg (by omega)]; omega
    · right; rw [if_neg (by omega)]; omega
  rcases mem_union.mp hx with h | h
  · obtain ⟨e, _, he⟩ := mem_image.mp h
    have h1 := congrArg (fun x : Fin _ × Fin _ => (x.1 : ℕ)) he
    have h2 := congrArg (fun x : Fin _ × Fin _ => (x.2 : ℕ)) he
    simp only [rootV, Fin.val_castAdd] at h1 h2
    have := e.1.isLt; have := e.2.isLt
    omega
  · obtain ⟨e, _, he⟩ := mem_image.mp h
    have h1 := congrArg (fun x : Fin _ × Fin _ => (x.1 : ℕ)) he
    have h2 := congrArg (fun x : Fin _ × Fin _ => (x.2 : ℕ)) he
    simp only [val_emb1] at h1 h2
    have := e.1.isLt; have := e.2.isLt
    omega

/-- **The splitting lemma** (plan §2.5): the density of `T ∪ emb1(F_a) ∪ emb2(F_b)` is
`∑_z ∏ w(zᵢ) · ∏_{e ∈ T} L(z_e) · Φ_a(z) · Φ_b(z)`. -/
theorem edgeDensity_rooted_split (w : Fin d → ℝ) (hw : ∑ j, w j = 1) (L : Fin d → Fin d → ℝ)
    (T : Finset (Fin r × Fin r)) (Fa Fb : Finset (Fin (r + k) × Fin (r + k)))
    (hFa : NoRootEdge r Fa) (hFb : NoRootEdge r Fb) :
    edgeDensity w (rootedEdges r k p T Fa Fb) L
      = ∑ z : Fin r → Fin d, (∏ i, w (z i)) * (∏ e ∈ T, L (z e.1) (z e.2)) *
          featDensity w L Fa z * featDensity w L Fb z := by
  have hinjR : Set.InjOn (fun e : Fin r × Fin r => (rootV r k p e.1, rootV r k p e.2)) T :=
    fun e _ f _ h => by
      simp only [Prod.mk.injEq, rootV] at h
      exact Prod.ext (Fin.castAdd_injective _ _ h.1) (Fin.castAdd_injective _ _ h.2)
  have hinj1 : Set.InjOn (fun e : Fin (r + k) × Fin (r + k) => (emb1 r k p e.1, emb1 r k p e.2))
      Fa := fun e _ f _ h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (emb1_injective h.1) (emb1_injective h.2)
  have hinj2 : Set.InjOn (fun e : Fin (r + k) × Fin (r + k) => (emb2 r k p e.1, emb2 r k p e.2))
      Fb := fun e _ f _ h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (emb2_injective h.1) (emb2_injective h.2)
  have hq : ∑ q : Fin p → Fin d, ∏ j, w (q j) = 1 := by rw [sum_prod_weights, hw, one_pow]
  unfold edgeDensity rootedEdges
  rw [sum_assemble]
  refine sum_congr rfl fun z _ => ?_
  -- the edge product at an assembled map splits into the three parts
  have hprod : ∀ (y1 y2 : Fin k → Fin d) (q : Fin p → Fin d),
      ∏ e ∈ (T.image fun e => (rootV r k p e.1, rootV r k p e.2)) ∪
          (Fa.image fun e => (emb1 r k p e.1, emb1 r k p e.2)) ∪
          (Fb.image fun e => (emb2 r k p e.1, emb2 r k p e.2)),
        L (assemble z y1 y2 q e.1) (assemble z y1 y2 q e.2)
      = (∏ e ∈ T, L (z e.1) (z e.2)) *
          (∏ e ∈ Fa, L (Fin.append z y1 e.1) (Fin.append z y1 e.2)) *
          ∏ e ∈ Fb, L (Fin.append z y2 e.1) (Fin.append z y2 e.2) := by
    intro y1 y2 q
    rw [prod_union (rootedEdges_disjoint₂ T Fa hFb), prod_union (rootedEdges_disjoint₁ T hFa),
      prod_image hinjR, prod_image hinj1, prod_image hinj2]
    simp only [assemble_rootV, assemble_emb1, assemble_emb2]
  simp only [hprod, prod_weights_assemble, featDensity, mul_sum, sum_mul]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun y1 _ => sum_congr rfl fun y2 _ => ?_
  have hsplit : ∀ a b : ℝ, ∑ q : Fin p → Fin d, a * (∏ j, w (q j)) * b = a * b := fun a b => by
    rw [← sum_mul, ← mul_sum, hq, mul_one]
  rw [hsplit]
  ring

/-! ### Masks on the two-copy vertex set

For a shape with `r + (k + (k + p)) = 6`, a six-vertex mask is read on the two-copy vertex set
through `Fin.cast`.  A root mask, a feature in the first copy and (after the block swap `σ`) a
feature in the second copy are pull-backs along `rootV`, `emb1`, `emb2`. -/

section Masks

variable (h6 : r + (k + (k + p)) = 6)

/-- The edges of the mask `g` pulled back along `φ`. -/
def pull {m : ℕ} (φ : Fin m → Fin (r + (k + (k + p)))) (g : ℕ) : Finset (Fin m × Fin m) :=
  univ.filter fun e => (Fin.cast h6 (φ e.1), Fin.cast h6 (φ e.2)) ∈ maskEdges g

lemma image_pull {m : ℕ} (φ : Fin m → Fin (r + (k + (k + p)))) {g : ℕ}
    (hg : ∀ q ∈ maskEdges g, ∃ u v : Fin m, q = (Fin.cast h6 (φ u), Fin.cast h6 (φ v))) :
    (pull h6 φ g).image (fun e => (Fin.cast h6 (φ e.1), Fin.cast h6 (φ e.2))) = maskEdges g := by
  ext q
  simp only [mem_image, pull, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro hq
    obtain ⟨u, v, rfl⟩ := hg q hq
    exact ⟨(u, v), hq, rfl⟩

lemma roots_range {g : ℕ} (hg : ∀ q ∈ maskEdges g, (q.2 : ℕ) < r) :
    ∀ q ∈ maskEdges g, ∃ u v : Fin r,
      q = (Fin.cast h6 (rootV r k p u), Fin.cast h6 (rootV r k p v)) := by
  intro q hq
  have h2 := hg q hq
  have h1 : (q.1 : ℕ) < q.2 := maskEdges_sorted g q hq
  exact ⟨⟨q.1, by omega⟩, ⟨q.2, h2⟩, Prod.ext (Fin.ext (by simp [rootV]))
    (Fin.ext (by simp [rootV]))⟩

lemma emb1_range {g : ℕ} (hg : ∀ q ∈ maskEdges g, (q.2 : ℕ) < r + k) :
    ∀ q ∈ maskEdges g, ∃ u v : Fin (r + k),
      q = (Fin.cast h6 (emb1 r k p u), Fin.cast h6 (emb1 r k p v)) := by
  intro q hq
  have h2 := hg q hq
  have h1 : (q.1 : ℕ) < q.2 := maskEdges_sorted g q hq
  exact ⟨⟨q.1, by omega⟩, ⟨q.2, h2⟩, Prod.ext (Fin.ext (by simp [val_emb1]))
    (Fin.ext (by simp [val_emb1]))⟩

/-- The second copy of a feature is its relabelling by the block swap. -/
lemma maskEdges_relabel_emb2 {code : ℕ} (hc : isPerm code = true)
    (hσ : ∀ v : Fin (r + k), Fin.cast h6 (emb2 r k p v) = permOf hc (Fin.cast h6 (emb1 r k p v)))
    {g : ℕ} (hg : ∀ q ∈ maskEdges g, (q.2 : ℕ) < r + k) :
    maskEdges (relabel g code) = (pull h6 (emb1 r k p) g).image
      (fun e => (Fin.cast h6 (emb2 r k p e.1), Fin.cast h6 (emb2 r k p e.2))) := by
  rw [maskEdges_relabel g hc, ← image_pull h6 (emb1 r k p) (emb1_range h6 hg), image_image]
  refine image_congr fun e he => ?_
  have he' : (Fin.cast h6 (emb1 r k p e.1), Fin.cast h6 (emb1 r k p e.2)) ∈ maskEdges g := by
    simpa [pull] using he
  have hlt : ((Fin.cast h6 (emb1 r k p e.1) : Fin 6) : ℕ) < Fin.cast h6 (emb1 r k p e.2) :=
    maskEdges_sorted g _ he'
  simp only [Fin.val_cast, val_emb1] at hlt
  simp only [Function.comp_apply, ← hσ]
  apply sortPair_of_lt
  show ((Fin.cast h6 (emb2 r k p e.1) : Fin 6) : ℕ) < Fin.cast h6 (emb2 r k p e.2)
  simp only [Fin.val_cast, val_emb2]
  split_ifs <;> omega

/-- A mask's edges all lie below `bound` (checked bit by bit). -/
def maskBelow (g bound : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => (!g.testBit b || Nat.blt (edgeSnd b) bound) && maskBelow g bound b

/-- Every edge of a mask has its larger end at least `bound`. -/
def maskAbove (g bound : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => (!g.testBit b || Nat.ble bound (edgeSnd b)) && maskAbove g bound b

lemma maskBelow_sound {g bound : ℕ} (h : maskBelow g bound 15 = true) :
    ∀ q ∈ maskEdges g, (q.2 : ℕ) < bound := by
  have key : ∀ n, maskBelow g bound n = true → ∀ b : Fin 15, (b : ℕ) < n → g.testBit b = true →
      ((pairOf b).2 : ℕ) < bound := by
    intro n
    induction n with
    | zero => intro _ b hb; omega
    | succ n ih =>
      intro hn b hb hg
      simp only [maskBelow, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        Nat.blt_eq] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | heq
      · exact ih hn.2 b hlt hg
      · subst heq
        rcases hn.1 with h1 | h1
        · rw [hg] at h1; exact absurd h1 (by decide)
        · rwa [edgeSnd_eq] at h1
  intro q hq
  obtain ⟨b, hb, rfl⟩ := mem_maskEdges.mp hq
  exact key 15 h b b.isLt hb

lemma maskAbove_sound {g bound : ℕ} (h : maskAbove g bound 15 = true) :
    ∀ q ∈ maskEdges g, bound ≤ (q.2 : ℕ) := by
  have key : ∀ n, maskAbove g bound n = true → ∀ b : Fin 15, (b : ℕ) < n → g.testBit b = true →
      bound ≤ ((pairOf b).2 : ℕ) := by
    intro n
    induction n with
    | zero => intro _ b hb; omega
    | succ n ih =>
      intro hn b hb hg
      simp only [maskAbove, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        Nat.ble_eq] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | heq
      · exact ih hn.2 b hlt hg
      · subst heq
        rcases hn.1 with h1 | h1
        · rw [hg] at h1; exact absurd h1 (by decide)
        · rwa [edgeSnd_eq] at h1
  intro q hq
  obtain ⟨b, hb, rfl⟩ := mem_maskEdges.mp hq
  exact key 15 h b b.isLt hb

lemma noRootEdge_pull {g : ℕ} (hg : ∀ q ∈ maskEdges g, r ≤ (q.2 : ℕ)) :
    NoRootEdge r (pull h6 (emb1 r k p) g) := by
  intro e he
  have he' : (Fin.cast h6 (emb1 r k p e.1), Fin.cast h6 (emb1 r k p e.2)) ∈ maskEdges g := by
    simpa [pull] using he
  have := hg _ he'
  simp only [Fin.val_cast, val_emb1] at this
  exact Or.inr this

/-- **Skeleton evaluation.**  The mask `h ∪ F_a ∪ σ(F_b)` (root edges `h`, features `F_a, F_b` in
the first copy, `σ` the block swap) has the density `∑_z ∏ w(z) · ∏_{h} U · Φ_a(z) Φ_b(z)`. -/
theorem evalMask_skeleton (K : FiniteKernel d) {code : ℕ} (hc : isPerm code = true)
    (hσ : ∀ v : Fin (r + k), Fin.cast h6 (emb2 r k p v) = permOf hc (Fin.cast h6 (emb1 r k p v)))
    {h fa fb : ℕ} (hh : ∀ q ∈ maskEdges h, (q.2 : ℕ) < r)
    (hfa : ∀ q ∈ maskEdges fa, (q.2 : ℕ) < r + k) (hfa' : ∀ q ∈ maskEdges fa, r ≤ (q.2 : ℕ))
    (hfb : ∀ q ∈ maskEdges fb, (q.2 : ℕ) < r + k) (hfb' : ∀ q ∈ maskEdges fb, r ≤ (q.2 : ℕ)) :
    evalMask K (h ||| fa ||| relabel fb code)
      = ∑ z : Fin r → Fin d, (∏ i, K.w (z i)) *
          (∏ e ∈ pull h6 (rootV r k p) h, K.U (z e.1) (z e.2)) *
          featDensity K.w K.U (pull h6 (emb1 r k p) fa) z *
          featDensity K.w K.U (pull h6 (emb1 r k p) fb) z := by
  rw [← edgeDensity_rooted_split K.w K.w_sum K.U _ _ _ (noRootEdge_pull h6 hfa')
    (noRootEdge_pull h6 hfb')]
  have hE : maskEdges (h ||| fa ||| relabel fb code)
      = (rootedEdges r k p (pull h6 (rootV r k p) h) (pull h6 (emb1 r k p) fa)
          (pull h6 (emb1 r k p) fb)).map
          ((finCongr h6).toEmbedding.prodMap (finCongr h6).toEmbedding) := by
    rw [maskEdges_lor, maskEdges_lor, rootedEdges, map_union, map_union, map_eq_image,
      map_eq_image, map_eq_image, image_image, image_image, image_image,
      maskEdges_relabel_emb2 h6 hc hσ hfb]
    congr 2
    · rw [← image_pull h6 (rootV r k p) (roots_range h6 hh)]
      rfl
    · rw [← image_pull h6 (emb1 r k p) (emb1_range h6 hfa)]
      rfl
  rw [evalMask, hE, edgeDensity_map_equiv]

/-! ### The root-type factor -/

/-- `L` at a six-vertex pair whose ends are roots (and `1` otherwise). -/
def rootU (L : Fin d → Fin d → ℝ) (z : Fin r → Fin d) (q : Fin 6 × Fin 6) : ℝ :=
  if hq : (q.1 : ℕ) < r ∧ (q.2 : ℕ) < r then L (z ⟨q.1, hq.1⟩) (z ⟨q.2, hq.2⟩) else 1

lemma abs_rootU_le {L : Fin d → Fin d → ℝ} (hL : ∀ i j, |L i j| ≤ 1) (z : Fin r → Fin d)
    (q : Fin 6 × Fin 6) : |rootU L z q| ≤ 1 := by
  unfold rootU
  split_ifs
  · exact hL _ _
  · simp

/-- The root-edge product of a mask, bit by bit. -/
lemma rootProd_eq (L : Fin d → Fin d → ℝ) (z : Fin r → Fin d) {g : ℕ}
    (hg : ∀ q ∈ maskEdges g, (q.2 : ℕ) < r) :
    ∏ e ∈ pull h6 (rootV r k p) g, L (z e.1) (z e.2)
      = ∏ b ∈ univ.filter (fun b : Fin 15 => g.testBit b = true), rootU L z (pairOf b) := by
  have hinj : Set.InjOn (fun e : Fin r × Fin r =>
      (Fin.cast h6 (rootV r k p e.1), Fin.cast h6 (rootV r k p e.2))) (pull h6 (rootV r k p) g) :=
    fun e _ f _ hef => by
      simp only [Prod.mk.injEq, Fin.cast_inj, rootV] at hef
      exact Prod.ext (Fin.castAdd_injective _ _ hef.1) (Fin.castAdd_injective _ _ hef.2)
  rw [← prod_image (f := rootU L z) (fun b _ b' _ h => pairOf_injective h), ← maskEdges,
    ← image_pull h6 (rootV r k p) (roots_range h6 hg), prod_image hinj]
  refine prod_congr rfl fun e _ => ?_
  have h1 : ((Fin.cast h6 (rootV r k p e.1) : Fin 6) : ℕ) = e.1 := by simp [rootV]
  have h2 : ((Fin.cast h6 (rootV r k p e.2) : Fin 6) : ℕ) = e.2 := by simp [rootV]
  unfold rootU
  rw [dif_pos ⟨h1 ▸ e.1.isLt, h2 ▸ e.2.isLt⟩]
  congr 2

end Masks

/-- The submasks of `R` among its bits below `n`, ordered by the bits in increasing position. -/
def subMasks (R : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => if R.testBit n then subMasks R n ++ (subMasks R n).map (fun h => h ||| 2 ^ n)
      else subMasks R n

lemma subMasks_spec (R : ℕ) : ∀ n, ∀ h ∈ subMasks R n,
    h < 2 ^ n ∧ ∀ b, h.testBit b = true → R.testBit b = true
  | 0 => by simp [subMasks]
  | n + 1 => by
    intro h hh
    have ih := subMasks_spec R n
    unfold subMasks at hh
    split_ifs at hh with hR
    · rcases List.mem_append.mp hh with hh | hh
      · obtain ⟨hlt, hb⟩ := ih h hh
        exact ⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)), hb⟩
      · obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
        obtain ⟨hlt, hb⟩ := ih h' hh'
        refine ⟨?_, fun b hb' => ?_⟩
        · have h2 := Nat.two_pow_add_eq_or_of_lt hlt 1
          rw [mul_one] at h2
          have : h' ||| 2 ^ n = h' + 2 ^ n := by
            rw [Nat.lor_comm, ← h2, add_comm]
          rw [this, pow_succ]
          omega
        · rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hb'
          rcases hb' with hb' | hb'
          · exact hb b hb'
          · have : n = b := by simpa using hb'
            exact this ▸ hR
    · obtain ⟨hlt, hb⟩ := ih h hh
      exact ⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)), hb⟩

/-- Bits below `n + 1` of a number below `2^n` are its bits below `n`. -/
lemma filter_succ_low {h n : ℕ} (hh : h < 2 ^ n) :
    univ.filter (fun b : Fin 15 => (b : ℕ) < n + 1 ∧ h.testBit b = true)
      = univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true) := by
  ext b
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hb, hbit⟩
    refine ⟨?_, hbit⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | hb
    · exact hb
    · rw [hb, Nat.testBit_eq_false_of_lt hh] at hbit
      exact absurd hbit (by decide)
  · rintro ⟨hb, hbit⟩
    exact ⟨by omega, hbit⟩

/-- Bits below `n + 1` when bit `n` is set. -/
lemma filter_succ_set {h n : ℕ} (hn : n < 15) (hbit : h.testBit n = true) :
    univ.filter (fun b : Fin 15 => (b : ℕ) < n + 1 ∧ h.testBit b = true)
      = insert ⟨n, hn⟩ (univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true)) := by
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨hb, hb'⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | hb
    · exact Or.inr ⟨hb, hb'⟩
    · exact Or.inl (Fin.ext hb)
  · rintro (rfl | ⟨hb, hb'⟩)
    · exact ⟨by simp, hbit⟩
    · exact ⟨by omega, hb'⟩

/-- Bits below `n + 1` when bit `n` is clear. -/
lemma filter_succ_clear {h n : ℕ} (hbit : h.testBit n = false) :
    univ.filter (fun b : Fin 15 => (b : ℕ) < n + 1 ∧ h.testBit b = true)
      = univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true) := by
  ext b
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hb, hb'⟩
    refine ⟨?_, hb'⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | hb
    · exact hb
    · subst hb
      rw [hbit] at hb'
      exact absurd hb' (by decide)
  · rintro ⟨hb, hb'⟩
    exact ⟨by omega, hb'⟩

lemma not_mem_filter_self {h n : ℕ} (hn : n < 15) :
    (⟨n, hn⟩ : Fin 15) ∉ univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true) := by
  simp

/-- Expansion of `∏ (1 + f b)` over the bits of `R` as a sum over its submasks. -/
lemma prod_one_add_subMasks (R : ℕ) (f : Fin 15 → ℝ) : ∀ n ≤ 15,
    ∏ b ∈ univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ R.testBit b = true), (1 + f b)
      = ((subMasks R n).map fun h =>
          ∏ b ∈ univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true), f b).sum
  | 0, _ => by simp [subMasks]
  | n + 1, hn => by
    have ih := prod_one_add_subMasks R f n (by omega)
    have hn' : n < 15 := by omega
    have hspec := subMasks_spec R n
    unfold subMasks
    split_ifs with hR
    · rw [filter_succ_set hn' hR, prod_insert (not_mem_filter_self (h := R) hn'), ih, List.map_append,
        List.sum_append, List.map_map]
      have e1 : ((subMasks R n).map fun h =>
            ∏ b ∈ univ.filter (fun b : Fin 15 => (b : ℕ) < n + 1 ∧ h.testBit b = true), f b)
          = (subMasks R n).map fun h =>
            ∏ b ∈ univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true), f b :=
        List.map_congr_left fun h hh => by rw [filter_succ_low (hspec h hh).1]
      have e2 : ((subMasks R n).map ((fun h =>
            ∏ b ∈ univ.filter (fun b : Fin 15 => (b : ℕ) < n + 1 ∧ h.testBit b = true), f b) ∘
            fun h => h ||| 2 ^ n))
          = (subMasks R n).map fun h => f ⟨n, hn'⟩ *
            ∏ b ∈ univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true), f b :=
        List.map_congr_left fun h hh => by
          have hlt := (hspec h hh).1
          have hset : (h ||| 2 ^ n).testBit n = true := by simp [Nat.testBit_or]
          have hlow : univ.filter
                (fun b : Fin 15 => (b : ℕ) < n ∧ (h ||| 2 ^ n).testBit b = true)
              = univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true) := by
            ext b
            simp only [mem_filter, mem_univ, true_and, Nat.testBit_or, Nat.testBit_two_pow,
              Bool.or_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨hb, hb' | hb'⟩
              · exact ⟨hb, hb'⟩
              · omega
            · rintro ⟨hb, hb'⟩
              exact ⟨hb, Or.inl hb'⟩
          simp only [Function.comp_apply]
          rw [filter_succ_set hn' hset, prod_insert (not_mem_filter_self (h := h ||| 2 ^ n) hn'), hlow]
      rw [e1, e2, List.sum_map_mul_left]
      ring
    · have hR' : R.testBit n = false := by simpa using hR
      rw [filter_succ_clear hR', ih]
      exact congrArg List.sum (List.map_congr_left fun h hh => by
        rw [filter_succ_low (hspec h hh).1])

/-- The sign `(−1)^{|h ∖ t|}`, as a parity bit. -/
def sgnGo (t h : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => xor (sgnGo t h n) (h.testBit n && !t.testBit n)

/-- The sign `(−1)^{|h ∖ t|}` as a real number. -/
def sgnR (t h : ℕ) : ℝ := if sgnGo t h 15 then -1 else 1

lemma sgnGo_eq (t h : ℕ) : ∀ n ≤ 15, (if sgnGo t h n then (-1 : ℝ) else 1)
    = ∏ b ∈ univ.filter (fun b : Fin 15 => (b : ℕ) < n ∧ h.testBit b = true),
        (if t.testBit b then (1 : ℝ) else -1)
  | 0, _ => by simp [sgnGo]
  | n + 1, hn => by
    have ih := sgnGo_eq t h n (by omega)
    have hn' : n < 15 := by omega
    cases hh : h.testBit n
    · rw [filter_succ_clear hh, ← ih, sgnGo, hh]
      simp
    · rw [filter_succ_set hn' hh, prod_insert (not_mem_filter_self (h := h) hn'), ← ih, sgnGo, hh]
      show _ = (if t.testBit n then (1 : ℝ) else -1) * _
      cases sgnGo t h n <;> cases t.testBit n <;> simp

/-! ### Positivity of one block (`lem:rooted-positivity` with `lem:rooted-expansion`) -/

lemma list_sum_finset_sum {α β : Type*} (l : List α) (s : Finset β) (f : α → β → ℝ) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, sum_add_distrib]

/-- The root-type factor `∏_{e ∈ R} (1 ± U_e)`, `+` exactly on the edges of `t`. -/
def typeFactor (L : Fin d → Fin d → ℝ) (z : Fin r → Fin d) (R t : ℕ) : ℝ :=
  ∏ b ∈ univ.filter (fun b : Fin 15 => R.testBit b = true),
    (1 + (if t.testBit b then (1 : ℝ) else -1) * rootU L z (pairOf b))

lemma typeFactor_nonneg {L : Fin d → Fin d → ℝ} (hL : ∀ i j, |L i j| ≤ 1) (z : Fin r → Fin d)
    (R t : ℕ) : 0 ≤ typeFactor L z R t :=
  prod_nonneg fun b _ => by
    have := abs_le.mp (abs_rootU_le hL z (pairOf b))
    split_ifs <;> linarith [this.1, this.2]

lemma filter_fifteen (g : ℕ) :
    univ.filter (fun b : Fin 15 => (b : ℕ) < 15 ∧ g.testBit b = true)
      = univ.filter (fun b : Fin 15 => g.testBit b = true) := by
  ext b
  simp

/-- The edges of a submask of a root mask are root pairs. -/
lemma subMasks_roots {R : ℕ} (hR : ∀ q ∈ maskEdges R, (q.2 : ℕ) < r) {h : ℕ}
    (hh : h ∈ subMasks R 15) : ∀ q ∈ maskEdges h, (q.2 : ℕ) < r := by
  intro q hq
  obtain ⟨b, hb, rfl⟩ := mem_maskEdges.mp hq
  exact hR _ (mem_maskEdges.mpr ⟨b, (subMasks_spec R 15 h hh).2 b hb, rfl⟩)

/-- **Expansion of the type factor** over the submasks of the root mask. -/
lemma typeFactor_expand (h6 : r + (k + (k + p)) = 6) (L : Fin d → Fin d → ℝ)
    (z : Fin r → Fin d) {R : ℕ} (hR : ∀ q ∈ maskEdges R, (q.2 : ℕ) < r) (t : ℕ) :
    ((subMasks R 15).map fun h =>
        sgnR t h * ∏ e ∈ pull h6 (rootV r k p) h, L (z e.1) (z e.2)).sum
      = typeFactor L z R t := by
  rw [typeFactor, ← filter_fifteen, prod_one_add_subMasks R _ 15 le_rfl]
  refine congrArg List.sum (List.map_congr_left fun h hh => ?_)
  rw [rootProd_eq h6 L z (subMasks_roots hR hh), sgnR, sgnGo_eq t h 15 le_rfl, filter_fifteen,
    ← prod_mul_distrib]

/-- **Positivity of one block.**  If `A` is positive semidefinite on the features `F_a` (edges
between roots `< r` and new vertices `< r + k`, no root–root edge), then
`∑_{a,b} A_ab ∑_{h ⊆ R} (−1)^{|h ∖ t|} t(h ∪ F_a ∪ σF_b) ≥ 0` — it is
`∑_z ∏ w · ∏_{e ∈ R} (1 ± U_e) · Φᵀ A Φ`. -/
theorem block_nonneg (h6 : r + (k + (k + p)) = 6) (K : FiniteKernel d) {code : ℕ}
    (hc : isPerm code = true)
    (hσ : ∀ v : Fin (r + k), Fin.cast h6 (emb2 r k p v) = permOf hc (Fin.cast h6 (emb1 r k p v)))
    {R : ℕ} (hR : ∀ q ∈ maskEdges R, (q.2 : ℕ) < r) (t : ℕ) {n : ℕ} (fa : ℕ → ℕ)
    (hfa : ∀ a < n, ∀ q ∈ maskEdges (fa a), (q.2 : ℕ) < r + k)
    (hfa' : ∀ a < n, ∀ q ∈ maskEdges (fa a), r ≤ (q.2 : ℕ))
    (A : ℕ → ℕ → ℝ) (hA : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ range n, ∑ b ∈ range n, x a * A a b * x b) :
    0 ≤ ∑ a ∈ range n, ∑ b ∈ range n, A a b *
      ((subMasks R 15).map fun h => sgnR t h * evalMask K (h ||| fa a ||| relabel (fa b) code)).sum := by
  set Φ : ℕ → (Fin r → Fin d) → ℝ := fun a z => featDensity K.w K.U (pull h6 (emb1 r k p) (fa a)) z
  have key : ∀ a < n, ∀ b < n,
      ((subMasks R 15).map fun h => sgnR t h * evalMask K (h ||| fa a ||| relabel (fa b) code)).sum
        = ∑ z : Fin r → Fin d, (∏ i, K.w (z i)) * typeFactor K.U z R t * Φ a z * Φ b z := by
    intro a ha b hb
    rw [List.map_congr_left fun h hh => by
      rw [evalMask_skeleton h6 K hc hσ (subMasks_roots hR hh) (hfa a ha) (hfa' a ha) (hfa b hb)
        (hfa' b hb), mul_sum]]
    rw [list_sum_finset_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [← typeFactor_expand h6 K.U z hR t]
    have hl : ∀ l : List ℕ, (l.map fun h => sgnR t h * ((∏ i, K.w (z i)) *
          (∏ e ∈ pull h6 (rootV r k p) h, K.U (z e.1) (z e.2)) * Φ a z * Φ b z)).sum
        = (∏ i, K.w (z i)) * (l.map fun h =>
          sgnR t h * ∏ e ∈ pull h6 (rootV r k p) h, K.U (z e.1) (z e.2)).sum * Φ a z * Φ b z := by
      intro l
      induction l with
      | nil => simp
      | cons h l ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring
    exact hl _
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => by
    rw [key a (mem_range.mp ha) b (mem_range.mp hb), mul_sum]]
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  refine sum_nonneg fun z _ => ?_
  have hw : 0 ≤ ∏ i, K.w (z i) := prod_nonneg fun i _ => K.w_nonneg _
  have hT := typeFactor_nonneg K.U_abs_le z R t
  have hQ := hA fun a => Φ a z
  have : ∑ a ∈ range n, ∑ b ∈ range n,
      A a b * ((∏ i, K.w (z i)) * typeFactor K.U z R t * Φ a z * Φ b z)
      = (∏ i, K.w (z i)) * typeFactor K.U z R t *
        ∑ a ∈ range n, ∑ b ∈ range n, Φ a z * A a b * Φ b z := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  rw [this]
  exact mul_nonneg (mul_nonneg hw hT) hQ

end EvenCycleApex
