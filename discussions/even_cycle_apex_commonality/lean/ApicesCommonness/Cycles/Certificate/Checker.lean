import ApicesCommonness.Cycles.Certificate.Rooted
import ApicesCommonness.Cycles.Certificate.Accum
import ApicesCommonness.Cycles.Certificate.LDL

/-!
# The certificate checker and its soundness

Blueprint `prop:checked-data` and `thm:certificate-inequalities`, in the encoding of DEVIATIONS X3.

A certificate for a target polynomial `P` (a list of `(coefficient, mask)` monomials) consists of

* groups of blocks with the same number of roots (`GroupCert`): the shape and features (`Schema`),
  one relabelling witness per skeleton `h ∪ F_a ∪ σF_b` (`W a b` lists the witnesses for the
  submasks `h` of the root mask, in the order of `subMasks`), the integer matrices of all blocks
  of the group merged entrywise (`M a b` lists `A⁽ʲ⁾_ab` over the blocks `j`), and one `LDLᵀ`
  witness per block;
* one relabelling witness per monomial of `P`;
* an orbit-representative function `rep` (any function: soundness never uses what the
  representatives are).

A witness `w` packs an orbit id and a permutation code, `w = o + 256 · code`; it is valid for the
mask `g` when `code` is a permutation and `relabel g code = rep o` (`witOK`).

The coefficient of the skeleton `(a, b, h)` is `∑ⱼ (−1)^{|h ∖ tⱼ|} A⁽ʲ⁾_ab` (`coefT`); the group's
items `(orbit, coefficient)` are accumulated by `accRows` (packed, forced; `accRows_eq`).

`cert_sound`: if the schema, witnesses and factorizations check, and the packed values of
`scale · P` and of `∑_g weight_g · (group g)` agree with total mass `< 2^128`, then
`0 ≤ eval_U(P)` on every finite host.
-/

open Finset

namespace ApicesCommonness

variable {d : ℕ}

/-! ### Witnesses -/

/-- The orbit id of a witness. -/
def witOrb (w : ℕ) : ℕ := Nat.land w 255

/-- The permutation code of a witness. -/
def witCode (w : ℕ) : ℕ := Nat.shiftRight w 8

/-- The witness `w` maps the mask `g` to the representative of its orbit. -/
def witOK (rep : ℕ → ℕ) (g w : ℕ) : Bool :=
  isPerm (witCode w) && Nat.beq (relabel g (witCode w)) (rep (witOrb w))

lemma evalMask_of_witOK (K : FiniteKernel d) {rep : ℕ → ℕ} {g w : ℕ} (h : witOK rep g w = true) :
    evalMask K g = evalMask K (rep (witOrb w)) := by
  simp only [witOK, Bool.and_eq_true] at h
  rw [← Nat.eq_of_beq_eq_true h.2, evalMask_relabel K g h.1]

/-! ### Schemas -/

/-- The shape and the features of a group of blocks with `r` roots. -/
structure Schema where
  /-- number of roots -/
  r : ℕ
  /-- number of new vertices of a feature -/
  k : ℕ
  /-- padding, `r + 2k + p = 6` -/
  p : ℕ
  /-- permutation code of the block swap (second copy) -/
  sigma : ℕ
  /-- the root pairs, as a six-vertex mask -/
  rootMask : ℕ
  /-- the features, as six-vertex masks on the roots and the first copy -/
  feats : List ℕ
  /-- the root types of the blocks, as six-vertex masks -/
  types : List ℕ
  /-- the weight `2^{6 − C(r,2)}` of the group in identity (C) -/
  weight : ℕ

/-- The block swap fixes the roots and shifts the first copy onto the second. -/
def swapOK (r k code : ℕ) : Bool :=
  (List.range (r + k)).all fun v => Nat.beq (permAt code v) (if v < r then v else v + k)

/-- The schema checks. -/
def Schema.ok (S : Schema) : Bool :=
  Nat.beq (S.r + (S.k + (S.k + S.p))) 6 && isPerm S.sigma && swapOK S.r S.k S.sigma &&
    maskBelow S.rootMask S.r 15 &&
    S.feats.all fun f => maskBelow f (S.r + S.k) 15 && maskAbove f S.r 15

/-- The submasks of the root mask, in witness order. -/
def Schema.roots (S : Schema) : List ℕ := subMasks S.rootMask 15

/-- The second-copy features. -/
def Schema.feats2 (S : Schema) : List ℕ := S.feats.map fun f => relabel f S.sigma

/-- The signs `(−1)^{|h ∖ tⱼ|}` of the blocks, for every submask `h` (`true` = negative). -/
def Schema.signs (S : Schema) : List (List Bool) :=
  S.roots.map fun h => S.types.map fun t => sgnGo t h 15

/-! ### Group certificates -/

/-- The certificate data of one group. -/
structure GroupCert where
  /-- shape and features -/
  S : Schema
  /-- `W a b`: the witnesses of the skeletons `(a, b, h)`, `h` in `S.roots` order -/
  W : List (List (List ℕ))
  /-- `M a b`: the entries `A⁽ʲ⁾_ab` over the blocks `j` -/
  M : List (List (List ℤ))
  /-- `LDLᵀ` witness (strictly lower rows, diagonal) per block -/
  ldl : List (List (List (ℤ × ℕ)) × List (ℤ × ℕ))

/-- Entry `(a, b)` of a doubly nested list. -/
def entry {α : Type*} (X : List (List (List α))) (a b : ℕ) : List α := (X.getD a []).getD b []

/-- The matrix of block `j`, as a list of rows. -/
def GroupCert.block (G : GroupCert) (j : ℕ) : List (List ℤ) :=
  (List.range G.S.feats.length).map fun a =>
    (List.range G.S.feats.length).map fun b => (entry G.M a b).getD j 0

/-- The witness check of row `a`. -/
def GroupCert.witRow (rep : ℕ → ℕ) (G : GroupCert) (a : ℕ) : Bool :=
  all2 (fun fb wab => all2 (fun h w => witOK rep (Nat.lor (Nat.lor h (G.S.feats.getD a 0)) fb) w)
    G.S.roots wab) G.S.feats2 (G.W.getD a [])

/-- The factorization check of block `j`. -/
def GroupCert.ldlOK (G : GroupCert) (j : ℕ) : Bool :=
  factorOK (G.block j) (G.ldl.getD j ([], [])).1 (G.ldl.getD j ([], [])).2

/-- Everything checked about a group. -/
def GroupCert.valid (rep : ℕ → ℕ) (G : GroupCert) : Prop :=
  G.S.ok = true ∧ (∀ a < G.S.feats.length, G.witRow rep a = true) ∧
    ∀ j < G.S.types.length, G.ldlOK j = true

/-! ### Accumulation -/

/-- The merged coefficient `∑ⱼ ±eⱼ` of one skeleton (`true` = negative). -/
def coefT : List ℤ → List Bool → ℤ
  | a :: as, s :: ss => (if s then -a else a) + coefT as ss
  | _, _ => 0

/-- Items of one entry `(a, b)`: an orbit id and a coefficient per submask. -/
def itemsT (e : List ℤ) (ws : List ℕ) (sgs : List (List Bool)) : List (ℕ × ℤ) :=
  (ws.zip sgs).map fun x => (witOrb x.1, coefT e x.2)

/-- Items of the entries `(a, b), …, (a, b + fuel − 1)`. -/
def GroupCert.itemsCols (G : GroupCert) (a : ℕ) : ℕ → ℕ → List (ℕ × ℤ)
  | _, 0 => []
  | b, fuel + 1 => itemsT (entry G.M a b) (entry G.W a b) G.S.signs ++ G.itemsCols a (b + 1) fuel

/-- Items of the rows `a, …, a + fuel − 1`. -/
def GroupCert.itemsRows (G : GroupCert) : ℕ → ℕ → List (ℕ × ℤ)
  | _, 0 => []
  | a, fuel + 1 => G.itemsCols a 0 G.S.feats.length ++ G.itemsRows (a + 1) fuel

/-- All items of a group. -/
def GroupCert.items (G : GroupCert) : List (ℕ × ℤ) := G.itemsRows 0 G.S.feats.length

/-- Kernel loop over one entry. -/
def accT (e : List ℤ) : List ℕ → List (List Bool) → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → Bool) → Bool
  | w :: ws, sg :: sgs, p, q, m, k =>
      accStep p q m (witOrb w) (coefT e sg) fun p q m => accT e ws sgs p q m k
  | _, _, p, q, m, k => k p q m

/-- Kernel loop over the entries of a row. -/
def GroupCert.accCols (G : GroupCert) (a : ℕ) :
    ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → Bool) → Bool
  | _, 0, p, q, m, k => k p q m
  | b, fuel + 1, p, q, m, k =>
      accT (entry G.M a b) (entry G.W a b) G.S.signs p q m fun p q m =>
        G.accCols a (b + 1) fuel p q m k

/-- Kernel loop over rows. -/
def GroupCert.accRows (G : GroupCert) : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → Bool) → Bool
  | _, 0, p, q, m, k => k p q m
  | a, fuel + 1, p, q, m, k =>
      G.accCols a 0 G.S.feats.length p q m fun p q m => G.accRows (a + 1) fuel p q m k

lemma accT_eq (e : List ℤ) : ∀ (ws : List ℕ) (sgs : List (List Bool)) (p q m : ℕ)
    (k : ℕ → ℕ → ℕ → Bool), accT e ws sgs p q m k = accList (itemsT e ws sgs) p q m k
  | w :: ws, sg :: sgs, p, q, m, k => by
    rw [accT, itemsT, List.zip_cons_cons, List.map_cons, accList]
    exact congrArg _ (funext fun p => funext fun q => funext fun m => accT_eq e ws sgs p q m k)
  | [], _, p, q, m, k => by simp [accT, itemsT, accList]
  | _ :: _, [], p, q, m, k => by simp [accT, itemsT, accList]

lemma GroupCert.accCols_eq (G : GroupCert) (a : ℕ) : ∀ (fuel b p q m : ℕ)
    (k : ℕ → ℕ → ℕ → Bool), G.accCols a b fuel p q m k = accList (G.itemsCols a b fuel) p q m k
  | 0, b, p, q, m, k => by simp [accCols, itemsCols, accList]
  | fuel + 1, b, p, q, m, k => by
    rw [accCols, itemsCols, accList_append, accT_eq]
    exact congrArg _ (funext fun p => funext fun q => funext fun m => G.accCols_eq a fuel _ p q m k)

lemma GroupCert.accRows_eq (G : GroupCert) : ∀ (fuel a p q m : ℕ)
    (k : ℕ → ℕ → ℕ → Bool), G.accRows a fuel p q m k = accList (G.itemsRows a fuel) p q m k
  | 0, a, p, q, m, k => by simp [accRows, itemsRows, accList]
  | fuel + 1, a, p, q, m, k => by
    rw [accRows, itemsRows, accList_append, G.accCols_eq]
    exact congrArg _ (funext fun p => funext fun q => funext fun m => G.accRows_eq fuel _ p q m k)

lemma GroupCert.itemsRows_add (G : GroupCert) : ∀ (f₁ f₂ a : ℕ),
    G.itemsRows a (f₁ + f₂) = G.itemsRows a f₁ ++ G.itemsRows (a + f₁) f₂
  | 0, f₂, a => by simp [itemsRows]
  | f₁ + 1, f₂, a => by
    rw [show f₁ + 1 + f₂ = (f₁ + f₂) + 1 by ring, itemsRows, itemsRows,
      G.itemsRows_add f₁ f₂ (a + 1), List.append_assoc, show a + 1 + f₁ = a + (f₁ + 1) by ring]

/-! ### Semantics of the items -/

/-- Weighted sum of items, with the orbit representatives evaluated on the host. -/
def itemSum (K : FiniteKernel d) (rep : ℕ → ℕ) (l : List (ℕ × ℤ)) : ℝ :=
  (l.map fun x => (x.2 : ℝ) * evalMask K (rep x.1)).sum

lemma itemSum_append (K : FiniteKernel d) (rep : ℕ → ℕ) (l₁ l₂ : List (ℕ × ℤ)) :
    itemSum K rep (l₁ ++ l₂) = itemSum K rep l₁ + itemSum K rep l₂ := by
  simp [itemSum]

lemma itemSum_scaleItems (K : FiniteKernel d) (rep : ℕ → ℕ) (s : ℕ) (l : List (ℕ × ℤ)) :
    itemSum K rep (scaleItems s l) = s * itemSum K rep l :=
  sum_scaleItems s l fun o => evalMask K (rep o)

lemma sum_zip_getD {α β : Type*} (d₁ : α) (d₂ : β) (f : α × β → ℝ) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      ((l₁.zip l₂).map f).sum = ∑ i ∈ range l₁.length, f (l₁.getD i d₁, l₂.getD i d₂)
  | [], [], _ => by simp
  | a :: as, b :: bs, h => by
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons,
      sum_zip_getD d₁ d₂ f as bs (by simpa using h), List.length_cons, sum_range_succ']
    simp [add_comm]

lemma sum_map_getD {α : Type*} (dflt : α) (f : α → ℝ) :
    ∀ l : List α, (l.map f).sum = ∑ i ∈ range l.length, f (l.getD i dflt)
  | [] => by simp
  | a :: as => by
    rw [List.map_cons, List.sum_cons, sum_map_getD dflt f as, List.length_cons, sum_range_succ']
    simp [add_comm]

lemma getD_map_of_lt {α β : Type*} (g : α → β) (l : List α) (dα : α) (dβ : β) {i : ℕ}
    (hi : i < l.length) : (l.map g).getD i dβ = g (l.getD i dα) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma coefT_cast (h : ℕ) : ∀ (types : List ℕ) (e : List ℤ),
    (coefT e (types.map fun t => sgnGo t h 15) : ℝ)
      = ∑ j ∈ range types.length, sgnR (types.getD j 0) h * ((e.getD j 0 : ℤ) : ℝ)
  | [], e => by cases e <;> simp [coefT]
  | t :: ts, [] => by simp [coefT]
  | t :: ts, a :: as => by
    rw [List.map_cons, coefT, Int.cast_add, coefT_cast h ts as, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, sgnR]
    rw [add_comm]
    congr 1
    split_ifs <;> simp

/-- **The items of one entry** are the signed skeleton densities. -/
lemma itemSum_itemsT (K : FiniteKernel d) {rep : ℕ → ℕ} {G : GroupCert} {a b : ℕ}
    (hTL : G.S.roots.length = (entry G.W a b).length)
    (hwit : ∀ i < G.S.roots.length, witOK rep
      (Nat.lor (Nat.lor (G.S.roots.getD i 0) (G.S.feats.getD a 0)) (G.S.feats2.getD b 0))
      ((entry G.W a b).getD i 0) = true) :
    itemSum K rep (itemsT (entry G.M a b) (entry G.W a b) G.S.signs)
      = (G.S.roots.map fun h => (∑ j ∈ range G.S.types.length,
          sgnR (G.S.types.getD j 0) h * (((entry G.M a b).getD j 0 : ℤ) : ℝ)) *
          evalMask K (h ||| G.S.feats.getD a 0 ||| G.S.feats2.getD b 0)).sum := by
  have hsg : G.S.signs.length = G.S.roots.length := by simp [Schema.signs]
  rw [itemSum, itemsT, List.map_map, sum_zip_getD 0 [] _ _ _ (by rw [← hTL, hsg]), ← hTL,
    sum_map_getD 0]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  simp only [Function.comp_apply]
  rw [Schema.signs, getD_map_of_lt _ _ 0 [] hi', coefT_cast,
    ← evalMask_of_witOK K (hwit i hi')]
  rfl

lemma sum_itemsCols (K : FiniteKernel d) (rep : ℕ → ℕ) (G : GroupCert) (a : ℕ) :
    ∀ fuel b, itemSum K rep (G.itemsCols a b fuel)
      = ∑ i ∈ range fuel, itemSum K rep (itemsT (entry G.M a (b + i)) (entry G.W a (b + i)) G.S.signs)
  | 0, b => by simp [GroupCert.itemsCols, itemSum]
  | fuel + 1, b => by
    rw [GroupCert.itemsCols, itemSum_append, sum_itemsCols K rep G a fuel (b + 1), sum_range_succ']
    simp only [add_zero]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun i _ => by rw [show b + 1 + i = b + (i + 1) by ring]

lemma sum_itemsRows (K : FiniteKernel d) (rep : ℕ → ℕ) (G : GroupCert) :
    ∀ fuel a, itemSum K rep (G.itemsRows a fuel)
      = ∑ i ∈ range fuel, itemSum K rep (G.itemsCols (a + i) 0 G.S.feats.length)
  | 0, a => by simp [GroupCert.itemsRows, itemSum]
  | fuel + 1, a => by
    rw [GroupCert.itemsRows, itemSum_append, sum_itemsRows K rep G fuel (a + 1), sum_range_succ']
    simp only [add_zero]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun i _ => by rw [show a + 1 + i = a + (i + 1) by ring]

/-- **A valid group contributes a nonnegative amount.** -/
theorem GroupCert.itemSum_nonneg (K : FiniteKernel d) {rep : ℕ → ℕ} {G : GroupCert}
    (hG : G.valid rep) : 0 ≤ itemSum K rep G.items := by
  obtain ⟨hS, hW, hL⟩ := hG
  set S := G.S with hSdef
  set n := S.feats.length with hn
  -- the schema facts
  simp only [Schema.ok, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hS
  obtain ⟨⟨⟨⟨h6, hc⟩, hswap⟩, hR⟩, hfeats⟩ := hS
  have hσ : ∀ v : Fin (S.r + S.k), Fin.cast h6 (emb2 S.r S.k S.p v)
      = permOf hc (Fin.cast h6 (emb1 S.r S.k S.p v)) := by
    intro v
    simp only [swapOK, List.all_eq_true, List.mem_range, Nat.beq_eq] at hswap
    refine Fin.ext ?_
    rw [Fin.val_cast, val_emb2, permOf_apply, Fin.val_cast, val_emb1, hswap v v.isLt]
  have hRb := maskBelow_sound hR
  have hfa : ∀ a < n, ∀ q ∈ maskEdges (S.feats.getD a 0), (q.2 : ℕ) < S.r + S.k := by
    intro a ha
    have hmem : S.feats.getD a 0 ∈ S.feats := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
      exact List.getElem_mem ha
    exact maskBelow_sound (hfeats _ hmem).1
  have hfa' : ∀ a < n, ∀ q ∈ maskEdges (S.feats.getD a 0), S.r ≤ (q.2 : ℕ) := by
    intro a ha
    have hmem : S.feats.getD a 0 ∈ S.feats := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
      exact List.getElem_mem ha
    exact maskAbove_sound (hfeats _ hmem).2
  -- the sum as a double sum over entries
  have hentry : ∀ a < n, ∀ b < n, itemSum K rep (itemsT (entry G.M a b) (entry G.W a b) S.signs)
      = ∑ j ∈ range S.types.length, (((entry G.M a b).getD j 0 : ℤ) : ℝ) *
          (S.roots.map fun h => sgnR (S.types.getD j 0) h *
            evalMask K (h ||| S.feats.getD a 0 ||| relabel (S.feats.getD b 0) S.sigma)).sum := by
    intro a ha b hb
    obtain ⟨hlenFB, hrow⟩ := all2_sound 0 [] (hW a ha)
    have hbFB : b < S.feats2.length := by simp [Schema.feats2]; omega
    obtain ⟨hTL, hwit⟩ := all2_sound 0 0 (hrow b hbFB)
    have hWab : (G.W.getD a []).getD b [] = entry G.W a b := rfl
    rw [hWab] at hTL hwit
    rw [itemSum_itemsT K hTL hwit]
    have hFB : S.feats2.getD b 0 = relabel (S.feats.getD b 0) S.sigma :=
      getD_map_of_lt _ _ 0 0 hb
    rw [hFB]
    simp only [sum_mul]
    rw [list_sum_finset_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun h _ => by ring
  have hsum : itemSum K rep G.items = ∑ j ∈ range S.types.length,
      ∑ a ∈ range n, ∑ b ∈ range n, (((entry G.M a b).getD j 0 : ℤ) : ℝ) *
        (S.roots.map fun h => sgnR (S.types.getD j 0) h *
          evalMask K (h ||| S.feats.getD a 0 ||| relabel (S.feats.getD b 0) S.sigma)).sum := by
    rw [GroupCert.items, sum_itemsRows]
    simp only [zero_add]
    rw [sum_congr rfl fun a ha => by rw [sum_itemsCols]]
    simp only [zero_add]
    rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => hentry a (mem_range.mp ha) b
      (mem_range.mp hb)]
    rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  rw [hsum]
  refine sum_nonneg fun j hj => ?_
  have hblock := factorOK_sound (hL j (mem_range.mp hj))
  have hlen : (G.block j).length = n := by simp [GroupCert.block, hn, hSdef]
  refine block_nonneg h6 K hc hσ hRb (S.types.getD j 0) (fun a => S.feats.getD a 0) hfa hfa' _
    (fun x => ?_)
  have := hblock x
  rw [hlen] at this
  refine le_of_le_of_eq this (sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_)
  have ha' := mem_range.mp ha
  have hb' := mem_range.mp hb
  have ha'' : a < G.S.feats.length := ha'
  have hb'' : b < G.S.feats.length := hb'
  rw [GroupCert.block, getD_map_of_lt _ _ 0 [] (by simpa using ha''),
    getD_map_of_lt _ _ 0 0 (by simpa using hb'')]
  simp [List.getD_eq_getElem?_getD, ha'', hb'']

/-! ### Targets and the main soundness theorem -/

/-- A graph polynomial `∑ c [g]`, as a list of `(c, g)`. -/
abbrev GraphPoly := List (ℤ × ℕ)

/-- `eval_U(P) = ∑ c · t(g, U)` on a finite host. -/
def evalPoly (K : FiniteKernel d) (P : GraphPoly) : ℝ := (P.map fun x => (x.1 : ℝ) * evalMask K x.2).sum

/-- The target's items: one per monomial, with its witnessed orbit. -/
def targetItems (P : GraphPoly) (Wt : List ℕ) : List (ℕ × ℤ) :=
  (P.zip Wt).map fun x => (witOrb x.2, x.1.1)

/-- Kernel loop over the target. -/
def accTarget : GraphPoly → List ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → Bool) → Bool
  | x :: xs, w :: ws, p, q, m, k => accStep p q m (witOrb w) x.1 fun p q m => accTarget xs ws p q m k
  | _, _, p, q, m, k => k p q m

lemma accTarget_eq : ∀ (P : GraphPoly) (Wt : List ℕ) (p q m : ℕ) (k : ℕ → ℕ → ℕ → Bool),
    accTarget P Wt p q m k = accList (targetItems P Wt) p q m k
  | x :: xs, w :: ws, p, q, m, k => by
    rw [accTarget, targetItems, List.zip_cons_cons, List.map_cons, accList]
    exact congrArg _ (funext fun p => funext fun q => funext fun m => accTarget_eq xs ws p q m k)
  | [], _, p, q, m, k => by simp [accTarget, targetItems, accList]
  | _ :: _, [], p, q, m, k => by simp [accTarget, targetItems, accList]

lemma itemSum_targetItems (K : FiniteKernel d) {rep : ℕ → ℕ} {P : GraphPoly} {Wt : List ℕ}
    (h : all2 (fun x w => witOK rep x.2 w) P Wt = true) :
    itemSum K rep (targetItems P Wt) = evalPoly K P := by
  obtain ⟨hlen, hw⟩ := all2_sound (0, 0) 0 h
  rw [itemSum, targetItems, List.map_map, sum_zip_getD (0, 0) 0 _ _ _ hlen, evalPoly,
    sum_map_getD (0, 0)]
  refine sum_congr rfl fun i hi => ?_
  simp only [Function.comp_apply]
  rw [← evalMask_of_witOK K (hw i (mem_range.mp hi))]

/-- All groups' items, each scaled by its weight. -/
def allItems (Gs : List GroupCert) : List (ℕ × ℤ) :=
  Gs.flatMap fun G => scaleItems G.S.weight G.items

/-- The packed value of an item list. -/
def packed (l : List (ℕ × ℤ)) : ℤ := (l.map fun x => x.2 * (2 : ℤ) ^ (128 * x.1)).sum

lemma itemSum_allItems_nonneg (K : FiniteKernel d) {rep : ℕ → ℕ} :
    ∀ Gs : List GroupCert, (∀ G ∈ Gs, G.valid rep) → 0 ≤ itemSum K rep (allItems Gs)
  | [], _ => by simp [allItems, itemSum]
  | G :: Gs, hG => by
    rw [allItems, List.flatMap_cons, itemSum_append, ← allItems]
    refine add_nonneg ?_ (itemSum_allItems_nonneg K Gs fun G' hG' => hG G' (List.mem_cons_of_mem _ hG'))
    rw [itemSum_scaleItems]
    exact mul_nonneg (Nat.cast_nonneg _) (G.itemSum_nonneg K (hG G List.mem_cons_self))

/-- **Soundness of the certificate checker** (`thm:certificate-inequalities` for one target). -/
theorem cert_sound {rep : ℕ → ℕ} {P : GraphPoly} {Wt : List ℕ} {scale : ℕ} (hscale : 0 < scale)
    {Gs : List GroupCert} (hG : ∀ G ∈ Gs, G.valid rep)
    (hWt : all2 (fun x w => witOK rep x.2 w) P Wt = true)
    (hsum : packed (scaleItems scale (targetItems P Wt)) = packed (allItems Gs))
    (hmass : massOf (scaleItems scale (targetItems P Wt)) + massOf (allItems Gs) < 2 ^ 128)
    (K : FiniteKernel d) : 0 ≤ evalPoly K P := by
  have heq : itemSum K rep (scaleItems scale (targetItems P Wt)) = itemSum K rep (allItems Gs) :=
    list_sum_eq_of_packed hsum hmass fun o => evalMask K (rep o)
  rw [itemSum_scaleItems, itemSum_targetItems K hWt] at heq
  have hnn := itemSum_allItems_nonneg K Gs hG
  rw [← heq] at hnn
  exact nonneg_of_mul_nonneg_right hnn (by exact_mod_cast hscale)

end ApicesCommonness
