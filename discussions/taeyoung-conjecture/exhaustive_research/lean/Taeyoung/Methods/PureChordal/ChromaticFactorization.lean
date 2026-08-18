import Taeyoung.Methods.PureChordal.BalancedMultipartite
import Taeyoung.Methods.PureChordal.CertificatePolynomialBound
import Taeyoung.Methods.PureChordal.ChordalStructure
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Colouring count of a pure clique tree

The vertices introduced by a bag are coloured after all earlier bags.  Once the
separator colours are fixed, the new vertices can be coloured in
`(k-s)_(r-s)` ways.  This is the finite combinatorial factorisation underlying
both the chromatic-polynomial formula and sharpness of the balanced
multipartite graphon.
-/

namespace Taeyoung.Methods.PureChordal

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} {r m : ℕ}
variable (D : PureCliqueTreeDecomp H r m)

namespace PureCliqueTreeDecomp

/-- A colour assignment on the vertices exposed before step `n`, injective on
every earlier clique bag. -/
def PrefixColoring (k n : ℕ) :=
  {c : ↥(D.accumulatedVerticesLT n) → Fin k //
    ∀ (i : Fin m) (hi : i.val < n),
      Function.Injective (fun v : ↥(D.bag i) ↦
        c ⟨v, D.bag_subset_accumulatedVerticesLT hi v.property⟩)}

noncomputable instance prefixColoringFintype (k n : ℕ) :
    Fintype (D.PrefixColoring k n) := by
  classical
  unfold PrefixColoring
  infer_instance

lemma separator_subset_accumulatedVerticesLT (i : Fin m) :
    D.separator i ⊆ D.accumulatedVerticesLT i.val := by
  intro v hv
  have hv' : v ∈ D.accumulatedVerticesLT i.val ∩ D.bag i := by
    rw [D.accumulatedVerticesLT_inter_bag]
    exact hv
  exact (Finset.mem_inter.mp hv').1

/-- The colour of a separator vertex in a prefix colouring. -/
def separatorColor {k : ℕ} (i : Fin m)
    (c : D.PrefixColoring k i.val) (v : ↥(D.separator i)) : Fin k :=
  c.1 ⟨v, D.separator_subset_accumulatedVerticesLT i v.property⟩

/-- Colours still available after removing the colours on the separator. -/
def availableColors {k : ℕ} (i : Fin m)
    (c : D.PrefixColoring k i.val) : Finset (Fin k) :=
  Finset.univ \ (D.separator i).attach.image (D.separatorColor i c)

lemma separatorColor_injective {k : ℕ} (i : Fin m)
    (c : D.PrefixColoring k i.val) :
    Function.Injective (D.separatorColor i c) := by
  by_cases hi : i = D.root
  · subst i
    intro a
    exact False.elim (by simpa using a.property)
  · intro a b hab
    have hlt := D.parent_lt i hi
    have hpa : a.1 ∈ D.bag (D.parent i) := by
      have ha := a.property
      simp only [D.separator_of_ne_root hi, Finset.mem_inter] at ha
      exact ha.2
    have hpb : b.1 ∈ D.bag (D.parent i) := by
      have hb := b.property
      simp only [D.separator_of_ne_root hi, Finset.mem_inter] at hb
      exact hb.2
    have hp : Function.Injective
        (fun v : ↥(D.bag (D.parent i)) ↦
          c.1 ⟨v, D.bag_subset_accumulatedVerticesLT hlt v.property⟩) :=
      c.property (D.parent i) hlt
    let a' : ↥(D.bag (D.parent i)) := ⟨a.1, hpa⟩
    let b' : ↥(D.bag (D.parent i)) := ⟨b.1, hpb⟩
    have hab' :
        (fun v : ↥(D.bag (D.parent i)) ↦
          c.1 ⟨v, D.bag_subset_accumulatedVerticesLT hlt v.property⟩) a' =
        (fun v : ↥(D.bag (D.parent i)) ↦
          c.1 ⟨v, D.bag_subset_accumulatedVerticesLT hlt v.property⟩) b' := by
      simpa [separatorColor] using hab
    have habval : a'.1 = b'.1 := congrArg Subtype.val (hp hab')
    apply Subtype.ext
    exact habval

lemma card_availableColors {k : ℕ} (i : Fin m)
    (c : D.PrefixColoring k i.val) :
    (D.availableColors i c).card = k - D.sepCard i := by
  rw [availableColors, Finset.card_sdiff]
  have himage :
      ((D.separator i).attach.image (D.separatorColor i c)).card =
        (D.separator i).card := by
    calc
      ((D.separator i).attach.image (D.separatorColor i c)).card =
          (D.separator i).attach.card := Finset.card_image_iff.mpr <| by
            intro a ha b hb hab
            exact D.separatorColor_injective i c hab
      _ = (D.separator i).card := Finset.card_attach
  rw [Finset.inter_eq_left.mpr (Finset.subset_univ _), himage]
  simp [sepCard]

lemma separatorColor_not_mem_available {k : ℕ} (i : Fin m)
    (c : D.PrefixColoring k i.val) (v : ↥(D.separator i)) :
    D.separatorColor i c v ∉ D.availableColors i c := by
  simp only [availableColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
    not_not]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, rfl⟩

lemma accumulatedVerticesLT_succ_eq_new_union {n : ℕ} (hn : n < m) :
    D.accumulatedVerticesLT (n + 1) =
      D.newVertices ⟨n, hn⟩ ∪ D.accumulatedVerticesLT n := by
  rw [D.accumulatedVerticesLT_succ hn,
    D.newVertices_eq_bag_sdiff_previous,
    D.previousVertices_eq_accumulatedVerticesLT]
  ext v
  simp

/-- Forget the newest bag of a prefix colouring. -/
def restrictPrefix {k n : ℕ} (hn : n < m)
    (d : D.PrefixColoring k (n + 1)) : D.PrefixColoring k n where
  val v :=
    d.1 ⟨v, by
      rw [D.accumulatedVerticesLT_succ hn]
      exact Finset.mem_union_right _ v.property⟩
  property i hi := by
    have hd := d.property i (lt_trans hi (Nat.lt_succ_self n))
    intro a b hab
    apply Subtype.ext
    exact congrArg Subtype.val (hd hab)

@[simp] lemma restrictPrefix_apply {k n : ℕ} (hn : n < m)
    (d : D.PrefixColoring k (n + 1))
    (v : ↥(D.accumulatedVerticesLT n)) :
    (D.restrictPrefix hn d).1 v =
      d.1 ⟨v, by
        rw [D.accumulatedVerticesLT_succ hn]
        exact Finset.mem_union_right _ v.property⟩ :=
  rfl

/-- Extend a prefix by assigning pairwise distinct available colours to the
vertices introduced by the next bag. -/
def extendColor {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n)
    (e : ↥(D.newVertices ⟨n, hn⟩) ↪ ↥(D.availableColors ⟨n, hn⟩ c))
    (v : ↥(D.accumulatedVerticesLT (n + 1))) : Fin k :=
  if hv : v.1 ∈ D.accumulatedVerticesLT n then
    c.1 ⟨v.1, hv⟩
  else
    (e ⟨v.1, by
      have hvUnion :
          v.1 ∈ D.newVertices ⟨n, hn⟩ ∪ D.accumulatedVerticesLT n := by
        rw [← D.accumulatedVerticesLT_succ_eq_new_union hn]
        exact v.property
      exact (Finset.mem_union.mp hvUnion).resolve_right hv⟩).1

@[simp] lemma extendColor_of_mem_old {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n)
    (e : ↥(D.newVertices ⟨n, hn⟩) ↪ ↥(D.availableColors ⟨n, hn⟩ c))
    (v : ↥(D.accumulatedVerticesLT (n + 1)))
    (hv : v.1 ∈ D.accumulatedVerticesLT n) :
    D.extendColor hn c e v = c.1 ⟨v.1, hv⟩ := by
  simp [extendColor, hv]

@[simp] lemma extendColor_of_mem_new {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n)
    (e : ↥(D.newVertices ⟨n, hn⟩) ↪ ↥(D.availableColors ⟨n, hn⟩ c))
    (v : ↥(D.accumulatedVerticesLT (n + 1)))
    (hv : v.1 ∈ D.newVertices ⟨n, hn⟩) :
    D.extendColor hn c e v = (e ⟨v.1, hv⟩).1 := by
  have hnot : v.1 ∉ D.accumulatedVerticesLT n :=
    Finset.disjoint_left.mp
      (D.newVertices_disjoint_accumulatedVerticesLT ⟨n, hn⟩) hv
  simp [extendColor, hnot]

/-- A bag vertex already exposed before its own bag lies in the parent
separator. -/
lemma mem_separator_of_mem_accumulated {i : Fin m} {v : V}
    (hbag : v ∈ D.bag i) (hacc : v ∈ D.accumulatedVerticesLT i.val) :
    v ∈ D.separator i := by
  have hmem : v ∈ D.accumulatedVerticesLT i.val ∩ D.bag i :=
    Finset.mem_inter.mpr ⟨hacc, hbag⟩
  rw [D.accumulatedVerticesLT_inter_bag] at hmem
  exact hmem

/-- A bag vertex not yet exposed before its own bag is one of its new
vertices. -/
lemma mem_newVertices_of_notMem_accumulated {i : Fin m} {v : V}
    (hbag : v ∈ D.bag i) (hacc : v ∉ D.accumulatedVerticesLT i.val) :
    v ∈ D.newVertices i := by
  rw [D.newVertices_eq_bag_sdiff_previous,
    D.previousVertices_eq_accumulatedVerticesLT]
  exact Finset.mem_sdiff.mpr ⟨hbag, hacc⟩

lemma extendColor_current_injective {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n)
    (e : ↥(D.newVertices ⟨n, hn⟩) ↪ ↥(D.availableColors ⟨n, hn⟩ c)) :
    Function.Injective (fun v : ↥(D.bag ⟨n, hn⟩) ↦
      D.extendColor hn c e
        ⟨v, D.bag_subset_accumulatedVerticesLT (Nat.lt_succ_self n)
          v.property⟩) := by
  let i : Fin m := ⟨n, hn⟩
  intro a b hab
  by_cases ha : a.1 ∈ D.accumulatedVerticesLT n
  · by_cases hb : b.1 ∈ D.accumulatedVerticesLT n
    · have hasa := D.mem_separator_of_mem_accumulated a.property ha
      have hasb := D.mem_separator_of_mem_accumulated b.property hb
      have hcolor :
          D.separatorColor i c ⟨a.1, hasa⟩ =
            D.separatorColor i c ⟨b.1, hasb⟩ := by
        simpa [i, separatorColor, extendColor, ha, hb] using hab
      have hsep := D.separatorColor_injective i c hcolor
      exact Subtype.ext (congrArg (fun z : ↥(D.separator i) ↦ z.1) hsep)
    · have hasa := D.mem_separator_of_mem_accumulated a.property ha
      have hbnew := D.mem_newVertices_of_notMem_accumulated b.property hb
      have hcolor :
          D.separatorColor i c ⟨a.1, hasa⟩ =
            (e ⟨b.1, hbnew⟩).1 := by
        simpa [i, separatorColor, extendColor, ha, hb] using hab
      exfalso
      apply D.separatorColor_not_mem_available i c ⟨a.1, hasa⟩
      simp [hcolor]
  · by_cases hb : b.1 ∈ D.accumulatedVerticesLT n
    · have hasb := D.mem_separator_of_mem_accumulated b.property hb
      have hanew := D.mem_newVertices_of_notMem_accumulated a.property ha
      have hcolor :
          (e ⟨a.1, hanew⟩).1 =
            D.separatorColor i c ⟨b.1, hasb⟩ := by
        simpa [i, separatorColor, extendColor, ha, hb] using hab
      exfalso
      apply D.separatorColor_not_mem_available i c ⟨b.1, hasb⟩
      simp [← hcolor]
    · have hanew := D.mem_newVertices_of_notMem_accumulated a.property ha
      have hbnew := D.mem_newVertices_of_notMem_accumulated b.property hb
      have hcolor : e ⟨a.1, hanew⟩ = e ⟨b.1, hbnew⟩ := by
        apply Subtype.ext
        simpa [i, extendColor, ha, hb] using hab
      have hnew := e.injective hcolor
      exact Subtype.ext (congrArg (fun z : ↥(D.newVertices i) ↦ z.1) hnew)

/-- Assemble a valid successor prefix from an old prefix and an injection into
the available colours. -/
def extendPrefix {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n)
    (e : ↥(D.newVertices ⟨n, hn⟩) ↪ ↥(D.availableColors ⟨n, hn⟩ c)) :
    D.PrefixColoring k (n + 1) where
  val := D.extendColor hn c e
  property i hi := by
    by_cases hin : i.val < n
    · have hc := c.property i hin
      intro a b hab
      have haold := D.bag_subset_accumulatedVerticesLT hin a.property
      have hbold := D.bag_subset_accumulatedVerticesLT hin b.property
      have hcolor :
          c.1 ⟨a.1, haold⟩ = c.1 ⟨b.1, hbold⟩ := by
        simpa [extendColor, haold, hbold] using hab
      have hold := hc hcolor
      apply Subtype.ext
      exact congrArg Subtype.val hold
    · have hle : i.val ≤ n := Nat.lt_succ_iff.mp (by simpa using hi)
      have hge : n ≤ i.val := Nat.le_of_not_gt hin
      have hieq : i = ⟨n, hn⟩ :=
        Fin.ext (Nat.le_antisymm hle hge)
      subst i
      exact D.extendColor_current_injective hn c e

lemma newVertices_subset_accumulatedVerticesLT_succ {n : ℕ} (hn : n < m) :
    D.newVertices ⟨n, hn⟩ ⊆ D.accumulatedVerticesLT (n + 1) := by
  intro v hv
  rw [D.accumulatedVerticesLT_succ_eq_new_union hn]
  exact Finset.mem_union_left _ hv

/-- Extract from a successor prefix the injective assignment on its newly
introduced vertices. -/
def newColorEmbedding {k n : ℕ} (hn : n < m)
    (d : D.PrefixColoring k (n + 1)) :
    ↥(D.newVertices ⟨n, hn⟩) ↪
      ↥(D.availableColors ⟨n, hn⟩ (D.restrictPrefix hn d)) where
  toFun v :=
    ⟨d.1 ⟨v.1, D.newVertices_subset_accumulatedVerticesLT_succ hn v.property⟩,
      by
        simp only [availableColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_image, not_exists]
        intro w hw
        rcases hw with ⟨hw, heq⟩
        have hwbag : w.1 ∈ D.bag ⟨n, hn⟩ :=
          D.separator_subset_bag ⟨n, hn⟩ w.property
        have hcolor :
            d.1 ⟨v.1,
              D.newVertices_subset_accumulatedVerticesLT_succ hn v.property⟩ =
            d.1 ⟨w.1,
              D.bag_subset_accumulatedVerticesLT (Nat.lt_succ_self n)
                hwbag⟩ := by
          simpa [separatorColor, restrictPrefix] using heq.symm
        have hinj := d.property ⟨n, hn⟩ (Nat.lt_succ_self n)
        have hbag :
            (⟨v.1, (Finset.mem_sdiff.mp v.property).1⟩ :
                ↥(D.bag ⟨n, hn⟩)) =
              ⟨w.1, hwbag⟩ :=
          hinj hcolor
        have hval : v.1 = w.1 :=
          congrArg (fun z : ↥(D.bag ⟨n, hn⟩) ↦ z.1) hbag
        have hwold :
            w.1 ∈ D.accumulatedVerticesLT n :=
          D.separator_subset_accumulatedVerticesLT ⟨n, hn⟩ w.property
        have hvnot :
            v.1 ∉ D.accumulatedVerticesLT n :=
          Finset.disjoint_left.mp
            (D.newVertices_disjoint_accumulatedVerticesLT ⟨n, hn⟩)
            v.property
        exact hvnot (hval ▸ hwold)⟩
  inj' := by
    intro a b hab
    have hcolor :
        d.1 ⟨a.1,
          D.newVertices_subset_accumulatedVerticesLT_succ hn a.property⟩ =
        d.1 ⟨b.1,
          D.newVertices_subset_accumulatedVerticesLT_succ hn b.property⟩ :=
      congrArg Subtype.val hab
    have hinj := d.property ⟨n, hn⟩ (Nat.lt_succ_self n)
    have hbag :
        (⟨a.1, (Finset.mem_sdiff.mp a.property).1⟩ :
            ↥(D.bag ⟨n, hn⟩)) =
          ⟨b.1, (Finset.mem_sdiff.mp b.property).1⟩ :=
      hinj hcolor
    apply Subtype.ext
    exact congrArg (fun z : ↥(D.bag ⟨n, hn⟩) ↦ z.1) hbag

lemma restrictPrefix_extendPrefix {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n)
    (e : ↥(D.newVertices ⟨n, hn⟩) ↪ ↥(D.availableColors ⟨n, hn⟩ c)) :
    D.restrictPrefix hn (D.extendPrefix hn c e) = c := by
  apply Subtype.ext
  funext v
  simp [restrictPrefix, extendPrefix, extendColor]

lemma extendPrefix_restrictPrefix_newColorEmbedding {k n : ℕ} (hn : n < m)
    (d : D.PrefixColoring k (n + 1)) :
    D.extendPrefix hn (D.restrictPrefix hn d) (D.newColorEmbedding hn d) = d := by
  apply Subtype.ext
  funext v
  by_cases hv : v.1 ∈ D.accumulatedVerticesLT n
  · simp [extendPrefix, extendColor, restrictPrefix, hv]
  · have hvnew : v.1 ∈ D.newVertices ⟨n, hn⟩ := by
      have hvUnion :
          v.1 ∈ D.newVertices ⟨n, hn⟩ ∪ D.accumulatedVerticesLT n := by
        rw [← D.accumulatedVerticesLT_succ_eq_new_union hn]
        exact v.property
      exact (Finset.mem_union.mp hvUnion).resolve_right hv
    simp [extendPrefix, extendColor, newColorEmbedding, hv]

/-- The fibre of prefix restriction over a fixed old prefix. -/
def PrefixFiber {k n : ℕ} (hn : n < m) (c : D.PrefixColoring k n) :=
  {d : D.PrefixColoring k (n + 1) // D.restrictPrefix hn d = c}

noncomputable instance prefixFiberFintype {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n) : Fintype (D.PrefixFiber hn c) := by
  classical
  unfold PrefixFiber
  infer_instance

/-- The fresh-colour embedding of a member of a fixed restriction fibre.  This
definition records the target prefix directly, avoiding any casts in the
counting equivalence. -/
def fiberEmbedding {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n) (z : D.PrefixFiber hn c) :
    ↥(D.newVertices ⟨n, hn⟩) ↪
      ↥(D.availableColors ⟨n, hn⟩ c) where
  toFun v :=
    ⟨(D.newColorEmbedding hn z.1 v).1, by
      simp only [availableColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_image, not_exists]
      intro w hw
      rcases hw with ⟨hw, heq⟩
      have hwbag : w.1 ∈ D.bag ⟨n, hn⟩ :=
        D.separator_subset_bag ⟨n, hn⟩ w.property
      have hwold :
          w.1 ∈ D.accumulatedVerticesLT n :=
        D.separator_subset_accumulatedVerticesLT ⟨n, hn⟩ w.property
      have hprefix :
          (D.restrictPrefix hn z.1).1 ⟨w.1, hwold⟩ =
            c.1 ⟨w.1, hwold⟩ :=
        congrArg (fun q : D.PrefixColoring k n ↦ q.1 ⟨w.1, hwold⟩)
          z.property
      have hcolor :
          z.1.1 ⟨v.1,
              D.newVertices_subset_accumulatedVerticesLT_succ hn v.property⟩ =
            z.1.1 ⟨w.1,
              D.bag_subset_accumulatedVerticesLT (Nat.lt_succ_self n)
                hwbag⟩ := by
        calc
          z.1.1 ⟨v.1,
              D.newVertices_subset_accumulatedVerticesLT_succ hn v.property⟩ =
              D.separatorColor ⟨n, hn⟩ c w := heq.symm
          _ = c.1 ⟨w.1, hwold⟩ := by rfl
          _ = (D.restrictPrefix hn z.1).1 ⟨w.1, hwold⟩ := hprefix.symm
          _ = z.1.1 ⟨w.1,
              D.bag_subset_accumulatedVerticesLT (Nat.lt_succ_self n)
                hwbag⟩ := by rfl
      have hinj := z.1.property ⟨n, hn⟩ (Nat.lt_succ_self n)
      have hbag :
          (⟨v.1, (Finset.mem_sdiff.mp v.property).1⟩ :
              ↥(D.bag ⟨n, hn⟩)) =
            ⟨w.1, hwbag⟩ :=
        hinj hcolor
      have hval : v.1 = w.1 :=
        congrArg (fun q : ↥(D.bag ⟨n, hn⟩) ↦ q.1) hbag
      have hvnot :
          v.1 ∉ D.accumulatedVerticesLT n :=
        Finset.disjoint_left.mp
          (D.newVertices_disjoint_accumulatedVerticesLT ⟨n, hn⟩)
          v.property
      exact hvnot (hval ▸ hwold)⟩
  inj' := by
    intro a b hab
    apply (D.newColorEmbedding hn z.1).injective
    have hval :
        (D.newColorEmbedding hn z.1 a).1 =
          (D.newColorEmbedding hn z.1 b).1 :=
      congrArg (fun q : ↥(D.availableColors ⟨n, hn⟩ c) ↦ q.1) hab
    apply Subtype.ext
    exact hval

/-- A restriction fibre is equivalent to the injections of the fresh vertices
into the colours left available by its separator. -/
noncomputable def prefixFiberEquiv {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n) :
    D.PrefixFiber hn c ≃
      (↥(D.newVertices ⟨n, hn⟩) ↪
        ↥(D.availableColors ⟨n, hn⟩ c)) where
  toFun z := D.fiberEmbedding hn c z
  invFun e := ⟨D.extendPrefix hn c e, D.restrictPrefix_extendPrefix hn c e⟩
  left_inv z := by
    rcases z with ⟨d, hd⟩
    subst c
    have he :
        D.fiberEmbedding hn (D.restrictPrefix hn d) ⟨d, rfl⟩ =
          D.newColorEmbedding hn d := by
      apply Function.Embedding.ext
      intro v
      apply Subtype.ext
      rfl
    apply Subtype.ext
    dsimp
    change D.extendPrefix hn (D.restrictPrefix hn d)
      (D.fiberEmbedding hn (D.restrictPrefix hn d) ⟨d, rfl⟩) = d
    rw [he]
    exact D.extendPrefix_restrictPrefix_newColorEmbedding hn d
  right_inv e := by
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    have hvnot :
        v.1 ∉ D.accumulatedVerticesLT n :=
      Finset.disjoint_left.mp
        (D.newVertices_disjoint_accumulatedVerticesLT ⟨n, hn⟩)
        v.property
    change (if h : v.1 ∈ D.accumulatedVerticesLT n then
      c.1 ⟨v.1, h⟩ else (e v).1) = (e v).1
    rw [dif_neg hvnot]

lemma card_prefixFiber {k n : ℕ} (hn : n < m)
    (c : D.PrefixColoring k n) :
    Fintype.card (D.PrefixFiber hn c) =
      (k - D.sepCard ⟨n, hn⟩).descFactorial
        (r - D.sepCard ⟨n, hn⟩) := by
  calc
    Fintype.card (D.PrefixFiber hn c) =
        Fintype.card
          (↥(D.newVertices ⟨n, hn⟩) ↪
            ↥(D.availableColors ⟨n, hn⟩ c)) :=
      Fintype.card_congr (D.prefixFiberEquiv hn c)
    _ = (Fintype.card ↥(D.availableColors ⟨n, hn⟩ c)).descFactorial
          (Fintype.card ↥(D.newVertices ⟨n, hn⟩)) := by
      simp
    _ = (k - D.sepCard ⟨n, hn⟩).descFactorial
          (r - D.sepCard ⟨n, hn⟩) := by
      rw [Fintype.card_coe, Fintype.card_coe, D.card_availableColors,
        D.card_newVertices]

lemma card_prefixColoring_succ {k n : ℕ} (hn : n < m) :
    Fintype.card (D.PrefixColoring k (n + 1)) =
      Fintype.card (D.PrefixColoring k n) *
        (k - D.sepCard ⟨n, hn⟩).descFactorial
          (r - D.sepCard ⟨n, hn⟩) := by
  classical
  let f : D.PrefixColoring k (n + 1) → D.PrefixColoring k n :=
    D.restrictPrefix hn
  letI (c : D.PrefixColoring k n) : Fintype {d // f d = c} := by
    infer_instance
  calc
    Fintype.card (D.PrefixColoring k (n + 1)) =
        Fintype.card (Σ c : D.PrefixColoring k n, {d // f d = c}) := by
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ c : D.PrefixColoring k n,
          Fintype.card (D.PrefixFiber hn c) := by
      simp only [Fintype.card_sigma]
      rfl
    _ = ∑ _c : D.PrefixColoring k n,
          (k - D.sepCard ⟨n, hn⟩).descFactorial
            (r - D.sepCard ⟨n, hn⟩) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact D.card_prefixFiber hn c
    _ = Fintype.card (D.PrefixColoring k n) *
          (k - D.sepCard ⟨n, hn⟩).descFactorial
            (r - D.sepCard ⟨n, hn⟩) := by simp

lemma card_prefixColoring_zero (k : ℕ) :
    Fintype.card (D.PrefixColoring k 0) = 1 := by
  let c₀ : D.PrefixColoring k 0 :=
    ⟨fun v ↦ False.elim (by
        have hv : v.1 ∈ (∅ : Finset V) := by
          simpa only [D.accumulatedVerticesLT_zero] using v.property
        exact (by simp at hv)),
      by
        intro i hi
        omega⟩
  have hsub : Subsingleton (D.PrefixColoring k 0) := by
    constructor
    intro a b
    apply Subtype.ext
    funext v
    have hv : v.1 ∈ (∅ : Finset V) := by
      simpa only [D.accumulatedVerticesLT_zero] using v.property
    exact False.elim (by simp at hv)
  letI : Unique (D.PrefixColoring k 0) :=
    { default := c₀
      uniq := fun a ↦ hsub.elim a c₀ }
  exact Fintype.card_unique

theorem card_prefixColoring (k n : ℕ) (hn : n ≤ m) :
    Fintype.card (D.PrefixColoring k n) =
      ∏ i ∈ D.bagIndicesLT n,
        (k - D.sepCard i).descFactorial (r - D.sepCard i) := by
  induction n with
  | zero =>
      simp [D.card_prefixColoring_zero, bagIndicesLT]
  | succ n ih =>
      have hnlt : n < m := Nat.lt_of_succ_le hn
      rw [D.card_prefixColoring_succ hnlt, ih (Nat.le_of_lt hnlt),
        D.bagIndicesLT_succ hnlt]
      simp [D.index_not_mem_bagIndicesLT hnlt, Nat.mul_comm]

theorem card_fullPrefixColoring (k : ℕ) :
    Fintype.card (D.PrefixColoring k m) =
      ∏ i : Fin m,
        (k - D.sepCard i).descFactorial (r - D.sepCard i) := by
  rw [D.card_prefixColoring k m le_rfl, D.bagIndicesLT_card]

/-- Proper assignments are exactly the assignments injective on every bag. -/
lemma isProperAssignment_iff_bagInjective
    [DecidableRel H.Adj] {k : ℕ} (x : V → Fin k) :
    IsProperAssignment H x ↔
      ∀ i : Fin m, Function.Injective
        (fun v : ↥(D.bag i) ↦ x v) := by
  constructor
  · intro hx i u v huv
    by_contra hne
    have hadj : H.Adj u.1 v.1 :=
      D.bag_clique i u.property v.property
        (fun h => hne (Subtype.ext h))
    exact (hx hadj) huv
  · intro hx u v huv hsame
    rcases D.edge_cover huv with ⟨i, hui, hvi⟩
    have heq : (⟨u, hui⟩ : ↥(D.bag i)) = ⟨v, hvi⟩ :=
      hx i hsame
    exact (H.ne_of_adj huv) (congrArg Subtype.val heq)

/-- Proper colour assignments are precisely full prefix colourings. -/
def properAssignmentEquivFullPrefix [DecidableRel H.Adj] (k : ℕ) :
    {x : V → Fin k // IsProperAssignment H x} ≃ D.PrefixColoring k m where
  toFun x :=
    ⟨fun v ↦ x.1 v.1,
      by
        have hx := (D.isProperAssignment_iff_bagInjective x.1).mp x.property
        intro i hi
        exact hx i⟩
  invFun c :=
    ⟨fun v ↦ c.1 ⟨v, by
        rw [D.accumulatedVerticesLT_card]
        exact Finset.mem_univ v⟩,
      by
        rw [D.isProperAssignment_iff_bagInjective]
        intro i
        have hc := c.property i i.isLt
        intro a b hab
        have hcEq := hc hab
        apply Subtype.ext
        exact congrArg Subtype.val hcEq⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    rfl
  right_inv c := by
    apply Subtype.ext
    funext v
    rfl

/-- Chromatic-factorisation formula for a pure clique tree, expressed as the
number of proper maps into `Fin k`. -/
theorem properAssignmentCount_eq_product [DecidableRel H.Adj] (k : ℕ) :
    properAssignmentCount H k =
      ∏ i : Fin m,
        (k - D.sepCard i).descFactorial (r - D.sepCard i) := by
  classical
  unfold properAssignmentCount
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {x : V → Fin k // IsProperAssignment H x} =
        Fintype.card (D.PrefixColoring k m) :=
      Fintype.card_congr (D.properAssignmentEquivFullPrefix k)
    _ = ∏ i : Fin m,
          (k - D.sepCard i).descFactorial (r - D.sepCard i) :=
      D.card_fullPrefixColoring k

/-- The explicit evaluation of the chromatic polynomial supplied by the clique
tree.  The theorem below proves its universal natural-colouring property. -/
def chromaticPolynomialEval (q : ℝ) : ℝ :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ico (D.sepCard i) r, (q - (j : ℝ))

/-- The factored chromatic polynomial of the certified pure chordal graph. -/
noncomputable def chromaticPolynomial : Polynomial ℝ :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ico (D.sepCard i) r,
    (Polynomial.X - Polynomial.C (j : ℝ))

@[simp] lemma eval_chromaticPolynomial (q : ℝ) :
    Polynomial.eval q D.chromaticPolynomial =
      D.chromaticPolynomialEval q := by
  unfold chromaticPolynomial chromaticPolynomialEval
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval_prod]
  simp

lemma chromaticTail_natCast {s k : ℕ} (hsr : s ≤ r) (hrk : r ≤ k) :
    (∏ j ∈ Finset.Ico s r, ((k : ℝ) - (j : ℝ))) =
      ((k - s).descFactorial (r - s) : ℕ) := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.descFactorial_eq_prod_range,
    Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hjlt : j < r - s := Finset.mem_range.mp hj
  have hsk : s ≤ k := hsr.trans hrk
  have hjs : j ≤ k - s := by omega
  rw [Nat.cast_sub hjs, Nat.cast_sub hsk, Nat.cast_add]
  ring

lemma chromaticPolynomialEval_natCast [DecidableRel H.Adj] (k : ℕ) :
    D.chromaticPolynomialEval (k : ℝ) =
      (properAssignmentCount H k : ℕ) := by
  by_cases hrk : r ≤ k
  · rw [D.properAssignmentCount_eq_product]
    calc
      D.chromaticPolynomialEval (k : ℝ) =
          ∏ i : Fin m,
            (((k - D.sepCard i).descFactorial
              (r - D.sepCard i) : ℕ) : ℝ) := by
        unfold chromaticPolynomialEval
        apply Finset.prod_congr rfl
        intro i hi
        exact chromaticTail_natCast (r := r) (D.sepCard_le i) hrk
      _ = ((∏ i : Fin m,
          (k - D.sepCard i).descFactorial
            (r - D.sepCard i) : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
  · have hkr : k < r := Nat.lt_of_not_ge hrk
    have heval : D.chromaticPolynomialEval (k : ℝ) = 0 := by
      unfold chromaticPolynomialEval
      apply Finset.prod_eq_zero (Finset.mem_univ D.root)
      rw [D.sepCard_root]
      apply Finset.prod_eq_zero (i := k)
      · simp [hkr]
      · simp
    have hcount : properAssignmentCount H k = 0 := by
      rw [D.properAssignmentCount_eq_product]
      apply Finset.prod_eq_zero (Finset.mem_univ D.root)
      simp [D.sepCard_root, Nat.descFactorial_eq_zero_iff_lt, hkr]
    rw [heval, hcount]
    simp

theorem eval_chromaticPolynomial_natCast [DecidableRel H.Adj] (k : ℕ) :
    Polynomial.eval (k : ℝ) D.chromaticPolynomial =
      (properAssignmentCount H k : ℕ) := by
  rw [D.eval_chromaticPolynomial, D.chromaticPolynomialEval_natCast]

/-- The factored polynomial attached to a pure clique-tree certificate is the
chromatic polynomial in the common, extensional foundation interface. -/
theorem isChromaticPolynomial [DecidableRel H.Adj] :
    Taeyoung.IsChromaticPolynomial H D.chromaticPolynomial :=
  D.eval_chromaticPolynomial_natCast

include D in
/-- The clique size of a pure clique-tree certificate is the chromatic number.

The root factor supplies a zero whenever fewer than `r` colours are available,
while every falling-factorial factor is positive at exactly `r` colours. -/
theorem isChromaticNumber [DecidableRel H.Adj] :
    Taeyoung.IsChromaticNumber H r := by
  constructor
  · rw [D.properAssignmentCount_eq_product]
    apply Finset.prod_pos
    intro i hi
    exact Nat.descFactorial_pos.mpr (by omega)
  · intro k hk
    rw [D.properAssignmentCount_eq_product]
    apply Finset.prod_eq_zero (Finset.mem_univ D.root)
    simp [D.sepCard_root, Nat.descFactorial_eq_zero_iff_lt, hk]

lemma sum_newVertexCards :
    ∑ i : Fin m, (r - D.sepCard i) = Fintype.card V := by
  have hcard := Finset.card_biUnion D.newVertices_pairwiseDisjoint
  rw [D.biUnion_newVertices] at hcard
  simp_rw [D.card_newVertices] at hcard
  simpa using hcard.symm

lemma cliquePolyTail_zero (p : ℝ) :
    cliquePolyTail 0 r p = cliquePoly r p := by
  simp [cliquePolyTail, cliquePoly]

lemma certificateBound_eq_prod_tail (p : ℝ) :
    D.certificateBound p =
      ∏ i : Fin m, cliquePolyTail (D.sepCard i) r p := by
  unfold certificateBound
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hir : i = D.root
  · subst i
    simp [D.sepCard_root, cliquePolyTail_zero]
  · simp [hir, sepCard]

lemma cliquePolyTail_eq_scaled_chromaticTail
    {s : ℕ} (_hsr : s ≤ r) {p : ℝ} (hp : p ≠ 1) :
    cliquePolyTail s r p =
      (1 - p) ^ (r - s) *
        ∏ j ∈ Finset.Ico s r,
          (1 / (1 - p) - (j : ℝ)) := by
  have hδ : 1 - p ≠ 0 := sub_ne_zero.mpr hp.symm
  have hcard : (Finset.Ico s r).card = r - s := by simp
  rw [cliquePolyTail, ← hcard, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  field_simp [hδ]

/-- Exact identification of the analytic certificate with the source
chromatic expression away from `p = 1`. -/
theorem certificateBound_eq_chromaticExpression {p : ℝ} (hp : p ≠ 1) :
    D.certificateBound p =
      (1 - p) ^ Fintype.card V *
        D.chromaticPolynomialEval (1 / (1 - p)) := by
  rw [D.certificateBound_eq_prod_tail]
  simp_rw [cliquePolyTail_eq_scaled_chromaticTail (r := r) (D.sepCard_le _)
    (p := p) hp]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    D.sum_newVertexCards]
  rfl

/-- Polynomial-object version of the certificate/chromatic identity. -/
theorem certificateBound_eq_eval_chromaticPolynomial {p : ℝ} (hp : p ≠ 1) :
    D.certificateBound p =
      (1 - p) ^ Fintype.card V *
        Polynomial.eval (1 / (1 - p)) D.chromaticPolynomial := by
  rw [D.eval_chromaticPolynomial]
  exact D.certificateBound_eq_chromaticExpression hp

/-- The balanced complete `k`-partite graphon attains the clique-tree
certificate exactly. -/
theorem certificateBound_balancedMultipartite
    [DecidableRel H.Adj] (k : ℕ) [NeZero k] :
    D.certificateBound
        (cliqueDensity 2 (balancedMultipartiteGraphon k)) =
      homDensity H (balancedMultipartiteGraphon k) := by
  have hkℝ : (k : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne k)
  have hpne : 1 - 1 / (k : ℝ) ≠ 1 := by
    intro h
    have hzero : 1 / (k : ℝ) = 0 := by linarith
    exact (one_div_ne_zero hkℝ) hzero
  rw [edgeDensity_balancedMultipartite]
  rw [D.certificateBound_eq_chromaticExpression hpne]
  have hone :
      1 - (1 - 1 / (k : ℝ)) = 1 / (k : ℝ) := by ring
  have hinv : 1 / (1 / (k : ℝ)) = (k : ℝ) := by
    field_simp
  rw [hone, hinv, D.chromaticPolynomialEval_natCast,
    homDensity_balancedMultipartite]
  simp [div_eq_mul_inv, mul_comm]

include D in
/-- At edge density `1 - 1/k`, the balanced complete `k`-partite graphon
minimizes the homomorphism density of any graph carrying this pure clique-tree
certificate `D` with clique size `r ≤ k`.  This is the certificate-level
statement of `k`-partite optimality; it needs no chordality or maximality
hypotheses beyond the existence of `D`. -/
theorem balancedMultipartite_minimal
    [DecidableRel H.Adj]
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (k : ℕ) [NeZero k]
    (W : Graphon Ω μ)
    (hr : 3 ≤ r)
    (hrk : r ≤ k)
    (hedge : cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity H (balancedMultipartiteGraphon k) ≤ homDensity H W := by
  have hrsPos : 0 < (((r - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < r - 1 by omega)
  have hrsLeK : ((r - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (show r - 1 ≤ k by omega)
  have hthreshold :
      1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W := by
    rw [hedge]
    have hinv : 1 / (k : ℝ) ≤ 1 / (((r - 1 : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le hrsPos hrsLeK
    linarith
  calc
    homDensity H (balancedMultipartiteGraphon k) =
        D.certificateBound
          (cliqueDensity 2 (balancedMultipartiteGraphon k)) :=
      (D.certificateBound_balancedMultipartite k).symm
    _ = D.certificateBound (cliqueDensity 2 W) := by
      rw [edgeDensity_balancedMultipartite, hedge]
    _ ≤ homDensity H W :=
      D.certificateBound_le_homDensity W hr hthreshold

end PureCliqueTreeDecomp

end Taeyoung.Methods.PureChordal
