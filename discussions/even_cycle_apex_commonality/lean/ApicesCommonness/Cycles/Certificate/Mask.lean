import ApicesCommonness.Common.Host.EdgeDensity
import Mathlib.Data.Nat.Bitwise

/-!
# Six-vertex masks

Blueprint `def:graph-polynomial`.  The fifteen pairs `i < j` of `Fin 6` are listed
lexicographically (`pairOf`), with position `ι(i, j) = i(11 − i)/2 + (j − i − 1)` (`pairIdx`).  A mask
`g : ℕ` stands for the graph with the edges at its set bits (`maskEdges`), evaluated on a finite host
by `evalMask`.

* `maskEdges_lor`: bitwise or is union of edge sets (the only product of masks used, always on
  disjoint edge sets — there is no relation `U_e² = U_e`);
* `maskEdges_single`: the mask `2^{ι(i,j)}` is the single edge `{i, j}`;
* `relabel g code` applies the permutation `π(i) = (code >>> 3i) mod 8` of `Fin 6` to the mask `g`,
  written with the kernel's accelerated `Nat` primitives (M0 spike, DEVIATIONS X3);
  `maskEdges_relabel` identifies it with the image of the edge set, and `evalMask_relabel` —
  **`lem:normalform-soundness`, one mask at a time** — shows a relabelled mask has the same density.
  A permutation code is checked by `isPerm` (six fields `< 6`, pairwise distinct).
-/

open Finset

namespace ApicesCommonness

/-- The fifteen pairs `i < j` of `Fin 6`, lexicographically. -/
def pairOf : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5), (4, 5)]

/-- Position of the unordered pair `{i, j}`: `i (11 − i) / 2 + (j − i − 1)` for `i < j`. -/
def pairIdx (i j : ℕ) : ℕ :=
  if i < j then i * (11 - i) / 2 + (j - i - 1) else j * (11 - j) / 2 + (i - j - 1)

lemma pairOf_lt : ∀ b : Fin 15, (pairOf b).1 < (pairOf b).2 := by decide

lemma pairIdx_pairOf : ∀ b : Fin 15, pairIdx (pairOf b).1 (pairOf b).2 = b := by decide

lemma pairOf_injective : Function.Injective pairOf := by decide

lemma pairIdx_lt : ∀ i j : Fin 6, i ≠ j → pairIdx i j < 15 := by decide

lemma pairOf_eq_sortPair : ∀ (i j : Fin 6) (b : Fin 15), i ≠ j → (b : ℕ) = pairIdx i j →
    pairOf b = sortPair i j := by decide

/-- The edge set of a mask. -/
def maskEdges (g : ℕ) : Finset (Fin 6 × Fin 6) :=
  (univ.filter fun b : Fin 15 => g.testBit b).image pairOf

lemma mem_maskEdges {g : ℕ} {p : Fin 6 × Fin 6} :
    p ∈ maskEdges g ↔ ∃ b : Fin 15, g.testBit b = true ∧ pairOf b = p := by
  simp [maskEdges]

lemma maskEdges_sorted (g : ℕ) : ∀ p ∈ maskEdges g, p.1 < p.2 := by
  intro p hp
  obtain ⟨b, -, rfl⟩ := mem_maskEdges.mp hp
  exact pairOf_lt b

lemma maskEdges_zero : maskEdges 0 = ∅ := by
  simp [maskEdges]

/-- Bitwise or is union of edge sets. -/
lemma maskEdges_lor (g h : ℕ) : maskEdges (g ||| h) = maskEdges g ∪ maskEdges h := by
  rw [maskEdges, maskEdges, maskEdges, ← image_union, ← filter_or]
  congr 1
  ext b
  simp

/-- The mask of a single edge. -/
lemma maskEdges_single {i j : Fin 6} (hij : i ≠ j) :
    maskEdges (2 ^ pairIdx i j) = {sortPair i j} := by
  ext p
  rw [mem_maskEdges, mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Nat.testBit_two_pow] at hb
    have hb' : pairIdx i j = b := by simpa using hb
    exact pairOf_eq_sortPair i j b hij hb'.symm
  · rintro rfl
    refine ⟨⟨pairIdx i j, pairIdx_lt i j hij⟩, ?_, pairOf_eq_sortPair i j _ hij rfl⟩
    simp

/-- The density of a mask on a finite host. -/
def evalMask {d : ℕ} (K : FiniteKernel d) (g : ℕ) : ℝ := edgeDensity K.w (maskEdges g) K.U

/-! ### Relabelling -/

/-- Field `i` of a permutation code, `π(i) = (code >>> 3i) mod 8`. -/
def permAt (code i : ℕ) : ℕ := Nat.mod (Nat.shiftRight code (Nat.mul 3 i)) 8

/-- The six fields of `code` are `< 6` and pairwise distinct. -/
def isPerm (code : ℕ) : Bool :=
  Nat.blt (permAt code 0) 6 && Nat.blt (permAt code 1) 6 && Nat.blt (permAt code 2) 6 &&
  Nat.blt (permAt code 3) 6 && Nat.blt (permAt code 4) 6 && Nat.blt (permAt code 5) 6 &&
  !Nat.beq (permAt code 0) (permAt code 1) && !Nat.beq (permAt code 0) (permAt code 2) &&
  !Nat.beq (permAt code 0) (permAt code 3) && !Nat.beq (permAt code 0) (permAt code 4) &&
  !Nat.beq (permAt code 0) (permAt code 5) && !Nat.beq (permAt code 1) (permAt code 2) &&
  !Nat.beq (permAt code 1) (permAt code 3) && !Nat.beq (permAt code 1) (permAt code 4) &&
  !Nat.beq (permAt code 1) (permAt code 5) && !Nat.beq (permAt code 2) (permAt code 3) &&
  !Nat.beq (permAt code 2) (permAt code 4) && !Nat.beq (permAt code 2) (permAt code 5) &&
  !Nat.beq (permAt code 3) (permAt code 4) && !Nat.beq (permAt code 3) (permAt code 5) &&
  !Nat.beq (permAt code 4) (permAt code 5)

/-- Endpoints of edge `b`, read from packed 3-bit tables (kernel-friendly). -/
def edgeFst (b : ℕ) : ℕ := Nat.mod (Nat.shiftRight 19467226873856 (Nat.mul 3 b)) 8
def edgeSnd (b : ℕ) : ℕ := Nat.mod (Nat.shiftRight 25061629974737 (Nat.mul 3 b)) 8

lemma edgeFst_eq : ∀ b : Fin 15, edgeFst b = (pairOf b).1 := by decide
lemma edgeSnd_eq : ∀ b : Fin 15, edgeSnd b = (pairOf b).2 := by decide

/-- The contribution of bit `b` of `g` to the relabelled mask. -/
def relabelBit (g code b : ℕ) : ℕ :=
  Nat.shiftLeft (Nat.land (Nat.shiftRight g b) 1)
    (pairIdx (permAt code (edgeFst b)) (permAt code (edgeSnd b)))

/-- The relabelled mask, bit by bit. -/
def relabelGo (g code : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => Nat.lor (relabelGo g code b) (relabelBit g code b)

/-- `π · g` for the permutation encoded by `code`. -/
def relabel (g code : ℕ) : ℕ := relabelGo g code 15

section Soundness

variable {code : ℕ}

private lemma nat_beq_false {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · exact Nat.ne_of_beq_eq_false
  · intro h
    cases hb : Nat.beq a b
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- A checked code gives a permutation of `Fin 6`. -/
lemma permAt_lt (hc : isPerm code = true) (i : Fin 6) : permAt code i < 6 := by
  simp only [isPerm, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', nat_beq_false]
    at hc
  fin_cases i <;> simp_all

lemma permAt_injective (hc : isPerm code = true) {i j : Fin 6} (h : permAt code i = permAt code j) :
    i = j := by
  simp only [isPerm, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', nat_beq_false]
    at hc
  fin_cases i <;> fin_cases j <;> simp_all

/-- The permutation of `Fin 6` encoded by a checked code. -/
noncomputable def permOf (hc : isPerm code = true) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (fun i => ⟨permAt code i, permAt_lt hc i⟩)
    (Finite.injective_iff_bijective.mp fun _ _ h =>
      permAt_injective hc (congrArg Fin.val h))

lemma permOf_apply (hc : isPerm code = true) (i : Fin 6) :
    ((permOf hc i : Fin 6) : ℕ) = permAt code i := rfl

/-- The bit contribution is either nothing or the single relabelled edge. -/
lemma relabelBit_eq (g : ℕ) (b : Fin 15) (hc : isPerm code = true) :
    relabelBit g code b = if g.testBit b then
      2 ^ pairIdx (permOf hc (pairOf b).1) (permOf hc (pairOf b).2) else 0 := by
  have hbit : Nat.land (Nat.shiftRight g b) 1 = if g.testBit b then 1 else 0 := by
    have ht : g.testBit b = decide ((g >>> (b : ℕ)) % 2 = 1) := by
      rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
    rw [show Nat.land (Nat.shiftRight g b) 1 = (g >>> (b : ℕ)) &&& 1 from rfl, Nat.and_one_is_mod,
      ht]
    rcases Nat.mod_two_eq_zero_or_one (g >>> (b : ℕ)) with h | h <;> simp [h]
  rw [relabelBit, hbit, permOf_apply, permOf_apply, edgeFst_eq, edgeSnd_eq]
  split_ifs <;> simp [Nat.shiftLeft_eq]

/-- The relabelled mask of the first `n` bits. -/
lemma maskEdges_relabelGo (g : ℕ) (hc : isPerm code = true) :
    ∀ n ≤ 15, maskEdges (relabelGo g code n)
      = ((univ.filter fun b : Fin 15 => (b : ℕ) < n ∧ g.testBit b = true).image fun b =>
          sortPair (permOf hc (pairOf b).1) (permOf hc (pairOf b).2))
  | 0, _ => by simp [relabelGo, maskEdges_zero]
  | n + 1, hn => by
    have hn' : n < 15 := by omega
    rw [relabelGo, show Nat.lor (relabelGo g code n) (relabelBit g code n)
      = relabelGo g code n ||| relabelBit g code n from rfl, maskEdges_lor,
      maskEdges_relabelGo g hc n (by omega)]
    have hb := relabelBit_eq (code := code) g ⟨n, hn'⟩ hc
    rw [hb]
    ext p
    simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro (⟨b, ⟨hbn, hbg⟩, rfl⟩ | hp)
      · exact ⟨b, ⟨by omega, hbg⟩, rfl⟩
      · split_ifs at hp with hg
        · have hne : permOf hc (pairOf ⟨n, hn'⟩).1 ≠ permOf hc (pairOf ⟨n, hn'⟩).2 :=
            (permOf hc).injective.ne (pairOf_lt _).ne
          rw [maskEdges_single hne, mem_singleton] at hp
          exact ⟨⟨n, hn'⟩, ⟨by simp, hg⟩, hp.symm⟩
        · simp [maskEdges_zero] at hp
    · rintro ⟨b, ⟨hbn, hbg⟩, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hbn with hlt | heq
      · exact Or.inl ⟨b, ⟨hlt, hbg⟩, rfl⟩
      · right
        have hb' : b = ⟨n, hn'⟩ := Fin.ext heq
        subst hb'
        rw [if_pos hbg]
        have hne : permOf hc (pairOf ⟨n, hn'⟩).1 ≠ permOf hc (pairOf ⟨n, hn'⟩).2 :=
          (permOf hc).injective.ne (pairOf_lt _).ne
        rw [maskEdges_single hne, mem_singleton]

/-- **Relabelling a mask relabels its edge set.** -/
lemma maskEdges_relabel (g : ℕ) (hc : isPerm code = true) :
    maskEdges (relabel g code)
      = (maskEdges g).image fun p => sortPair (permOf hc p.1) (permOf hc p.2) := by
  rw [relabel, maskEdges_relabelGo g hc 15 le_rfl, maskEdges, image_image]
  congr 1
  ext b
  simp

/-- **`lem:normalform-soundness`, one mask.**  A relabelled mask has the same density on every
finite host. -/
theorem evalMask_relabel {d : ℕ} (K : FiniteKernel d) (g : ℕ) (hc : isPerm code = true) :
    evalMask K (relabel g code) = evalMask K g := by
  rw [evalMask, evalMask, maskEdges_relabel g hc]
  exact edgeDensity_image_sortPair K.w K.U_symm (permOf hc) (maskEdges_sorted g)

end Soundness

end ApicesCommonness
