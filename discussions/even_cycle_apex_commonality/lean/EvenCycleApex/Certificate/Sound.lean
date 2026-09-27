import EvenCycleApex.Certificate.Targets
import EvenCycleApex.Certificate.Schema

/-!
# Soundness in the form the kernel checks discharge

`cert_sound_of_totals` restates `cert_sound` with the packed comparison written on natural-number
totals: `posOf`, `negOf`, `massOf` of the target's items and the weighted totals `posAll`,
`negAll`, `massAll` of the groups.  The kernel computes these totals in chunks
(`accRows` over a range of rows, `accTarget`), each checked against literal values
(`claimOK`); `accRows_claim` and `accTarget_claim` read such a check back, and `itemsRows_add`
with `posOf_append` reassembles the chunks.

The M6 gate: `meanThree_nonneg_of_checks`, `negMajority_nonneg_of_checks`,
`posMajority_nonneg_of_checks` — `checker = true → ∀ host, 0 ≤ eval target` for the three
targets on the proof path, with the checks as hypotheses (evaluated in M7).
-/

namespace EvenCycleApex

variable {d : ℕ}

/-- A claimed accumulator value. -/
def claimOK (P N M : ℕ) : ℕ → ℕ → ℕ → Bool := fun p q m => Nat.beq p P && Nat.beq q N && Nat.beq m M

lemma accList_claim {l : List (ℕ × ℤ)} {P N M : ℕ} (h : accList l 0 0 0 (claimOK P N M) = true) :
    posOf l = P ∧ negOf l = N ∧ massOf l = M := by
  rw [accList_eq] at h
  simp only [claimOK, zero_add, Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma GroupCert.accRows_claim {G : GroupCert} {a len P N M : ℕ}
    (h : G.accRows a len 0 0 0 (claimOK P N M) = true) :
    posOf (G.itemsRows a len) = P ∧ negOf (G.itemsRows a len) = N ∧
      massOf (G.itemsRows a len) = M := by
  rw [G.accRows_eq] at h
  exact accList_claim h

lemma accTarget_claim {P : GraphPoly} {Wt : List ℕ} {Pt Nt Mt : ℕ}
    (h : accTarget P Wt 0 0 0 (claimOK Pt Nt Mt) = true) :
    posOf (targetItems P Wt) = Pt ∧ negOf (targetItems P Wt) = Nt ∧
      massOf (targetItems P Wt) = Mt := by
  rw [accTarget_eq] at h
  exact accList_claim h

lemma posOf_append (l₁ l₂ : List (ℕ × ℤ)) : posOf (l₁ ++ l₂) = posOf l₁ + posOf l₂ := by
  simp [posOf]

lemma negOf_append (l₁ l₂ : List (ℕ × ℤ)) : negOf (l₁ ++ l₂) = negOf l₁ + negOf l₂ := by
  simp [negOf]

/-- Weighted totals of the groups. -/
def posAll (Gs : List GroupCert) : ℕ := (Gs.map fun G => G.S.weight * posOf G.items).sum
def negAll (Gs : List GroupCert) : ℕ := (Gs.map fun G => G.S.weight * negOf G.items).sum
def massAll (Gs : List GroupCert) : ℕ := (Gs.map fun G => G.S.weight * massOf G.items).sum

lemma packed_allItems : ∀ Gs : List GroupCert,
    packed (allItems Gs) = (posAll Gs : ℤ) - negAll Gs
  | [] => by simp [packed, allItems, posAll, negAll]
  | G :: Gs => by
    have ih := packed_allItems Gs
    rw [allItems, List.flatMap_cons, ← allItems] at *
    rw [packed, packed_append, ← packed, ← packed, ih, packed, scaleItems_packed]
    simp only [posAll, negAll, List.map_cons, List.sum_cons]
    push_cast
    ring

lemma massOf_allItems : ∀ Gs : List GroupCert, massOf (allItems Gs) = massAll Gs
  | [] => by simp [massOf, allItems, massAll]
  | G :: Gs => by
    rw [allItems, List.flatMap_cons, ← allItems, massOf_append, massOf_scaleItems,
      massOf_allItems Gs]
    simp [massAll]

/-- **Soundness, on natural-number totals.** -/
theorem cert_sound_of_totals {rep : ℕ → ℕ} {P : GraphPoly} {Wt : List ℕ} {scale : ℕ}
    (hscale : 0 < scale) {Gs : List GroupCert} (hG : ∀ G ∈ Gs, G.valid rep)
    (hWt : all2 (fun x w => witOK rep x.2 w) P Wt = true)
    (hsum : scale * posOf (targetItems P Wt) + negAll Gs = posAll Gs + scale * negOf (targetItems P Wt))
    (hmass : scale * massOf (targetItems P Wt) + massAll Gs < 2 ^ 128)
    (K : FiniteKernel d) : 0 ≤ evalPoly K P := by
  refine cert_sound hscale hG hWt ?_ ?_ K
  · rw [packed_allItems, packed, scaleItems_packed]
    have : ((scale * posOf (targetItems P Wt) + negAll Gs : ℕ) : ℤ)
        = ((posAll Gs + scale * negOf (targetItems P Wt) : ℕ) : ℤ) := by rw [hsum]
    push_cast at this
    linarith
  · rw [massOf_scaleItems, massOf_allItems]
    exact hmass

/-! ### Claimed totals

The kernel checks each accumulation against literal totals; `totalsOK` then compares the
weighted totals.  `cert_sound_of_claims` is the form used by the per-target checks. -/

/-- Componentwise sum of claimed totals. -/
def add3 (x y : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)

/-- The final comparison of the weighted totals (`scale · target` against `∑ weight · group`). -/
def totalsOK (scale : ℕ) (T : ℕ × ℕ × ℕ) (Cs : List (ℕ × (ℕ × ℕ × ℕ))) : Bool :=
  Nat.beq (scale * T.1 + (Cs.map fun c => c.1 * c.2.2.1).sum)
      ((Cs.map fun c => c.1 * c.2.1).sum + scale * T.2.1) &&
    Nat.blt (scale * T.2.2 + (Cs.map fun c => c.1 * c.2.2.2).sum) (2 ^ 128)

/-- A group has the claimed weight and totals. -/
def GroupCert.Totals (G : GroupCert) (c : ℕ × (ℕ × ℕ × ℕ)) : Prop :=
  c.1 = G.S.weight ∧ posOf G.items = c.2.1 ∧ negOf G.items = c.2.2.1 ∧ massOf G.items = c.2.2.2

lemma totals_all : ∀ {Gs : List GroupCert} {Cs : List (ℕ × (ℕ × ℕ × ℕ))},
    List.Forall₂ GroupCert.Totals Gs Cs →
      posAll Gs = (Cs.map fun c => c.1 * c.2.1).sum ∧
      negAll Gs = (Cs.map fun c => c.1 * c.2.2.1).sum ∧
      massAll Gs = (Cs.map fun c => c.1 * c.2.2.2).sum
  | [], [], _ => by simp [posAll, negAll, massAll]
  | G :: Gs, c :: Cs, List.Forall₂.cons ⟨hw, hp, hn, hm⟩ h => by
    obtain ⟨ih1, ih2, ih3⟩ := totals_all h
    simp only [posAll, negAll, massAll, List.map_cons, List.sum_cons] at ih1 ih2 ih3 ⊢
    rw [ih1, ih2, ih3, hw, hp, hn, hm]
    exact ⟨rfl, rfl, rfl⟩

lemma GroupCert.totals_of_claim {G : GroupCert} {c : ℕ × ℕ × ℕ}
    (h : G.accRows 0 G.S.feats.length 0 0 0 (claimOK c.1 c.2.1 c.2.2) = true) :
    G.Totals (G.S.weight, c) := by
  obtain ⟨hp, hn, hm⟩ := G.accRows_claim h
  exact ⟨rfl, hp, hn, hm⟩

lemma GroupCert.totals_of_claims3 {G : GroupCert} (hlen : G.S.feats.length = 15)
    {c₀ c₅ c₁₀ : ℕ × ℕ × ℕ}
    (h₀ : G.accRows 0 5 0 0 0 (claimOK c₀.1 c₀.2.1 c₀.2.2) = true)
    (h₅ : G.accRows 5 5 0 0 0 (claimOK c₅.1 c₅.2.1 c₅.2.2) = true)
    (h₁₀ : G.accRows 10 5 0 0 0 (claimOK c₁₀.1 c₁₀.2.1 c₁₀.2.2) = true) :
    G.Totals (G.S.weight, add3 (add3 c₀ c₅) c₁₀) := by
  have hitems : G.items = G.itemsRows 0 5 ++ G.itemsRows 5 5 ++ G.itemsRows 10 5 := by
    rw [GroupCert.items, hlen, show 15 = (5 + 5) + 5 from rfl, G.itemsRows_add, G.itemsRows_add]
  obtain ⟨p₀, n₀, m₀⟩ := G.accRows_claim h₀
  obtain ⟨p₅, n₅, m₅⟩ := G.accRows_claim h₅
  obtain ⟨p₁₀, n₁₀, m₁₀⟩ := G.accRows_claim h₁₀
  refine ⟨rfl, ?_, ?_, ?_⟩ <;>
    simp only [hitems, posOf_append, negOf_append, massOf_append, p₀, p₅, p₁₀, n₀, n₅, n₁₀, m₀, m₅,
      m₁₀, add3]

/-- **Soundness from kernel-checked claims.** -/
theorem cert_sound_of_claims {rep : ℕ → ℕ} {P : GraphPoly} {Wt : List ℕ} {scale : ℕ}
    (hscale : 0 < scale) {Gs : List GroupCert} (hG : ∀ G ∈ Gs, G.valid rep)
    (hWt : all2 (fun x w => witOK rep x.2 w) P Wt = true) {T : ℕ × ℕ × ℕ}
    (hT : accTarget P Wt 0 0 0 (claimOK T.1 T.2.1 T.2.2) = true)
    {Cs : List (ℕ × (ℕ × ℕ × ℕ))} (hC : List.Forall₂ GroupCert.Totals Gs Cs)
    (hfin : totalsOK scale T Cs = true) (K : FiniteKernel d) : 0 ≤ evalPoly K P := by
  obtain ⟨hp, hn, hm⟩ := accTarget_claim hT
  obtain ⟨hP, hN, hM⟩ := totals_all hC
  simp only [totalsOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hfin
  refine cert_sound_of_totals hscale hG hWt ?_ ?_ K
  · rw [hp, hn, hP, hN]
    exact hfin.1
  · rw [hm, hM]
    exact hfin.2

/-! ### Targets checked in chunks

A target with a few thousand monomials is checked in chunks of `C` monomials (kernel memory grows
with the number of relabelling checks in one declaration): `tchunk` checks the witnesses of one
chunk and its accumulated totals together; `target_chunks` reassembles the chunks. -/

/-- Chunk `k` (of size `C`) of a list. -/
def chunk {α : Type*} (C : ℕ) (P : List α) (k : ℕ) : List α := (P.drop (C * k)).take C

/-- The kernel check of one target chunk: its witnesses and its accumulated totals `c`. -/
def tchunk (rep : ℕ → ℕ) (C : ℕ) (P : GraphPoly) (k : ℕ) (W : List ℕ) (c : ℕ × ℕ × ℕ) : Bool :=
  all2 (fun x w => witOK rep x.2 w) (chunk C P k) W &&
    accTarget (chunk C P k) W 0 0 0 (claimOK c.1 c.2.1 c.2.2)

/-- Componentwise sum of a list of totals. -/
def sum3 (cs : List (ℕ × ℕ × ℕ)) : ℕ × ℕ × ℕ := cs.foldr add3 (0, 0, 0)

lemma all2_append {α β : Type*} {f : α → β → Bool} : ∀ {A : List α} {W₁ : List β} {B : List α}
    {W₂ : List β}, all2 f A W₁ = true → all2 f B W₂ = true → all2 f (A ++ B) (W₁ ++ W₂) = true
  | [], [], _, _, _, h => by simpa using h
  | a :: A, w :: W₁, B, W₂, h₁, h₂ => by
    simp only [all2, Bool.and_eq_true, List.cons_append] at h₁ ⊢
    exact ⟨h₁.1, all2_append h₁.2 h₂⟩
  | [], _ :: _, _, _, h, _ => by simp [all2] at h
  | _ :: _, [], _, _, h, _ => by simp [all2] at h

lemma targetItems_append {A B : GraphPoly} {W₁ W₂ : List ℕ} (h : A.length = W₁.length) :
    targetItems (A ++ B) (W₁ ++ W₂) = targetItems A W₁ ++ targetItems B W₂ := by
  simp [targetItems, List.zip_append h]

/-- **Reassembling a chunked target check.** -/
theorem target_chunks {rep : ℕ → ℕ} {C : ℕ} :
    ∀ (Ws : List (List ℕ)) (cs : List (ℕ × ℕ × ℕ)) (P : GraphPoly), Ws.length = cs.length →
      (∀ k < Ws.length, tchunk rep C P k (Ws.getD k []) (cs.getD k (0, 0, 0)) = true) →
      P.drop (C * Ws.length) = [] →
      all2 (fun x w => witOK rep x.2 w) P Ws.flatten = true ∧
        posOf (targetItems P Ws.flatten) = (sum3 cs).1 ∧
        negOf (targetItems P Ws.flatten) = (sum3 cs).2.1 ∧
        massOf (targetItems P Ws.flatten) = (sum3 cs).2.2
  | [], [], P, _, _, hP => by
    simp only [List.length_nil, mul_zero, List.drop_zero] at hP
    subst hP
    simp [all2, targetItems, posOf, negOf, massOf, sum3]
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | W :: Ws, c :: cs, P, hlen, hk, hP => by
    have hd : ∀ k, (P.drop C).drop (C * k) = P.drop (C * (k + 1)) := fun k => by
      rw [List.drop_drop]
      congr 1
      ring
    have h0 := hk 0 (by simp)
    simp only [tchunk, Bool.and_eq_true, chunk, mul_zero, List.drop_zero, List.getD_cons_zero] at h0
    have hrest : ∀ k < Ws.length,
        tchunk rep C (P.drop C) k (Ws.getD k []) (cs.getD k (0, 0, 0)) = true := by
      intro k hk'
      have := hk (k + 1) (by simp; omega)
      rw [List.getD_cons_succ, List.getD_cons_succ] at this
      rw [tchunk, chunk, hd]
      rwa [tchunk, chunk] at this
    have hP' : (P.drop C).drop (C * Ws.length) = [] := by
      rw [hd]
      simpa using hP
    obtain ⟨ha, hp, hn, hm⟩ := target_chunks Ws cs (P.drop C) (by simpa using hlen) hrest hP'
    obtain ⟨hlenW, _⟩ := all2_sound ((0 : ℤ), (0 : ℕ)) (0 : ℕ) h0.1
    obtain ⟨p₀, n₀, m₀⟩ := accTarget_claim h0.2
    have hsplit : P = P.take C ++ P.drop C := (List.take_append_drop C P).symm
    rw [List.flatten_cons, hsplit, targetItems_append hlenW, ← hsplit]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsplit]
      exact all2_append h0.1 ha
    · rw [posOf_append, p₀, hp]
      rfl
    · rw [negOf_append, n₀, hn]
      rfl
    · rw [massOf_append, m₀, hm]
      rfl

/-- **Soundness from kernel-checked claims, with the target checked in chunks.** -/
theorem cert_sound_of_chunks {rep : ℕ → ℕ} {P : GraphPoly} {scale : ℕ} (hscale : 0 < scale)
    {Gs : List GroupCert} (hG : ∀ G ∈ Gs, G.valid rep) {C : ℕ} {Ws : List (List ℕ)}
    {cs : List (ℕ × ℕ × ℕ)} (hlen : Ws.length = cs.length)
    (hk : ∀ k < Ws.length, tchunk rep C P k (Ws.getD k []) (cs.getD k (0, 0, 0)) = true)
    (hP : P.drop (C * Ws.length) = []) {Cs : List (ℕ × (ℕ × ℕ × ℕ))}
    (hC : List.Forall₂ GroupCert.Totals Gs Cs) (hfin : totalsOK scale (sum3 cs) Cs = true)
    (K : FiniteKernel d) : 0 ≤ evalPoly K P := by
  obtain ⟨hWt, hp, hn, hm⟩ := target_chunks Ws cs P hlen hk hP
  obtain ⟨hPa, hNa, hMa⟩ := totals_all hC
  simp only [totalsOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hfin
  refine cert_sound_of_totals hscale hG hWt ?_ ?_ K
  · rw [hp, hn, hPa, hNa]
    exact hfin.1
  · rw [hm, hMa]
    exact hfin.2

/-! ### The M6 gate: soundness for the three targets on the proof path -/

/-- `checker = true → ∀ host, 0 ≤ eval(P_mean,3)`. -/
theorem meanThree_nonneg_of_checks {rep : ℕ → ℕ} {Wt : List ℕ} {scale : ℕ} (hscale : 0 < scale)
    {Gs : List GroupCert} (hG : ∀ G ∈ Gs, G.valid rep)
    (hWt : all2 (fun x w => witOK rep x.2 w) targetMeanThree Wt = true)
    (hsum : scale * posOf (targetItems targetMeanThree Wt) + negAll Gs
      = posAll Gs + scale * negOf (targetItems targetMeanThree Wt))
    (hmass : scale * massOf (targetItems targetMeanThree Wt) + massAll Gs < 2 ^ 128)
    (K : FiniteKernel d) : 0 ≤ evalPoly K targetMeanThree :=
  cert_sound_of_totals hscale hG hWt hsum hmass K

/-- `checker = true → ∀ host, 0 ≤ eval(P₋)`. -/
theorem negMajority_nonneg_of_checks {rep : ℕ → ℕ} {Wt : List ℕ} {scale : ℕ} (hscale : 0 < scale)
    {Gs : List GroupCert} (hG : ∀ G ∈ Gs, G.valid rep)
    (hWt : all2 (fun x w => witOK rep x.2 w) targetNeg Wt = true)
    (hsum : scale * posOf (targetItems targetNeg Wt) + negAll Gs
      = posAll Gs + scale * negOf (targetItems targetNeg Wt))
    (hmass : scale * massOf (targetItems targetNeg Wt) + massAll Gs < 2 ^ 128)
    (K : FiniteKernel d) : 0 ≤ evalPoly K targetNeg :=
  cert_sound_of_totals hscale hG hWt hsum hmass K

/-- `checker = true → ∀ host, 0 ≤ eval(P₊)`. -/
theorem posMajority_nonneg_of_checks {rep : ℕ → ℕ} {Wt : List ℕ} {scale : ℕ} (hscale : 0 < scale)
    {Gs : List GroupCert} (hG : ∀ G ∈ Gs, G.valid rep)
    (hWt : all2 (fun x w => witOK rep x.2 w) targetPos Wt = true)
    (hsum : scale * posOf (targetItems targetPos Wt) + negAll Gs
      = posAll Gs + scale * negOf (targetItems targetPos Wt))
    (hmass : scale * massOf (targetItems targetPos Wt) + massAll Gs < 2 ^ 128)
    (K : FiniteKernel d) : 0 ≤ evalPoly K targetPos :=
  cert_sound_of_totals hscale hG hWt hsum hmass K

end EvenCycleApex
