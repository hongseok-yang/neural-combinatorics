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
