import ApicesCommonness.Common.Graph.HomDensity

/-!
# Relabelling invariance of homomorphism densities

Blueprint `lem:density-algebra`, relabelling part: for a permutation `e` of the vertices and a
symmetric kernel `L`, `t(F.comap e, L) = t(F, L)` (`homDensity_comap_equiv`).  The proof changes
variables by `MeasurableEquiv.piCongrLeft` (measure preserving for `μ^{⊗v}`) and reindexes the edge
product by `p ↦ sortPair (e p.1) (e p.2)`.

The other parts of `lem:density-algebra` — isolated vertices and disjoint unions — are consumed only
on finite hosts, where they are finite-sum identities; they are proved there (plan D2, `Host/`).
-/

open MeasureTheory Finset

namespace ApicesCommonness

/-- An unordered pair of vertices written with the smaller one first. -/
def sortPair {v : ℕ} (a b : Fin v) : Fin v × Fin v := if a < b then (a, b) else (b, a)

lemma sortPair_of_lt {v : ℕ} {a b : Fin v} (h : a < b) : sortPair a b = (a, b) := if_pos h

lemma sortPair_of_gt {v : ℕ} {a b : Fin v} (h : b < a) : sortPair a b = (b, a) :=
  if_neg (not_lt.mpr h.le)

lemma sortPair_comm {v : ℕ} {a b : Fin v} (h : a ≠ b) : sortPair a b = sortPair b a := by
  rcases lt_or_gt_of_ne h with hab | hab
  · rw [sortPair_of_lt hab, sortPair_of_gt hab]
  · rw [sortPair_of_gt hab, sortPair_of_lt hab]

/-- `sortPair a b` is an edge of `F` whenever `a ~ b`. -/
lemma sortPair_mem_edgePairs {v : ℕ} {F : SimpleGraph (Fin v)} [DecidableRel F.Adj] {a b : Fin v}
    (h : F.Adj a b) : sortPair a b ∈ edgePairs F := by
  rcases lt_or_gt_of_ne (F.ne_of_adj h) with hab | hab
  · rw [sortPair_of_lt hab]; exact mem_edgePairs.mpr ⟨hab, h⟩
  · rw [sortPair_of_gt hab]; exact mem_edgePairs.mpr ⟨hab, h.symm⟩

/-- `sortPair a b` represents the unordered pair `{a, b}`. -/
lemma sym2_sortPair_eq {v : ℕ} (a b : Fin v) : s((sortPair a b).1, (sortPair a b).2) = s(a, b) := by
  unfold sortPair
  split_ifs
  · rfl
  · exact Sym2.eq_swap

/-- A symmetric function of an unordered pair does not see the order. -/
lemma apply_sortPair {v : ℕ} {β : Type*} (g : Fin v → Fin v → β) (hg : ∀ a b, g a b = g b a)
    (a b : Fin v) : g (sortPair a b).1 (sortPair a b).2 = g a b := by
  unfold sortPair
  split_ifs
  · rfl
  · exact hg b a

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Relabelling.**  For a permutation `e` of `Fin v` and a symmetric kernel,
`t(F.comap e, L) = t(F, L)`. -/
theorem homDensity_comap_equiv {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (e : Fin v ≃ Fin v) {L : Ω → Ω → ℝ} (hsymm : ∀ x y, L x y = L y x) :
    homDensity (F.comap e) L μ = homDensity F L μ := by
  set Φ := MeasurableEquiv.piCongrLeft (fun _ : Fin v => Ω) e with hΦdef
  have hΦ : MeasurePreserving Φ (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
    measurePreserving_piCongrLeft (fun _ => μ) e
  have hΦx : ∀ (x : Fin v → Ω) (a : Fin v), Φ x (e a) = x a :=
    fun x a => MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin v => Ω) e x a
  rw [homDensity_eq_integral_edgeProd, homDensity_eq_integral_edgeProd F,
    ← hΦ.integral_comp Φ.measurableEmbedding (edgeProd F L)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  unfold edgeProd
  refine prod_nbij' (fun p => sortPair (e p.1) (e p.2)) (fun q => sortPair (e.symm q.1) (e.symm q.2))
    (fun p hp => ?_) (fun q hq => ?_) (fun p hp => ?_) (fun q hq => ?_) (fun p hp => ?_)
  · rw [mem_edgePairs] at hp
    exact sortPair_mem_edgePairs (F := F) hp.2
  · rw [mem_edgePairs] at hq
    refine sortPair_mem_edgePairs (F := F.comap e) ?_
    simpa [SimpleGraph.comap_adj] using hq.2
  · rw [mem_edgePairs] at hp
    have hne : e p.1 ≠ e p.2 := e.injective.ne hp.1.ne
    rcases lt_or_gt_of_ne hne with h | h
    · simp only [sortPair_of_lt h, Equiv.symm_apply_apply, sortPair_of_lt hp.1]
    · simp only [sortPair_of_gt h, Equiv.symm_apply_apply, sortPair_of_gt hp.1]
  · rw [mem_edgePairs] at hq
    have hne : e.symm q.1 ≠ e.symm q.2 := e.symm.injective.ne hq.1.ne
    rcases lt_or_gt_of_ne hne with h | h
    · simp only [sortPair_of_lt h, Equiv.apply_symm_apply, sortPair_of_lt hq.1]
    · simp only [sortPair_of_gt h, Equiv.apply_symm_apply, sortPair_of_gt hq.1]
  · rw [apply_sortPair (fun a b => L (Φ x a) (Φ x b)) (fun a b => hsymm _ _), hΦx, hΦx]

end ApicesCommonness
