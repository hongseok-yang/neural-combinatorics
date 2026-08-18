import Taeyoung.Foundation.GraphMap
import Taeyoung.Foundation.ChromaticPolynomial
import Taeyoung.Foundation.Status

/-!
# Disjoint unions: multiplicativity of the homomorphism density

`t(H₁ ⊔ H₂, W) = t(H₁,W)·t(H₂,W)`.  The graph side is the same `SimpleGraph.map`
machinery the cone uses — `H₁` carried along `Fin.castAdd` and `H₂` along
`Fin.natAdd` — so `graphWeight_map` already factors the weight.  What is new is
the measure side: the assignment measure on `Fin (m+n)` has to be split as a
product, which Mathlib supplies in two pieces,
`measurePreserving_piCongrLeft` along `finSumFinEquiv` and
`measurePreserving_sumPiEquivProdPi`.

This is needed by the component-multiplicativity row and by the cone
methodologies whose base is itself a disjoint union.
-/

open MeasureTheory Finset

namespace Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {m n : ℕ}

/-! ### Splitting the assignment measure -/

/-- Splitting an assignment on `Fin (m+n)` into its two blocks, as a measurable
equivalence. -/
def assignmentSplit (Ω : Type*) [MeasurableSpace Ω] (m n : ℕ) :
    (Fin (m + n) → Ω) ≃ᵐ ((Fin m → Ω) × (Fin n → Ω)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) ↦ Ω) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ Ω))

@[simp] lemma assignmentSplit_apply (m n : ℕ) (z : Fin (m + n) → Ω) :
    assignmentSplit Ω m n z =
      (fun i : Fin m ↦ z (Fin.castAdd n i), fun j : Fin n ↦ z (Fin.natAdd m j)) := by
  have hpi : ∀ (w : Fin (m + n) → Ω) (s : Fin m ⊕ Fin n),
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) ↦ Ω) finSumFinEquiv).symm w s =
        w (finSumFinEquiv s) := fun w s ↦ rfl
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp [assignmentSplit, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
      hpi]

/-- **Splitting an assignment into its two blocks is measure preserving.** -/
lemma measurePreserving_assignmentSplit (m n : ℕ) :
    MeasurePreserving (assignmentSplit Ω m n)
      (assignmentMeasure (Fin (m + n)) μ)
      ((assignmentMeasure (Fin m) μ).prod (assignmentMeasure (Fin n) μ)) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) ↦ Ω) finSumFinEquiv)
      (Measure.pi fun _ : Fin m ⊕ Fin n ↦ μ)
      (Measure.pi fun _ : Fin (m + n) ↦ μ) :=
    measurePreserving_piCongrLeft (fun _ : Fin (m + n) ↦ μ) finSumFinEquiv
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ μ)
  simpa [assignmentMeasure, assignmentSplit, MeasurableEquiv.coe_trans] using
    h2.comp (MeasurePreserving.symm _ h1)

/-! ### The disjoint union -/

/-- `H₁ ⊔ H₂` on `Fin (m + n)`: `H₁` on the first block, `H₂` on the second. -/
def disjointUnion (H₁ : SimpleGraph (Fin m)) (H₂ : SimpleGraph (Fin n)) :
    SimpleGraph (Fin (m + n)) :=
  H₁.map (Fin.castAdd n) ⊔ H₂.map (Fin.natAdd m)

instance disjointUnion_decidableAdj (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj] :
    DecidableRel (disjointUnion H₁ H₂).Adj := by
  unfold disjointUnion
  infer_instance

lemma disjoint_blocks (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj] :
    Disjoint (H₁.edgeFinset.image (Sym2.map (Fin.castAdd n)))
      (H₂.edgeFinset.image (Sym2.map (Fin.natAdd m))) := by
  rw [Finset.disjoint_left]
  rintro e he he'
  rw [Finset.mem_image] at he he'
  obtain ⟨e₁, -, rfl⟩ := he
  obtain ⟨e₂, -, he'⟩ := he'
  revert he'
  induction e₁ using Sym2.inductionOn with
  | _ a b =>
    induction e₂ using Sym2.inductionOn with
    | _ c d =>
      intro heq
      rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at heq
      have hval : ∀ (i : Fin m) (j : Fin n),
          (Fin.castAdd n i : Fin (m + n)) ≠ (Fin.natAdd m j : Fin (m + n)) := by
        intro i j hij
        have hv := congrArg Fin.val hij
        have hi := i.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      rcases heq with ⟨h, -⟩ | ⟨h, -⟩
      · exact hval a c h.symm
      · exact hval b c h.symm

omit [IsProbabilityMeasure μ] in
/-- **The weight of a disjoint union factors.** -/
theorem graphWeight_disjointUnion (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj] (W : Graphon Ω μ)
    (z : Fin (m + n) → Ω) :
    graphWeight (disjointUnion H₁ H₂) W z =
      graphWeight H₁ W (fun i ↦ z (Fin.castAdd n i)) *
        graphWeight H₂ W (fun j ↦ z (Fin.natAdd m j)) := by
  have hsup : (disjointUnion H₁ H₂).edgeFinset =
      (H₁.map (Fin.castAdd n)).edgeFinset ∪ (H₂.map (Fin.natAdd m)).edgeFinset := by
    simpa [disjointUnion] using
      SimpleGraph.edgeFinset_sup (G₁ := H₁.map (Fin.castAdd n))
        (G₂ := H₂.map (Fin.natAdd m))
  rw [graphWeight, hsup, edgeFinset_map_eq_image H₁ (Fin.castAdd_injective m n),
    edgeFinset_map_eq_image H₂ (Fin.natAdd_injective n m),
    Finset.prod_union (disjoint_blocks H₁ H₂)]
  congr 1
  · rw [Finset.prod_image
      fun e _ e' _ h ↦ sym2_map_injective (Fin.castAdd_injective m n) h, graphWeight]
    exact Finset.prod_congr rfl fun e _ ↦ edgeValue_sym2_map W z _ e
  · rw [Finset.prod_image
      fun e _ e' _ h ↦ sym2_map_injective (Fin.natAdd_injective n m) h, graphWeight]
    exact Finset.prod_congr rfl fun e _ ↦ edgeValue_sym2_map W z _ e

/-- **Multiplicativity of the homomorphism density over a disjoint union.** -/
theorem homDensity_disjointUnion (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj] (W : Graphon Ω μ) :
    homDensity (disjointUnion H₁ H₂) W = homDensity H₁ W * homDensity H₂ W := by
  have hmp := measurePreserving_assignmentSplit (μ := μ) m n
  have hsplit := hmp.integral_comp'
    (g := fun q : (Fin m → Ω) × (Fin n → Ω) ↦
      graphWeight H₁ W q.1 * graphWeight H₂ W q.2)
  simp only [assignmentSplit_apply] at hsplit
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_disjointUnion H₁ H₂ W)),
    hsplit, integral_prod_mul]
  rfl

/-! ### The chromatic side -/

/-- The block splitting, as a plain equivalence. -/
def splitEquiv (α : Type*) (m n : ℕ) :
    (Fin (m + n) → α) ≃ ((Fin m → α) × (Fin n → α)) :=
  (Equiv.piCongrLeft (fun _ : Fin (m + n) ↦ α) finSumFinEquiv).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ α))

@[simp] lemma splitEquiv_apply {α : Type*} (m n : ℕ) (z : Fin (m + n) → α) :
    splitEquiv α m n z =
      (fun i : Fin m ↦ z (Fin.castAdd n i), fun j : Fin n ↦ z (Fin.natAdd m j)) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [splitEquiv, Equiv.sumPiEquivProdPi]

/-- Splitting a subtype of a product. -/
def subtypeProdSplit {A B : Type*} (p : A → Prop) (q : B → Prop) :
    {z : A × B // p z.1 ∧ q z.2} ≃ ({a // p a} × {b // q b}) where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun w := ⟨(w.1.1, w.2.1), ⟨w.1.2, w.2.2⟩⟩
  left_inv := by rintro ⟨⟨a, b⟩, ⟨ha, hb⟩⟩; rfl
  right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl

lemma isProperAssignment_disjointUnion (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj] {k : ℕ} (x : Fin (m + n) → Fin k) :
    IsProperAssignment (disjointUnion H₁ H₂) x ↔
      IsProperAssignment H₁ (fun i ↦ x (Fin.castAdd n i)) ∧
        IsProperAssignment H₂ (fun j ↦ x (Fin.natAdd m j)) := by
  constructor
  · intro h
    refine ⟨fun a b hab ↦ h ?_, fun a b hab ↦ h ?_⟩
    · exact Or.inl ⟨fun he ↦ hab.ne (Fin.castAdd_injective m n he), a, b, hab, rfl, rfl⟩
    · exact Or.inr ⟨fun he ↦ hab.ne (Fin.natAdd_injective n m he), a, b, hab, rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩ u v huv
    rcases huv with ⟨-, a, b, hab, rfl, rfl⟩ | ⟨-, a, b, hab, rfl, rfl⟩
    · exact h₁ hab
    · exact h₂ hab

/-- **The proper-assignment count is multiplicative over a disjoint union.** -/
theorem properAssignmentCount_disjointUnion (H₁ : SimpleGraph (Fin m))
    [DecidableRel H₁.Adj] (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj] (k : ℕ) :
    properAssignmentCount (disjointUnion H₁ H₂) k =
      properAssignmentCount H₁ k * properAssignmentCount H₂ k := by
  classical
  have hcard : ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj],
      properAssignmentCount H k = Fintype.card {x : V → Fin k // IsProperAssignment H x} := by
    intro V _ _ H _
    rw [properAssignmentCount, Fintype.card_subtype]
  rw [hcard, hcard, hcard, ← Fintype.card_prod]
  refine Fintype.card_congr ?_
  refine (Equiv.subtypeEquiv (splitEquiv (Fin k) m n) ?_).trans
    (subtypeProdSplit _ _)
  intro x
  simpa using isProperAssignment_disjointUnion H₁ H₂ x

open Polynomial in
/-- **The chromatic polynomial factors over a disjoint union.** -/
theorem isChromaticPolynomial_disjointUnion {P₁ P₂ : Polynomial ℝ}
    (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj]
    (h₁ : IsChromaticPolynomial H₁ P₁) (h₂ : IsChromaticPolynomial H₂ P₂) :
    IsChromaticPolynomial (disjointUnion H₁ H₂) (P₁ * P₂) := by
  intro k
  rw [eval_mul, h₁ k, h₂ k, properAssignmentCount_disjointUnion, Nat.cast_mul]

/-- More colours never lose proper assignments. -/
lemma properAssignmentCount_pos_of_le {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {r k : ℕ} (hrk : r ≤ k)
    (hr : 0 < properAssignmentCount H r) : 0 < properAssignmentCount H k := by
  classical
  rw [properAssignmentCount, Finset.card_pos] at hr ⊢
  obtain ⟨x, hx⟩ := hr
  rw [Finset.mem_filter] at hx
  refine ⟨fun v ↦ Fin.castLE hrk (x v), ?_⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun u v huv he ↦
    hx.2 huv (Fin.castLE_injective hrk he)⟩

/-- **The chromatic number of a disjoint union is the larger of the two.** -/
theorem isChromaticNumber_disjointUnion {r₁ r₂ : ℕ}
    (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj]
    (h₁ : IsChromaticNumber H₁ r₁) (h₂ : IsChromaticNumber H₂ r₂) :
    IsChromaticNumber (disjointUnion H₁ H₂) (max r₁ r₂) where
  positive := by
    rw [properAssignmentCount_disjointUnion]
    exact Nat.mul_pos
      (properAssignmentCount_pos_of_le H₁ (le_max_left r₁ r₂) h₁.positive)
      (properAssignmentCount_pos_of_le H₂ (le_max_right r₁ r₂) h₂.positive)
  zero_below k hk := by
    rw [properAssignmentCount_disjointUnion]
    rcases lt_or_ge k r₁ with h | h
    · rw [h₁.zero_below k h, Nat.zero_mul]
    · have hk2 : k < r₂ := by omega
      rw [h₂.zero_below k hk2, Nat.mul_zero]

/-! ### The catalogue proposition -/

open Polynomial in
/-- The catalogue target factors over a disjoint union. -/
theorem chromaticTarget_mul (m n : ℕ) (P₁ P₂ : Polynomial ℝ) (p : ℝ) :
    chromaticTarget (V := Fin (m + n)) (P₁ * P₂) p =
      chromaticTarget (V := Fin m) P₁ p * chromaticTarget (V := Fin n) P₂ p := by
  by_cases hp : p = 1
  · simp [hp]
  · rw [chromaticTarget_of_ne_one _ hp, chromaticTarget_of_ne_one _ hp,
      chromaticTarget_of_ne_one _ hp]
    simp only [Fintype.card_fin, eval_mul, pow_add]
    ring

open Polynomial in
/-- **The catalogue proposition is multiplicative over a disjoint union.**  Each
side supplies its chromatic data together with a nonnegative bound valid on the
*union's* admissible interval. -/
theorem satisfiesLowerBound_disjointUnion {P₁ P₂ : Polynomial ℝ} {r₁ r₂ : ℕ}
    (H₁ : SimpleGraph (Fin m)) [DecidableRel H₁.Adj]
    (H₂ : SimpleGraph (Fin n)) [DecidableRel H₂.Adj]
    (hc₁ : IsChromaticPolynomial H₁ P₁) (hn₁ : IsChromaticNumber H₁ r₁)
    (hc₂ : IsChromaticPolynomial H₂ P₂) (hn₂ : IsChromaticNumber H₂ r₂)
    (hb₁ : ∀ {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
      (W : Graphon Ω ν), admissibleDensity (max r₁ r₂) (edgeDensity W) →
      0 ≤ chromaticTarget (V := Fin m) P₁ (edgeDensity W) ∧
        chromaticTarget (V := Fin m) P₁ (edgeDensity W) ≤ homDensity H₁ W)
    (hb₂ : ∀ {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
      (W : Graphon Ω ν), admissibleDensity (max r₁ r₂) (edgeDensity W) →
      0 ≤ chromaticTarget (V := Fin n) P₂ (edgeDensity W) ∧
        chromaticTarget (V := Fin n) P₂ (edgeDensity W) ≤ homDensity H₂ W) :
    SatisfiesLowerBound (disjointUnion H₁ H₂) := by
  intro P r hP hr Ω instM ν instP W hadm
  have hPeq : P = P₁ * P₂ :=
    IsChromaticPolynomial.unique (H := disjointUnion H₁ H₂) hP
      (isChromaticPolynomial_disjointUnion H₁ H₂ hc₁ hc₂)
  have hreq : r = max r₁ r₂ :=
    IsChromaticNumber.unique (H := disjointUnion H₁ H₂) hr
      (isChromaticNumber_disjointUnion H₁ H₂ hn₁ hn₂)
  subst hPeq
  subst hreq
  obtain ⟨hnn₁, hle₁⟩ := hb₁ W hadm
  obtain ⟨hnn₂, hle₂⟩ := hb₂ W hadm
  rw [chromaticTarget_mul, homDensity_disjointUnion]
  exact mul_le_mul hle₁ hle₂ hnn₂ (homDensity_nonneg H₁ W)

end Taeyoung
