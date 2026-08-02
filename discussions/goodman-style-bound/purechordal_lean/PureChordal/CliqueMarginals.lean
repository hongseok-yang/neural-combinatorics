import PureChordal.CliqueTreeCombinatorics
import PureChordal.Relabeling
import PureChordal.MarginalAlgebra
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
# Marginals of equal-size clique laws

This file supplies the finite-coordinate relabelings needed by the
junction-tree density.
-/

namespace PureChordal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def finsetDiffEquiv
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) :
    ↥(A \ S) ≃ ↥(B \ S) :=
  Fintype.equivOfCardEq <| by
    simp only [Fintype.card_coe]
    rw [Finset.card_sdiff, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hSA, Finset.inter_eq_left.mpr hSB,
      hcard]

noncomputable def splitFinsetEquiv
    {S A : Finset V} (hSA : S ⊆ A) :
    ↥A ≃ ↥S ⊕ ↥(A \ S) where
  toFun a :=
    if ha : a.1 ∈ S then Sum.inl ⟨a.1, ha⟩
    else Sum.inr ⟨a.1, Finset.mem_sdiff.mpr ⟨a.2, ha⟩⟩
  invFun z := match z with
    | Sum.inl a => ⟨a.1, hSA a.2⟩
    | Sum.inr a => ⟨a.1, (Finset.mem_sdiff.mp a.2).1⟩
  left_inv a := by
    dsimp
    by_cases ha : a.1 ∈ S <;> simp [ha]
  right_inv z := by
    dsimp
    rcases z with a | a
    · simp [a.2]
    · simp [(Finset.mem_sdiff.mp a.2).2]

noncomputable def finsetEquivFixing
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) :
    ↥A ≃ ↥B :=
  (splitFinsetEquiv hSA).trans <|
    (Equiv.sumCongr (Equiv.refl ↥S)
      (finsetDiffEquiv hSA hSB hcard)).trans
        (splitFinsetEquiv hSB).symm

/-- Extend the equivalence between `A` and `B` to a permutation of the ambient
finite vertex type. -/
noncomputable def finsetPermFixing
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) :
    Equiv.Perm V :=
  (finsetEquivFixing hSA hSB hcard).extendSubtype

lemma splitFinsetEquiv_apply_of_mem
    {S A : Finset V} (hSA : S ⊆ A) (a : ↥A) (ha : a.1 ∈ S) :
    splitFinsetEquiv hSA a = Sum.inl ⟨a.1, ha⟩ := by
  classical
  simp [splitFinsetEquiv, ha]

@[simp] lemma finsetEquivFixing_apply_val_of_mem
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) (a : ↥A) (ha : a.1 ∈ S) :
    (finsetEquivFixing hSA hSB hcard a).1 = a.1 := by
  classical
  rw [finsetEquivFixing, Equiv.trans_apply, Equiv.trans_apply,
    splitFinsetEquiv_apply_of_mem hSA a ha]
  simp [splitFinsetEquiv]

@[simp] lemma finsetPermFixing_apply_of_mem
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) {v : V} (hv : v ∈ S) :
    finsetPermFixing hSA hSB hcard v = v := by
  classical
  rw [finsetPermFixing,
    Equiv.extendSubtype_apply_of_mem _ v (hSA hv)]
  exact finsetEquivFixing_apply_val_of_mem hSA hSB hcard
    ⟨v, hSA hv⟩ hv

lemma finsetPermFixing_map_left
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) :
    A.map (finsetPermFixing hSA hSB hcard).toEmbedding = B := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact Equiv.extendSubtype_mem
      (finsetEquivFixing hSA hSB hcard) a ha
  · simp [hcard]

lemma finsetPermFixing_map_common
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) :
    S.map (finsetPermFixing hSA hSB hcard).toEmbedding = S := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    change finsetPermFixing hSA hSB hcard u ∈ S
    rw [finsetPermFixing_apply_of_mem hSA hSB hcard hu]
    exact hu
  · intro hv
    refine Finset.mem_map.mpr ⟨v, hv, ?_⟩
    exact finsetPermFixing_apply_of_mem hSA hSB hcard hv

lemma finsetPermFixing_map_compl
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) :
    (Finset.univ \ S).map
        (finsetPermFixing hSA hSB hcard).toEmbedding =
      Finset.univ \ S := by
  classical
  rw [Finset.map_sdiff,
    Finset.map_univ_equiv (finsetPermFixing hSA hSB hcard),
    finsetPermFixing_map_common hSA hSB hcard]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem cliqueWeightOn_eq_graphWeight
    (A : Finset V) (W : Graphon Ω μ) (x : V → Ω) :
    PureCliqueTreeDecomp.cliqueWeightOn A W x =
      graphWeight (⊤ : SimpleGraph ↥A) W (fun a => x a.1) := by
  classical
  unfold PureCliqueTreeDecomp.cliqueWeightOn graphWeight
  symm
  apply Finset.prod_bij
      (fun e _ => e.map (fun a : ↥A => a.1))
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        change s(u.1, v.1) ∈ pairsIn A
        rw [mk_mem_pairsIn]
        have huv : u ≠ v := by
          simpa [SimpleGraph.mem_edgeFinset] using he
        exact ⟨fun h => huv (Subtype.ext h), u.2, v.2⟩
  · intro e₁ h₁ e₂ h₂ h
    exact Sym2.map.injective Subtype.val_injective h
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        rw [mk_mem_pairsIn] at he
        refine ⟨s(⟨u, he.2.1⟩, ⟨v, he.2.2⟩), ?_, ?_⟩
        · simpa [SimpleGraph.mem_edgeFinset] using he.1
        · simp
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v => simp [edgeValue, Sym2.lift_mk]

lemma cliqueWeightOn_comp_finsetPermFixing
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) (W : Graphon Ω μ) (x : V → Ω) :
    PureCliqueTreeDecomp.cliqueWeightOn A W
        (fun v => x (finsetPermFixing hSA hSB hcard v)) =
      PureCliqueTreeDecomp.cliqueWeightOn B W x := by
  classical
  let φ := finsetEquivFixing hSA hSB hcard
  let σ := finsetPermFixing hSA hSB hcard
  calc
    PureCliqueTreeDecomp.cliqueWeightOn A W (fun v => x (σ v)) =
        graphWeight (⊤ : SimpleGraph ↥A) W
          (fun a => x (σ a.1)) :=
      cliqueWeightOn_eq_graphWeight A W (fun v => x (σ v))
    _ = graphWeight (⊤ : SimpleGraph ↥A) W
          (fun a => x ((φ a).1)) := by
      congr 1
      funext a
      congr 1
      exact Equiv.extendSubtype_apply_of_mem φ a.1 a.2
    _ = graphWeight (⊤ : SimpleGraph ↥B) W
          (fun b => x b.1) := by
      exact graphWeight_iso W
        (SimpleGraph.Iso.completeGraph φ) (fun b => x b.1)
    _ = PureCliqueTreeDecomp.cliqueWeightOn B W x :=
      (cliqueWeightOn_eq_graphWeight B W x).symm

lemma measurable_cliqueWeightOn
    (A : Finset V) (W : Graphon Ω μ) :
    Measurable (PureCliqueTreeDecomp.cliqueWeightOn A W) := by
  unfold PureCliqueTreeDecomp.cliqueWeightOn
  exact Finset.measurable_fun_prod _ fun e _ =>
    measurable_edgeValue W e

/-- The clique weight as a nonnegative extended-real-valued function, suitable
for `lmarginal` and Tonelli. -/
noncomputable def cliqueWeightOnENN
    (A : Finset V) (W : Graphon Ω μ) (x : V → Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (PureCliqueTreeDecomp.cliqueWeightOn A W x)

lemma measurable_cliqueWeightOnENN
    (A : Finset V) (W : Graphon Ω μ) :
    Measurable (cliqueWeightOnENN A W) :=
  (measurable_cliqueWeightOn A W).ennreal_ofReal

lemma cliqueWeightOnENN_comp_finsetPermFixing
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) (W : Graphon Ω μ) (x : V → Ω) :
    cliqueWeightOnENN A W
        (fun v => x (finsetPermFixing hSA hSB hcard v)) =
      cliqueWeightOnENN B W x := by
  simp only [cliqueWeightOnENN,
    cliqueWeightOn_comp_finsetPermFixing hSA hSB hcard W x]

lemma cliqueWeightOn_congr_on
    (A : Finset V) (W : Graphon Ω μ) {x y : V → Ω}
    (hxy : ∀ v ∈ A, x v = y v) :
    PureCliqueTreeDecomp.cliqueWeightOn A W x =
      PureCliqueTreeDecomp.cliqueWeightOn A W y := by
  classical
  unfold PureCliqueTreeDecomp.cliqueWeightOn
  apply Finset.prod_congr rfl
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ u v =>
      rw [edgeValue_mk, edgeValue_mk]
      have huv := (mk_mem_pairsIn.mp hedge).2
      rw [hxy u huv.1, hxy v huv.2]

lemma cliqueWeightOnENN_congr_on
    (A : Finset V) (W : Graphon Ω μ) {x y : V → Ω}
    (hxy : ∀ v ∈ A, x v = y v) :
    cliqueWeightOnENN A W x = cliqueWeightOnENN A W y := by
  rw [cliqueWeightOnENN, cliqueWeightOnENN,
    cliqueWeightOn_congr_on A W hxy]

lemma lmarginal_cliqueWeightOnENN_eq_self_of_disjoint
    (A T : Finset V) (W : Graphon Ω μ) (hTA : Disjoint T A) :
    lmarginal (fun _ : V => μ) T (cliqueWeightOnENN A W) =
      cliqueWeightOnENN A W := by
  have hdep : FinsetDependsOn A (cliqueWeightOnENN A W) := by
    intro x y hxy
    exact cliqueWeightOnENN_congr_on A W hxy
  exact hdep.lmarginal_eq_self_of_disjoint hTA

lemma lmarginal_cliqueWeightOnENN_compl_eq_diff
    {S A : Finset V} (hSA : S ⊆ A) (W : Graphon Ω μ) :
    lmarginal (fun _ : V => μ) (Finset.univ \ S)
        (cliqueWeightOnENN A W) =
      lmarginal (fun _ : V => μ) (A \ S)
        (cliqueWeightOnENN A W) := by
  rw [lmarginal_compl_subset hSA (measurable_cliqueWeightOnENN A W),
    lmarginal_cliqueWeightOnENN_eq_self_of_disjoint A (Finset.univ \ A) W
      ((Finset.disjoint_sdiff (s := A) (t := Finset.univ)).symm)]

/-- Purity at the analytic level: two equal-size complete-graph weights have
the same marginal on any common vertex subset.  All ambient coordinates outside
the common subset are integrated out. -/
theorem cliqueWeightOnENN_separatorMarginal_eq
    {S A B : Finset V} (hSA : S ⊆ A) (hSB : S ⊆ B)
    (hcard : A.card = B.card) (W : Graphon Ω μ) :
    lmarginal (fun _ : V => μ) (Finset.univ \ S)
        (cliqueWeightOnENN A W) =
      lmarginal (fun _ : V => μ) (Finset.univ \ S)
        (cliqueWeightOnENN B W) := by
  classical
  funext x
  let σ := finsetPermFixing hSA hSB hcard
  let T : Finset V := Finset.univ \ S
  have hT : T.map σ.toEmbedding = T := by
    exact finsetPermFixing_map_compl hSA hSB hcard
  have hTimage : T.image σ = T := by
    ext v
    constructor
    · intro hv
      obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
      have hvmap : v ∈ T.map σ.toEmbedding := by
        refine Finset.mem_map.mpr ⟨a, ha, ?_⟩
        change σ a = v
        exact hav
      rwa [hT] at hvmap
    · intro hv
      have hvmap : v ∈ T.map σ.toEmbedding := by
        rwa [hT]
      obtain ⟨a, ha, hav⟩ := Finset.mem_map.mp hvmap
      refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
      change σ a = v at hav
      exact hav
  have hx :
      lmarginal (fun _ : V => μ) T (cliqueWeightOnENN A W)
          (fun v => x (σ v)) =
        lmarginal (fun _ : V => μ) T (cliqueWeightOnENN A W) x := by
    apply lmarginal_congr
    intro v hv
    have hvS : v ∈ S := by
      simpa [T] using hv
    rw [finsetPermFixing_apply_of_mem hSA hSB hcard hvS]
  have hrename := lmarginal_image
    (μ := fun _ : V => μ) σ.injective T
    (measurable_cliqueWeightOnENN A W) x
  have hrename' :
      lmarginal (fun _ : V => μ) T (cliqueWeightOnENN A W)
          (fun v => x (σ v)) =
        lmarginal (fun _ : V => μ) (T.image σ)
          (fun y => cliqueWeightOnENN A W (fun v => y (σ v))) x := by
    (convert hrename.symm using 1; rfl)
  calc
    lmarginal (fun _ : V => μ) T (cliqueWeightOnENN A W) x =
        lmarginal (fun _ : V => μ) T (cliqueWeightOnENN A W)
          (fun v => x (σ v)) := hx.symm
    _ = lmarginal (fun _ : V => μ) (T.image σ)
          (fun y => cliqueWeightOnENN A W (fun v => y (σ v))) x := by
      exact hrename'
    _ = lmarginal (fun _ : V => μ) T
          (cliqueWeightOnENN B W) x := by
      rw [hTimage]
      congr 1
      funext y
      exact cliqueWeightOnENN_comp_finsetPermFixing
        hSA hSB hcard W y

lemma cliqueWeightOn_nonneg
    (A : Finset V) (W : Graphon Ω μ) (x : V → Ω) :
    0 ≤ PureCliqueTreeDecomp.cliqueWeightOn A W x := by
  unfold PureCliqueTreeDecomp.cliqueWeightOn
  exact Finset.prod_nonneg fun e _ => edgeValue_nonneg W x e

lemma cliqueWeightOn_le_one
    (A : Finset V) (W : Graphon Ω μ) (x : V → Ω) :
    PureCliqueTreeDecomp.cliqueWeightOn A W x ≤ 1 := by
  unfold PureCliqueTreeDecomp.cliqueWeightOn
  exact Finset.prod_le_one
    (fun e _ => edgeValue_nonneg W x e)
    (fun e _ => edgeValue_le_one W x e)

lemma edgeValue_lower_bound
    (W : Graphon Ω μ) {δ : ℝ}
    (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) (edge : Sym2 V) :
    δ ≤ edgeValue W x edge := by
  induction edge using Sym2.inductionOn with
  | _ u v => simpa using hδ (x u) (x v)

lemma cliqueWeightOn_lower_bound
    (A : Finset V) (W : Graphon Ω μ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    δ ^ (pairsIn A).card ≤
      PureCliqueTreeDecomp.cliqueWeightOn A W x := by
  unfold PureCliqueTreeDecomp.cliqueWeightOn
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod
    (fun _ _ => hδ0)
    (fun edge _ => edgeValue_lower_bound W hδ x edge)

lemma cliqueWeightOnENN_le_one
    (A : Finset V) (W : Graphon Ω μ) (x : V → Ω) :
    cliqueWeightOnENN A W x ≤ 1 := by
  rw [cliqueWeightOnENN, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (cliqueWeightOn_le_one A W x)

lemma cliqueWeightOnENN_lower_bound
    (A : Finset V) (W : Graphon Ω μ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    ENNReal.ofReal (δ ^ (pairsIn A).card) ≤ cliqueWeightOnENN A W x := by
  rw [cliqueWeightOnENN]
  exact ENNReal.ofReal_le_ofReal
    (cliqueWeightOn_lower_bound A W hδ0 hδ x)

lemma integrable_cliqueWeightOn
    (A : Finset V) (W : Graphon Ω μ) :
    Integrable (PureCliqueTreeDecomp.cliqueWeightOn A W)
      (assignmentMeasure V μ) := by
  refine (integrable_const
    (μ := assignmentMeasure V μ) (1 : ℝ)).mono'
    (measurable_cliqueWeightOn A W).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (cliqueWeightOn_nonneg A W x)]
  exact cliqueWeightOn_le_one A W x

/-- Integrating a complete weight supported on `A` over the ambient product
space gives the clique density of size `|A|`. -/
theorem integral_cliqueWeightOn
    (A : Finset V) (W : Graphon Ω μ) :
    (∫ x, PureCliqueTreeDecomp.cliqueWeightOn A W x
        ∂assignmentMeasure V μ) =
      cliqueDensity A.card W := by
  classical
  let p : V → Prop := fun v => v ∈ A
  letI : Fintype (Subtype p) := Subtype.fintype p
  letI : Fintype (Subtype fun v => ¬p v) :=
    Subtype.fintype (fun v => ¬p v)
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : V => Ω) p
  have he : MeasurePreserving e
      (assignmentMeasure V μ)
      ((Measure.pi fun _ : Subtype p => μ).prod
        (Measure.pi fun _ : Subtype fun v => ¬p v => μ)) := by
    simpa only [e, assignmentMeasure] using
      (measurePreserving_piEquivPiSubtypeProd
        (fun _ : V => μ) p)
  let F : ((Subtype p → Ω) ×
      (Subtype (fun v => ¬p v) → Ω)) → ℝ :=
    fun z => graphWeight (⊤ : SimpleGraph (Subtype p)) W z.1
  have hF : Integrable F
      ((Measure.pi fun _ : Subtype p => μ).prod
        (Measure.pi fun _ : Subtype fun v => ¬p v => μ)) := by
    refine (integrable_const
      (μ := (Measure.pi fun _ : Subtype p => μ).prod
        (Measure.pi fun _ : Subtype fun v => ¬p v => μ))
      (1 : ℝ)).mono'
      ((measurable_graphWeight (⊤ : SimpleGraph (Subtype p)) W).comp
        measurable_fst).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (graphWeight_nonneg (⊤ : SimpleGraph (Subtype p)) W z.1)]
    exact graphWeight_le_one (⊤ : SimpleGraph (Subtype p)) W z.1
  have hcomp :
      F ∘ e = PureCliqueTreeDecomp.cliqueWeightOn A W := by
    funext x
    change graphWeight (⊤ : SimpleGraph (Subtype p)) W
        (fun a => x a.1) =
      PureCliqueTreeDecomp.cliqueWeightOn A W x
    unfold graphWeight PureCliqueTreeDecomp.cliqueWeightOn
    apply Finset.prod_bij
        (fun edge _ => edge.map (fun a : Subtype p => a.1))
    · intro edge hedge
      induction edge using Sym2.inductionOn with
      | _ u v =>
          change s(u.1, v.1) ∈ pairsIn A
          rw [mk_mem_pairsIn]
          have huv : u ≠ v := by
            simpa [SimpleGraph.mem_edgeFinset] using hedge
          refine ⟨fun h => huv (Subtype.ext h), ?_, ?_⟩
          · exact u.2
          · exact v.2
    · intro edge₁ h₁ edge₂ h₂ h
      exact Sym2.map.injective Subtype.val_injective h
    · intro edge hedge
      induction edge using Sym2.inductionOn with
      | _ u v =>
          rw [mk_mem_pairsIn] at hedge
          refine ⟨s(⟨u, hedge.2.1⟩, ⟨v, hedge.2.2⟩), ?_, ?_⟩
          · simpa [SimpleGraph.mem_edgeFinset] using hedge.1
          · simp
    · intro edge hedge
      induction edge using Sym2.inductionOn with
      | _ u v => simp [edgeValue, Sym2.lift_mk]
  calc
    (∫ x, PureCliqueTreeDecomp.cliqueWeightOn A W x
        ∂assignmentMeasure V μ) =
        ∫ z, F z
          ∂((Measure.pi fun _ : Subtype p => μ).prod
            (Measure.pi fun _ : Subtype fun v => ¬p v => μ)) := by
      rw [← he.integral_comp']
      exact integral_congr_ae (ae_of_all _ fun x => (congrFun hcomp x).symm)
    _ = ∫ z : Subtype p → Ω,
          graphWeight (⊤ : SimpleGraph (Subtype p)) W z
            ∂Measure.pi (fun _ : Subtype p => μ) := by
      rw [integral_prod _ hF]
      simp [F]
    _ = homDensity (⊤ : SimpleGraph (Subtype p)) W := rfl
    _ = cliqueDensity (Fintype.card (Subtype p)) W := by
      exact homDensity_iso W
        (SimpleGraph.Iso.completeGraph (Fintype.equivFin (Subtype p)))
    _ = cliqueDensity A.card W := by
      congr 2
      simp [p]

lemma lintegral_cliqueWeightOnENN
    (A : Finset V) (W : Graphon Ω μ) :
    ∫⁻ x, cliqueWeightOnENN A W x
        ∂assignmentMeasure V μ =
      ENNReal.ofReal (cliqueDensity A.card W) := by
  unfold cliqueWeightOnENN
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_cliqueWeightOn A W)
    (Filter.Eventually.of_forall fun x =>
      cliqueWeightOn_nonneg A W x)]
  rw [integral_cliqueWeightOn]

end PureChordal
