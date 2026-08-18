import Taeyoung.Foundation.HomDensity
import Taeyoung.Foundation.Relabeling
import Taeyoung.Methods.PureChordal.WeightedCauchySchwarz
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Conditional clique moments

We represent an assignment on `Option α` by an assignment on `α` together
with the value of the new vertex `none`.  The complete-graph weight then
factors into the old clique weight and the product of the new incident edges.
-/

open MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def optionAssignment {α : Type*} (z : α → Ω) (y : Ω) : Option α → Ω
  | none => y
  | some i => z i

@[simp] lemma optionAssignment_none {α : Type*} (z : α → Ω) (y : Ω) :
    optionAssignment z y none = y := rfl

@[simp] lemma optionAssignment_some {α : Type*} (z : α → Ω) (y : Ω) (i : α) :
    optionAssignment z y (some i) = z i := rfl

noncomputable def optionAssignmentEquiv
    {α : Type*} [Fintype α] [DecidableEq α] :
    ((α → Ω) × Ω) ≃ᵐ (Option α → Ω) :=
  (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option α => Ω)).symm

@[simp] lemma optionAssignmentEquiv_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : (α → Ω) × Ω) :
    optionAssignmentEquiv p =
      optionAssignment p.1 p.2 := by
  funext i
  cases i <;> rfl

private lemma measurePreserving_optionAssignment
    {α : Type*} [Fintype α] [DecidableEq α] :
    MeasurePreserving
      (optionAssignmentEquiv :
        ((α → Ω) × Ω) ≃ᵐ (Option α → Ω))
      ((assignmentMeasure α μ).prod μ)
      (assignmentMeasure (Option α) μ) := by
  refine ⟨(optionAssignmentEquiv (α := α) (Ω := Ω)).measurable, ?_⟩
  simpa [optionAssignmentEquiv, assignmentMeasure] using
    (Measure.pi_map_piOptionEquivProd
      (fun _ : Option α => μ))

lemma integral_assignmentMeasure_option
    {α : Type*} [Fintype α] [DecidableEq α]
    {f : (Option α → Ω) → ℝ}
    (hf : Integrable f (assignmentMeasure (Option α) μ)) :
    (∫ x, f x ∂assignmentMeasure (Option α) μ) =
      ∫ z, ∫ y, f (optionAssignment z y) ∂μ
        ∂assignmentMeasure α μ := by
  have hp := measurePreserving_optionAssignment (α := α) (Ω := Ω) (μ := μ)
  have hprod :
      Integrable
        (fun p : (α → Ω) × Ω =>
          f (optionAssignmentEquiv p))
        ((assignmentMeasure α μ).prod μ) :=
    hp.integrable_comp_of_integrable hf
  calc
    (∫ x, f x ∂assignmentMeasure (Option α) μ) =
        ∫ p, f (optionAssignmentEquiv p)
          ∂((assignmentMeasure α μ).prod μ) :=
      (hp.integral_comp' f).symm
    _ = ∫ z, ∫ y, f (optionAssignment z y) ∂μ
          ∂assignmentMeasure α μ := by
      rw [integral_prod _ hprod]
      simp only [optionAssignmentEquiv_apply]

lemma integrable_optionFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    {f : (Option α → Ω) → ℝ}
    (hf : Integrable f (assignmentMeasure (Option α) μ)) :
    Integrable (fun z => ∫ y, f (optionAssignment z y) ∂μ)
      (assignmentMeasure α μ) := by
  have hp := measurePreserving_optionAssignment (α := α) (Ω := Ω) (μ := μ)
  have hprod :
      Integrable
        (fun p : (α → Ω) × Ω =>
          f (optionAssignmentEquiv p))
        ((assignmentMeasure α μ).prod μ) :=
    hp.integrable_comp_of_integrable hf
  simpa only [optionAssignmentEquiv_apply] using hprod.integral_prod_left

/-- Product of the edges from one new vertex to all vertices of an assignment. -/
def cliqueExtensionWeight {α : Type*} [Fintype α]
    (W : Graphon Ω μ) (z : α → Ω) (y : Ω) : ℝ :=
  ∏ i, W y (z i)

lemma measurable_cliqueExtensionWeight {α : Type*} [Fintype α]
    (W : Graphon Ω μ) :
    Measurable (Function.uncurry (cliqueExtensionWeight (α := α) W)) := by
  unfold cliqueExtensionWeight
  exact Finset.measurable_fun_prod _ fun i _ =>
    W.measurable.comp
      (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))

lemma cliqueExtensionWeight_nonneg {α : Type*} [Fintype α]
    (W : Graphon Ω μ) (z : α → Ω) (y : Ω) :
    0 ≤ cliqueExtensionWeight W z y :=
  Finset.prod_nonneg fun i _ => W.nonneg _ _

lemma cliqueExtensionWeight_le_one {α : Type*} [Fintype α]
    (W : Graphon Ω μ) (z : α → Ω) (y : Ω) :
    cliqueExtensionWeight W z y ≤ 1 :=
  Finset.prod_le_one
    (fun i _ => W.nonneg _ _)
    (fun i _ => W.le_one _ _)

private lemma prod_old_edges_option
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) (z : α → Ω) (y : Ω) :
    (∏ e ∈ (⊤ : SimpleGraph α).edgeFinset, edgeValue W z e) =
      ∏ e ∈ (⊤ : SimpleGraph (Option α)).edgeFinset \
          (⊤ : SimpleGraph (Option α)).incidenceFinset none,
        edgeValue W (optionAssignment z y) e := by
  classical
  apply Finset.prod_bij
      (fun e _ => e.map Option.some)
  · intro e he
    rw [Finset.mem_sdiff]
    constructor
    · have hn : ¬e.IsDiag :=
        (⊤ : SimpleGraph α).not_isDiag_of_mem_edgeFinset he
      have hm : ¬(e.map Option.some).IsDiag :=
        ((Sym2.isDiag_map (f := @Option.some α)
          (z := e) (Option.some_injective α)).not).mpr hn
      simpa [SimpleGraph.mem_edgeFinset] using hm
    · rw [SimpleGraph.mem_incidenceFinset]
      intro h
      rcases Sym2.mem_map.mp h.2 with ⟨a, ha, hsome⟩
      exact Option.some_ne_none a hsome
  · intro e₁ h₁ e₂ h₂ h
    exact Sym2.map.injective (Option.some_injective α) h
  · intro e he
    rw [Finset.mem_sdiff] at he
    induction e using Sym2.inductionOn with
    | _ u v =>
        rcases u with _ | u
        · exfalso
          apply he.2
          rw [SimpleGraph.mem_incidenceFinset]
          exact ⟨SimpleGraph.mem_edgeFinset.mp he.1, Sym2.mem_mk_left _ _⟩
        rcases v with _ | v
        · exfalso
          apply he.2
          rw [SimpleGraph.mem_incidenceFinset]
          exact ⟨SimpleGraph.mem_edgeFinset.mp he.1, Sym2.mem_mk_right _ _⟩
        refine ⟨s(u, v), ?_, ?_⟩
        · simpa [SimpleGraph.mem_edgeFinset] using he.1
        · simp
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v => simp

private lemma prod_incident_edges_option
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) (z : α → Ω) (y : Ω) :
    (∏ i : α, W y (z i)) =
      ∏ e ∈ (⊤ : SimpleGraph (Option α)).incidenceFinset none,
        edgeValue W (optionAssignment z y) e := by
  classical
  apply Finset.prod_bij (fun i _ => s(none, some i))
  · intro i hi
    simp [SimpleGraph.mem_incidenceFinset]
  · intro i₁ h₁ i₂ h₂ h
    simpa [Sym2.eq_iff] using h
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        rcases u with _ | u
        · rcases v with _ | v
          · have he' :=
              (((⊤ : SimpleGraph (Option α)).mem_incidenceFinset none)
                s(none, none)).mp he
            exact False.elim
              ((⊤ : SimpleGraph (Option α)).not_isDiag_of_mem_edgeSet he'.1 rfl)
          · exact ⟨v, Finset.mem_univ _, rfl⟩
        · rcases v with _ | v
          · exact ⟨u, Finset.mem_univ _, by simp [Sym2.eq_iff]⟩
          · exfalso
            have he' :=
              (((⊤ : SimpleGraph (Option α)).mem_incidenceFinset none)
                s(some u, some v)).mp he
            have hnone : none ∈ s(some u, some v) := he'.2
            simp [Sym2.mem_iff] at hnone
  · intro i hi
    simp [edgeValue, Sym2.lift_mk]

/-- Deleting all edges at the new `none` vertex leaves exactly the old
complete-graph weight. -/
theorem graphWeight_top_deleteIncidence_option
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) (z : α → Ω) (y : Ω) :
    graphWeight
        ((⊤ : SimpleGraph (Option α)).deleteIncidenceSet none) W
        (optionAssignment z y) =
      graphWeight (⊤ : SimpleGraph α) W z := by
  classical
  unfold graphWeight
  rw [SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff]
  exact (prod_old_edges_option W z y).symm

/-- An isolated extra vertex contributes a factor one to homomorphism
density. -/
theorem homDensity_top_deleteIncidence_option
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) :
    homDensity ((⊤ : SimpleGraph (Option α)).deleteIncidenceSet none) W =
      homDensity (⊤ : SimpleGraph α) W := by
  let G := (⊤ : SimpleGraph (Option α)).deleteIncidenceSet none
  have hf : Integrable (graphWeight G W)
      (assignmentMeasure (Option α) μ) :=
    integrable_graphWeight G W
  rw [homDensity, integral_assignmentMeasure_option hf, homDensity]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [show (∫ y, graphWeight G W (optionAssignment z y) ∂μ) =
      ∫ _ : Ω, graphWeight (⊤ : SimpleGraph α) W z ∂μ by
        apply integral_congr_ae
        filter_upwards [] with y
        exact graphWeight_top_deleteIncidence_option W z y]
  simp

theorem graphWeight_top_option
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) (z : α → Ω) (y : Ω) :
    graphWeight (⊤ : SimpleGraph (Option α)) W (optionAssignment z y) =
      graphWeight (⊤ : SimpleGraph α) W z * cliqueExtensionWeight W z y := by
  classical
  unfold graphWeight cliqueExtensionWeight
  calc
    (∏ e ∈ (⊤ : SimpleGraph (Option α)).edgeFinset,
        edgeValue W (optionAssignment z y) e) =
      (∏ e ∈ (⊤ : SimpleGraph (Option α)).edgeFinset \
          (⊤ : SimpleGraph (Option α)).incidenceFinset none,
        edgeValue W (optionAssignment z y) e) *
      ∏ e ∈ (⊤ : SimpleGraph (Option α)).incidenceFinset none,
        edgeValue W (optionAssignment z y) e :=
      (Finset.prod_sdiff
        (f := fun e => edgeValue W (optionAssignment z y) e)
        ((⊤ : SimpleGraph (Option α)).incidenceFinset_subset none)
        ).symm
    _ = (∏ e ∈ (⊤ : SimpleGraph α).edgeFinset, edgeValue W z e) *
          ∏ i : α, W y (z i) := by
      rw [prod_old_edges_option W z y, prod_incident_edges_option W z y]

/-- The conditional density of extending an assigned clique by one vertex. -/
noncomputable def cliqueExtensionDensity
    {α : Type*} [Fintype α]
    (W : Graphon Ω μ) (z : α → Ω) : ℝ :=
  ∫ y, cliqueExtensionWeight W z y ∂μ

lemma measurable_cliqueExtensionDensity
    {α : Type*} [Fintype α]
    (W : Graphon Ω μ) :
    Measurable (cliqueExtensionDensity (α := α) W) := by
  exact ((measurable_cliqueExtensionWeight (α := α) W).stronglyMeasurable
    |>.integral_prod_right (ν := μ)).measurable

lemma cliqueExtensionDensity_nonneg
    {α : Type*} [Fintype α]
    (W : Graphon Ω μ) (z : α → Ω) :
    0 ≤ cliqueExtensionDensity W z := by
  exact integral_nonneg fun y => cliqueExtensionWeight_nonneg W z y

lemma cliqueExtensionDensity_le_one
    {α : Type*} [Fintype α]
    (W : Graphon Ω μ) (z : α → Ω) :
    cliqueExtensionDensity W z ≤ 1 := by
  simpa [cliqueExtensionDensity] using
    integral_mono
      ((integrable_const (μ := μ) (1 : ℝ)).mono'
        ((measurable_cliqueExtensionWeight (α := α) W).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun y => by
          simp only [Function.comp_apply, Function.uncurry_apply_pair, id_eq]
          rw [Real.norm_eq_abs, abs_of_nonneg
            (cliqueExtensionWeight_nonneg W z y)]
          exact cliqueExtensionWeight_le_one W z y))
      (integrable_const (μ := μ) (1 : ℝ))
      (fun y => cliqueExtensionWeight_le_one W z y)

/-- Adding one vertex to a clique is integration against its extension density. -/
theorem homDensity_top_option_eq_extension
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Option α)) W =
      ∫ z, graphWeight (⊤ : SimpleGraph α) W z *
        cliqueExtensionDensity W z ∂assignmentMeasure α μ := by
  let e :=
    MeasurableEquiv.piOptionEquivProd
      (fun _ : Option α => Ω)
  have he : MeasurePreserving e.symm
      ((assignmentMeasure α μ).prod μ)
      (assignmentMeasure (Option α) μ) := by
    refine ⟨e.symm.measurable, ?_⟩
    simpa [assignmentMeasure] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option α => μ))
  have hint :
      Integrable
        (graphWeight (⊤ : SimpleGraph (Option α)) W ∘ e.symm)
        ((assignmentMeasure α μ).prod μ) :=
    he.integrable_comp_of_integrable
      (integrable_graphWeight (⊤ : SimpleGraph (Option α)) W)
  rw [homDensity, ← he.integral_comp']
  rw [integral_prod
    (fun z => graphWeight (⊤ : SimpleGraph (Option α)) W (e.symm z))
    (by simpa [Function.comp_def] using hint)]
  apply integral_congr_ae
  filter_upwards [] with z
  have he_apply (y : Ω) :
      e.symm (z, y) = optionAssignment z y := by
    funext i
    cases i <;> rfl
  calc
    (∫ y, graphWeight (⊤ : SimpleGraph (Option α)) W
        (e.symm (z, y)) ∂μ) =
        ∫ y, graphWeight (⊤ : SimpleGraph α) W z *
          cliqueExtensionWeight W z y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [he_apply, graphWeight_top_option]
    _ = graphWeight (⊤ : SimpleGraph α) W z *
        cliqueExtensionDensity W z := by
      rw [integral_const_mul]
      rfl

theorem cliqueDensity_succ_eq_extension
    (s : ℕ) (W : Graphon Ω μ) :
    cliqueDensity (s + 1) W =
      ∫ z, graphWeight (⊤ : SimpleGraph (Fin s)) W z *
        cliqueExtensionDensity W z ∂assignmentMeasure (Fin s) μ := by
  calc
    cliqueDensity (s + 1) W =
        homDensity (⊤ : SimpleGraph (Option (Fin s))) W := by
      exact homDensity_iso W
        (SimpleGraph.Iso.completeGraph (finSuccEquiv s))
    _ = _ := homDensity_top_option_eq_extension W

/-- The complete graph on two successive new vertices, with the edge between
the two new vertices removed. -/
abbrev twoExtensionGraph (α : Type*) :
    SimpleGraph (Option (Option α)) :=
  (⊤ : SimpleGraph (Option (Option α))).deleteEdges
    (({s(none, some none)} :
      Finset (Sym2 (Option (Option α)))) : Set (Sym2 (Option (Option α))))

private lemma prod_incident_edges_twoExtension
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) (z : α → Ω) (y₁ y₂ : Ω) :
    (∏ i : α, W y₂ (z i)) =
      ∏ e ∈ (⊤ : SimpleGraph (Option (Option α))).incidenceFinset none
          |>.erase s(none, some none),
        edgeValue W (optionAssignment (optionAssignment z y₁) y₂) e := by
  classical
  apply Finset.prod_bij (fun i _ => s(none, some (some i)))
  · intro i hi
    simp [SimpleGraph.mem_incidenceFinset, Sym2.eq_iff]
  · intro i₁ h₁ i₂ h₂ h
    simpa [Sym2.eq_iff] using h
  · intro e he
    simp only [Finset.mem_erase] at he
    induction e using Sym2.inductionOn with
    | _ u v =>
        rcases u with _ | u
        · rcases v with _ | v
          · have he' :=
              (((⊤ : SimpleGraph (Option (Option α))).mem_incidenceFinset none)
                s(none, none)).mp he.2
            exact False.elim
              ((⊤ : SimpleGraph (Option (Option α))).not_isDiag_of_mem_edgeSet he'.1 rfl)
          · rcases v with _ | v
            · exact False.elim (he.1 (by simp [Sym2.eq_iff]))
            · exact ⟨v, Finset.mem_univ _, rfl⟩
        · rcases v with _ | v
          · rcases u with _ | u
            · exact False.elim (he.1 (by simp [Sym2.eq_iff]))
            · exact ⟨u, Finset.mem_univ _, by simp [Sym2.eq_iff]⟩
          · exfalso
            have he' :=
              (((⊤ : SimpleGraph (Option (Option α))).mem_incidenceFinset none)
                s(some u, some v)).mp he.2
            have hnone : none ∈ s(some u, some v) := he'.2
            simp [Sym2.mem_iff] at hnone
  · intro i hi
    simp [edgeValue, Sym2.lift_mk]

theorem graphWeight_twoExtension
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) (z : α → Ω) (y₁ y₂ : Ω) :
    graphWeight (twoExtensionGraph α) W
        (optionAssignment (optionAssignment z y₁) y₂) =
      graphWeight (⊤ : SimpleGraph α) W z *
        cliqueExtensionWeight W z y₁ *
        cliqueExtensionWeight W z y₂ := by
  classical
  let E := (⊤ : SimpleGraph (Option (Option α))).edgeFinset
  let I := (⊤ : SimpleGraph (Option (Option α))).incidenceFinset none
  let e₀ : Sym2 (Option (Option α)) := s(none, some none)
  have heI : e₀ ∈ I := by
    simp [I, e₀, SimpleGraph.mem_incidenceFinset]
  have hset : E.erase e₀ = (E \ I) ∪ (I.erase e₀) := by
    ext e
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro h
      by_cases he : e ∈ I
      · exact Or.inr ⟨h.1, he⟩
      · exact Or.inl ⟨h.2, he⟩
    · intro h
      rcases h with h | h
      · exact ⟨fun heq => h.2 (heq ▸ heI), h.1⟩
      · exact ⟨h.1, (⊤ : SimpleGraph (Option (Option α))).incidenceFinset_subset none h.2⟩
  have hdisj : Disjoint (E \ I) (I.erase e₀) := by
    exact Finset.disjoint_left.mpr fun e heOld heInc =>
      (Finset.mem_sdiff.mp heOld).2 (Finset.mem_erase.mp heInc).2
  unfold graphWeight
  change
    (∏ e ∈ ((⊤ : SimpleGraph (Option (Option α))).deleteEdges
        (({s(none, some none)} :
          Finset (Sym2 (Option (Option α)))) :
            Set (Sym2 (Option (Option α))))).edgeFinset,
      edgeValue W (optionAssignment (optionAssignment z y₁) y₂) e) = _
  rw [SimpleGraph.edgeFinset_deleteEdges, Finset.sdiff_singleton_eq_erase, hset,
    Finset.prod_union hdisj]
  rw [← prod_old_edges_option W (optionAssignment z y₁) y₂]
  have htop := graphWeight_top_option W z y₁
  unfold graphWeight at htop
  rw [htop]
  dsimp [I, e₀]
  rw [← prod_incident_edges_twoExtension W z y₁ y₂]
  rfl

/-- The weighted second moment of the conditional clique-extension density. -/
noncomputable def cliqueExtensionSecondMoment
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) : ℝ :=
  ∫ z, graphWeight (⊤ : SimpleGraph α) W z *
    cliqueExtensionDensity W z ^ 2 ∂assignmentMeasure α μ

theorem homDensity_twoExtension_eq_secondMoment
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : Graphon Ω μ) :
    homDensity (twoExtensionGraph α) W =
      cliqueExtensionSecondMoment (α := α) W := by
  let f : (Option (Option α) → Ω) → ℝ :=
    graphWeight (twoExtensionGraph α) W
  have hf : Integrable f (assignmentMeasure (Option (Option α)) μ) :=
    integrable_graphWeight (twoExtensionGraph α) W
  rw [homDensity, integral_assignmentMeasure_option hf]
  have hinner : Integrable
      (fun q => ∫ y₂, f (optionAssignment q y₂) ∂μ)
      (assignmentMeasure (Option α) μ) :=
    integrable_optionFiber hf
  rw [integral_assignmentMeasure_option hinner]
  unfold cliqueExtensionSecondMoment
  apply integral_congr_ae
  filter_upwards [] with z
  calc
    (∫ y₁, ∫ y₂,
        f (optionAssignment (optionAssignment z y₁) y₂) ∂μ ∂μ) =
        ∫ y₁, (graphWeight (⊤ : SimpleGraph α) W z *
          cliqueExtensionWeight W z y₁) *
          cliqueExtensionDensity W z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y₁
      calc
        (∫ y₂, f (optionAssignment (optionAssignment z y₁) y₂) ∂μ) =
            ∫ y₂, (graphWeight (⊤ : SimpleGraph α) W z *
              cliqueExtensionWeight W z y₁) *
              cliqueExtensionWeight W z y₂ ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with y₂
          exact graphWeight_twoExtension W z y₁ y₂
        _ = (graphWeight (⊤ : SimpleGraph α) W z *
              cliqueExtensionWeight W z y₁) *
              cliqueExtensionDensity W z := by
          rw [integral_const_mul]
          rfl
    _ = (graphWeight (⊤ : SimpleGraph α) W z *
          cliqueExtensionDensity W z) *
          cliqueExtensionDensity W z := by
      rw [integral_mul_const]
      rw [integral_const_mul]
      rfl
    _ = graphWeight (⊤ : SimpleGraph α) W z *
          cliqueExtensionDensity W z ^ 2 := by ring

theorem cliqueDensity_sq_le_cliqueDensity_mul_secondMoment
    (s : ℕ) (W : Graphon Ω μ) :
    cliqueDensity (s + 1) W ^ 2 ≤
      cliqueDensity s W *
        cliqueExtensionSecondMoment (α := Fin s) W := by
  let A : (Fin s → Ω) → ℝ :=
    graphWeight (⊤ : SimpleGraph (Fin s)) W
  let η : (Fin s → Ω) → ℝ :=
    cliqueExtensionDensity W
  have hη : Integrable η (assignmentMeasure (Fin s) μ) := by
    refine (integrable_const (μ := assignmentMeasure (Fin s) μ) (1 : ℝ)).mono'
      (measurable_cliqueExtensionDensity W).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (cliqueExtensionDensity_nonneg W z)]
    exact cliqueExtensionDensity_le_one W z
  have hA : Integrable A (assignmentMeasure (Fin s) μ) :=
    integrable_graphWeight (⊤ : SimpleGraph (Fin s)) W
  have hAη : Integrable (fun z => A z * η z)
      (assignmentMeasure (Fin s) μ) := by
    refine (integrable_const
      (μ := assignmentMeasure (Fin s) μ) (1 : ℝ)).mono'
      ((measurable_graphWeight (⊤ : SimpleGraph (Fin s)) W).mul
        (measurable_cliqueExtensionDensity W)).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (graphWeight_nonneg _ W z)
        (cliqueExtensionDensity_nonneg W z))]
    exact mul_le_one₀ (graphWeight_le_one _ W z)
      (cliqueExtensionDensity_nonneg W z)
      (cliqueExtensionDensity_le_one W z)
  have hAη2 : Integrable (fun z => A z * η z ^ 2)
      (assignmentMeasure (Fin s) μ) := by
    refine (integrable_const
      (μ := assignmentMeasure (Fin s) μ) (1 : ℝ)).mono'
      ((measurable_graphWeight (⊤ : SimpleGraph (Fin s)) W).mul
        ((measurable_cliqueExtensionDensity W).pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (graphWeight_nonneg _ W z) (sq_nonneg _))]
    have hηsq : η z ^ 2 ≤ 1 := by
      nlinarith [cliqueExtensionDensity_nonneg W z,
        cliqueExtensionDensity_le_one W z]
    exact mul_le_one₀ (graphWeight_le_one _ W z) (sq_nonneg _) hηsq
  have hcs :=
    integral_mul_sq_le_integral_mul_integral_mul_sq
      hA hAη hAη2
      (fun z => graphWeight_nonneg (⊤ : SimpleGraph (Fin s)) W z)
  rw [← cliqueDensity_succ_eq_extension s W] at hcs
  simpa [A, η, cliqueDensity, homDensity,
    cliqueExtensionSecondMoment] using hcs

end Taeyoung.Methods.PureChordal
