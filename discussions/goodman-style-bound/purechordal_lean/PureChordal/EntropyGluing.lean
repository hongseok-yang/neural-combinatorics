import PureChordal.JunctionDensity
import PureChordal.Gibbs
import PureChordal.Regularization

/-!
# Entropy gluing for a pure clique tree

This file proves the clique-tree gluing inequality `t(H,W) ∏ t_{s_i} ≥ t_r^m`.
It builds the normalized junction densities, applies the local Gibbs inequality
to them for strictly positive regularised kernels, and then removes the
regularisation by letting `ε → 0` via the explicit continuity estimate.  All
densities are explicit functions; no conditional-probability API is used.
-/

namespace PureChordal

open MeasureTheory
open scoped ENNReal BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} {r m : ℕ}
variable (D : PureCliqueTreeDecomp H r m)
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

namespace PureCliqueTreeDecomp

/-! ### Normalized junction densities

The gluing argument compares two probability laws with the local Gibbs
inequality.  Each object below is either an `ℝ≥0∞`-valued weight/law (`…ENN`) or
its real-valued `toReal` counterpart (`…Density`). -/

/-- Total mass of the separator clique weight: `∫ κ_{S_i} = t(K_{|S_i|}, W)`. -/
noncomputable def separatorMassENN
    (W : Graphon Ω μ) (i : Fin m) : ℝ≥0∞ :=
  ENNReal.ofReal (cliqueDensity (D.separator i).card W)

/-- The clique weight `κ_{S_i}` of the parent separator of bag `i`. -/
noncomputable def separatorWeightENN
    (W : Graphon Ω μ) (i : Fin m) : (V → Ω) → ℝ≥0∞ :=
  cliqueWeightOnENN (D.separator i) W

/-- The separator clique weight normalized to a probability law by its mass. -/
noncomputable def normalizedSeparatorENN
    (W : Graphon Ω μ) (i : Fin m) : (V → Ω) → ℝ≥0∞ :=
  fun x => (D.separatorMassENN W i)⁻¹ * D.separatorWeightENN W i x

/-- The new-vertex marginal of bag `i`, normalized by the common clique mass. -/
noncomputable def normalizedBagNewENN
    (W : Graphon Ω μ) (i : Fin m) : (V → Ω) → ℝ≥0∞ :=
  fun x => (D.cliqueMassENN W)⁻¹ * D.bagNewMarginalENN W i x

/-- The completed junction law reweighted at bag `i` by the ratio of its
normalized separator law to its normalized new-vertex law.  This is the second
comparison law feeding the Gibbs inequality for the separator factors. -/
noncomputable def separatorTiltENN
    (W : Graphon Ω μ) (i : Fin m) : (V → Ω) → ℝ≥0∞ :=
  fun x => D.partialJunctionENN W m x *
    ((D.normalizedBagNewENN W i x)⁻¹ *
      D.normalizedSeparatorENN W i x)

/-- The graph weight normalized by its homomorphism density: the graph Gibbs
law whose relative entropy against the junction law drives the bound. -/
noncomputable def normalizedGraphENN
    [DecidableRel H.Adj] (W : Graphon Ω μ) : (V → Ω) → ℝ≥0∞ :=
  fun x => (ENNReal.ofReal (homDensity H W))⁻¹ *
    ENNReal.ofReal (graphWeight H W x)

/-- Real-valued form of `normalizedGraphENN`. -/
noncomputable def normalizedGraphDensity
    [DecidableRel H.Adj] (W : Graphon Ω μ) : (V → Ω) → ℝ :=
  fun x => (normalizedGraphENN (H := H) W x).toReal

/-- Real-valued form of `separatorTiltENN`. -/
noncomputable def separatorTiltDensity
    (W : Graphon Ω μ) (i : Fin m) : (V → Ω) → ℝ :=
  fun x => (D.separatorTiltENN W i x).toReal

/-- Real-valued form of `normalizedBagNewENN`. -/
noncomputable def normalizedBagNewDensity
    (W : Graphon Ω μ) (i : Fin m) : (V → Ω) → ℝ :=
  fun x => (D.normalizedBagNewENN W i x).toReal

/-- Real-valued form of `normalizedSeparatorENN`. -/
noncomputable def normalizedSeparatorDensity
    (W : Graphon Ω μ) (i : Fin m) : (V → Ω) → ℝ :=
  fun x => (D.normalizedSeparatorENN W i x).toReal

/-! ### Measurability, positivity, and bounds of the densities -/

lemma measurable_separatorWeightENN
    (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.separatorWeightENN W i) :=
  measurable_cliqueWeightOnENN (D.separator i) W

lemma measurable_normalizedSeparatorENN
    (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.normalizedSeparatorENN W i) :=
  measurable_const.mul (D.measurable_separatorWeightENN W i)

lemma measurable_normalizedBagNewENN
    (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.normalizedBagNewENN W i) :=
  measurable_const.mul (D.measurable_bagNewMarginalENN W i)

lemma measurable_separatorTiltENN
    (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.separatorTiltENN W i) :=
  (D.measurable_partialJunctionENN W m).mul <|
    (D.measurable_normalizedBagNewENN W i).inv.mul
      (D.measurable_normalizedSeparatorENN W i)

lemma measurable_normalizedGraphENN
    [DecidableRel H.Adj] (W : Graphon Ω μ) :
    Measurable (normalizedGraphENN (H := H) W) :=
  measurable_const.mul <|
    (measurable_graphWeight H W).ennreal_ofReal

lemma measurable_normalizedGraphDensity
    [DecidableRel H.Adj] (W : Graphon Ω μ) :
    Measurable (normalizedGraphDensity (H := H) W) :=
  (measurable_normalizedGraphENN (H := H) W).ennreal_toReal

lemma measurable_separatorTiltDensity
    (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.separatorTiltDensity W i) :=
  (D.measurable_separatorTiltENN W i).ennreal_toReal

lemma normalizedBagNewENN_dependsOn
    (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (D.separator i) (D.normalizedBagNewENN W i) :=
  (FinsetDependsOn.const (D.separator i)
    (D.cliqueMassENN W)⁻¹).mul
      (D.bagNewMarginalENN_dependsOn W i)

lemma separatorWeightENN_dependsOn
    (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (D.separator i) (D.separatorWeightENN W i) := by
  intro x y hxy
  exact cliqueWeightOnENN_congr_on (D.separator i) W hxy

lemma normalizedSeparatorENN_dependsOn
    (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (D.separator i) (D.normalizedSeparatorENN W i) :=
  (FinsetDependsOn.const (D.separator i)
    (D.separatorMassENN W i)⁻¹).mul
      (D.separatorWeightENN_dependsOn W i)

lemma separatorMassENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    D.separatorMassENN W i ≠ 0 := by
  exact ne_of_gt <| ENNReal.ofReal_pos.mpr <|
    cliqueDensity_pos_of_lower_bound
      (D.separator i).card W hδpos hδ

lemma separatorMassENN_ne_top
    (W : Graphon Ω μ) (i : Fin m) :
    D.separatorMassENN W i ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma cliqueMassENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    D.cliqueMassENN W ≠ 0 := by
  exact ne_of_gt <| ENNReal.ofReal_pos.mpr <|
    cliqueDensity_pos_of_lower_bound r W hδpos hδ

lemma cliqueMassENN_ne_top (W : Graphon Ω μ) :
    D.cliqueMassENN W ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma normalizedBagNewENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.normalizedBagNewENN W i x ≠ 0 := by
  unfold normalizedBagNewENN
  exact mul_ne_zero
    (ENNReal.inv_ne_zero.mpr (D.cliqueMassENN_ne_top W))
    (D.bagNewMarginalENN_ne_zero W hδpos hδ i x)

lemma normalizedBagNewENN_ne_top
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.normalizedBagNewENN W i x ≠ ∞ := by
  unfold normalizedBagNewENN
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr
      (D.cliqueMassENN_ne_zero W hδpos hδ))
    (D.bagNewMarginalENN_ne_top W i x)

lemma separatorWeightENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.separatorWeightENN W i x ≠ 0 := by
  unfold separatorWeightENN
  have hlower := cliqueWeightOnENN_lower_bound
    (D.separator i) W hδpos.le hδ x
  exact ne_of_gt <| lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr (pow_pos hδpos _)) hlower

lemma separatorWeightENN_ne_top
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    D.separatorWeightENN W i x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (cliqueWeightOnENN_le_one (D.separator i) W x)

lemma normalizedSeparatorENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.normalizedSeparatorENN W i x ≠ 0 := by
  unfold normalizedSeparatorENN
  exact mul_ne_zero
    (ENNReal.inv_ne_zero.mpr (D.separatorMassENN_ne_top W i))
    (D.separatorWeightENN_ne_zero W hδpos hδ i x)

lemma normalizedSeparatorENN_ne_top
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.normalizedSeparatorENN W i x ≠ ∞ := by
  unfold normalizedSeparatorENN
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr
      (D.separatorMassENN_ne_zero W hδpos hδ i))
    (D.separatorWeightENN_ne_top W i x)

theorem lintegral_normalizedSeparatorENN_eq_one
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∫⁻ x, D.normalizedSeparatorENN W i x
        ∂assignmentMeasure V μ = 1 := by
  unfold normalizedSeparatorENN separatorWeightENN
  rw [MeasureTheory.lintegral_const_mul
    (μ := assignmentMeasure V μ)
    (D.separatorMassENN W i)⁻¹
    (measurable_cliqueWeightOnENN (D.separator i) W)]
  rw [lintegral_cliqueWeightOnENN]
  change (D.separatorMassENN W i)⁻¹ * D.separatorMassENN W i = 1
  exact ENNReal.inv_mul_cancel
    (D.separatorMassENN_ne_zero W hδpos hδ i)
    (D.separatorMassENN_ne_top W i)

lemma graphMassENN_ne_zero
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ENNReal.ofReal (homDensity H W) ≠ 0 :=
  ne_of_gt <| ENNReal.ofReal_pos.mpr <|
    homDensity_pos_of_lower_bound H W hδpos hδ

lemma lintegral_ofReal_graphWeight
    [DecidableRel H.Adj] (W : Graphon Ω μ) :
    ∫⁻ x, ENNReal.ofReal (graphWeight H W x)
        ∂assignmentMeasure V μ =
      ENNReal.ofReal (homDensity H W) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_graphWeight H W)
    (Filter.Eventually.of_forall fun x =>
      graphWeight_nonneg H W x)]
  rfl

theorem lintegral_normalizedGraphENN_eq_one
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ∫⁻ x, normalizedGraphENN (H := H) W x
        ∂assignmentMeasure V μ = 1 := by
  unfold normalizedGraphENN
  rw [MeasureTheory.lintegral_const_mul
    (μ := assignmentMeasure V μ)
    (ENNReal.ofReal (homDensity H W))⁻¹
    ((measurable_graphWeight H W).ennreal_ofReal)]
  rw [lintegral_ofReal_graphWeight]
  exact ENNReal.inv_mul_cancel
    (graphMassENN_ne_zero (H := H) W hδpos hδ)
    ENNReal.ofReal_ne_top

lemma normalizedGraphENN_ne_zero
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (x : V → Ω) :
    normalizedGraphENN (H := H) W x ≠ 0 := by
  unfold normalizedGraphENN
  exact mul_ne_zero
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ne_of_gt <| ENNReal.ofReal_pos.mpr <|
      lt_of_lt_of_le (pow_pos hδpos _) <|
        graphWeight_lower_bound H W hδpos.le hδ x)

lemma normalizedGraphENN_ne_top
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (x : V → Ω) :
    normalizedGraphENN (H := H) W x ≠ ∞ := by
  unfold normalizedGraphENN
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr
      (graphMassENN_ne_zero (H := H) W hδpos hδ))
    ENNReal.ofReal_ne_top

lemma normalizedGraphDensity_pos
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)
    (x : V → Ω) :
    0 < normalizedGraphDensity (H := H) W x :=
  ENNReal.toReal_pos
    (normalizedGraphENN_ne_zero (H := H) W hδpos hδ x)
    (normalizedGraphENN_ne_top (H := H) W hδpos hδ x)

lemma integrable_normalizedGraphDensity
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    Integrable (normalizedGraphDensity (H := H) W)
      (assignmentMeasure V μ) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_normalizedGraphENN (H := H) W).aemeasurable
  rw [lintegral_normalizedGraphENN_eq_one
    (H := H) W hδpos hδ]
  exact ENNReal.one_ne_top

theorem integral_normalizedGraphDensity_eq_one
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ∫ x, normalizedGraphDensity (H := H) W x
        ∂assignmentMeasure V μ = 1 := by
  unfold normalizedGraphDensity
  rw [integral_toReal
    (measurable_normalizedGraphENN (H := H) W).aemeasurable
    (Filter.Eventually.of_forall fun x =>
      (normalizedGraphENN_ne_top (H := H) W hδpos hδ x).lt_top)]
  rw [lintegral_normalizedGraphENN_eq_one
    (H := H) W hδpos hδ]
  rfl

lemma normalizedGraphDensity_eq
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    (x : V → Ω) :
    normalizedGraphDensity (H := H) W x =
      graphWeight H W x / homDensity H W := by
  unfold normalizedGraphDensity normalizedGraphENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (homDensity_nonneg H W),
    ENNReal.toReal_ofReal (graphWeight_nonneg H W x)]
  rw [div_eq_mul_inv, mul_comm]

lemma normalizedGraphDensity_exists_lower_bound
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ∃ a > 0, ∀ x, a ≤ normalizedGraphDensity (H := H) W x := by
  refine ⟨δ ^ H.edgeFinset.card, pow_pos hδpos _, ?_⟩
  intro x
  rw [normalizedGraphDensity_eq]
  have htpos := homDensity_pos_of_lower_bound H W hδpos hδ
  apply (le_div_iff₀ htpos).2
  calc
    δ ^ H.edgeFinset.card * homDensity H W ≤
        δ ^ H.edgeFinset.card * 1 :=
      mul_le_mul_of_nonneg_left (homDensity_le_one H W)
        (pow_pos hδpos _).le
    _ = δ ^ H.edgeFinset.card := mul_one _
    _ ≤ graphWeight H W x :=
      graphWeight_lower_bound H W hδpos.le hδ x

lemma normalizedGraphDensity_exists_upper_bound
    [DecidableRel H.Adj] (W : Graphon Ω μ)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b) :
    ∃ b > 0, ∀ x, normalizedGraphDensity (H := H) W x ≤ b := by
  refine ⟨(δ ^ H.edgeFinset.card)⁻¹,
    inv_pos.mpr (pow_pos hδpos _), ?_⟩
  intro x
  rw [normalizedGraphDensity_eq]
  have htpos := homDensity_pos_of_lower_bound H W hδpos hδ
  have hfloor : 0 < δ ^ H.edgeFinset.card := pow_pos hδpos _
  apply (div_le_iff₀ htpos).2
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hfloor).2
  calc
    graphWeight H W x * δ ^ H.edgeFinset.card ≤
        1 * δ ^ H.edgeFinset.card :=
      mul_le_mul_of_nonneg_right (graphWeight_le_one H W x)
        hfloor.le
    _ = δ ^ H.edgeFinset.card := one_mul _
    _ ≤ homDensity H W :=
      homDensity_lower_bound H W hδpos.le hδ

lemma normalizedBagNewDensity_eq
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    D.normalizedBagNewDensity W i x =
      (D.bagNewMarginalENN W i x).toReal / cliqueDensity r W := by
  unfold normalizedBagNewDensity normalizedBagNewENN cliqueMassENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (cliqueDensity_nonneg r W),
    div_eq_mul_inv, mul_comm]

lemma normalizedSeparatorDensity_eq
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    D.normalizedSeparatorDensity W i x =
      cliqueWeightOn (D.separator i) W x /
        cliqueDensity (D.separator i).card W := by
  unfold normalizedSeparatorDensity normalizedSeparatorENN
    separatorMassENN separatorWeightENN cliqueWeightOnENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal
      (cliqueDensity_nonneg (D.separator i).card W),
    ENNReal.toReal_ofReal
      (cliqueWeightOn_nonneg (D.separator i) W x),
    div_eq_mul_inv, mul_comm]

lemma normalizedBagNewDensity_exists_lower_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∃ a > 0, ∀ x, a ≤ D.normalizedBagNewDensity W i x := by
  refine ⟨δ ^ (pairsIn (D.bag i)).card, pow_pos hδpos _, ?_⟩
  intro x
  rw [D.normalizedBagNewDensity_eq]
  have htpos := cliqueDensity_pos_of_lower_bound r W hδpos hδ
  apply (le_div_iff₀ htpos).2
  calc
    δ ^ (pairsIn (D.bag i)).card * cliqueDensity r W ≤
        δ ^ (pairsIn (D.bag i)).card * 1 :=
      mul_le_mul_of_nonneg_left (cliqueDensity_le_one r W)
        (pow_pos hδpos _).le
    _ = δ ^ (pairsIn (D.bag i)).card := mul_one _
    _ ≤ (D.bagNewMarginalENN W i x).toReal := by
      have h := ENNReal.toReal_mono
        (D.bagNewMarginalENN_ne_top W i x)
        (D.bagNewMarginalENN_lower_bound W hδpos.le hδ i x)
      simpa [ENNReal.toReal_ofReal (pow_pos hδpos _).le] using h

lemma normalizedBagNewDensity_exists_upper_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∃ b > 0, ∀ x, D.normalizedBagNewDensity W i x ≤ b := by
  let c := δ ^ (⊤ : SimpleGraph (Fin r)).edgeFinset.card
  have hcpos : 0 < c := pow_pos hδpos _
  refine ⟨c⁻¹, inv_pos.mpr hcpos, ?_⟩
  intro x
  rw [D.normalizedBagNewDensity_eq]
  have htpos := cliqueDensity_pos_of_lower_bound r W hδpos hδ
  apply (div_le_iff₀ htpos).2
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hcpos).2
  calc
    (D.bagNewMarginalENN W i x).toReal * c ≤ 1 * c :=
      mul_le_mul_of_nonneg_right
        (by
          simpa using ENNReal.toReal_mono ENNReal.one_ne_top
            (D.bagNewMarginalENN_le_one W i x))
        hcpos.le
    _ = c := one_mul _
    _ ≤ cliqueDensity r W :=
      homDensity_lower_bound (⊤ : SimpleGraph (Fin r))
        W hδpos.le hδ

lemma normalizedSeparatorDensity_exists_lower_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∃ a > 0, ∀ x, a ≤ D.normalizedSeparatorDensity W i x := by
  refine ⟨δ ^ (pairsIn (D.separator i)).card, pow_pos hδpos _, ?_⟩
  intro x
  rw [D.normalizedSeparatorDensity_eq]
  have htpos := cliqueDensity_pos_of_lower_bound
    (D.separator i).card W hδpos hδ
  apply (le_div_iff₀ htpos).2
  calc
    δ ^ (pairsIn (D.separator i)).card *
        cliqueDensity (D.separator i).card W ≤
        δ ^ (pairsIn (D.separator i)).card * 1 :=
      mul_le_mul_of_nonneg_left
        (cliqueDensity_le_one (D.separator i).card W)
        (pow_pos hδpos _).le
    _ = δ ^ (pairsIn (D.separator i)).card := mul_one _
    _ ≤ cliqueWeightOn (D.separator i) W x :=
      cliqueWeightOn_lower_bound
        (D.separator i) W hδpos.le hδ x

lemma normalizedSeparatorDensity_exists_upper_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∃ b > 0, ∀ x, D.normalizedSeparatorDensity W i x ≤ b := by
  let s := (D.separator i).card
  let c := δ ^ (⊤ : SimpleGraph (Fin s)).edgeFinset.card
  have hcpos : 0 < c := pow_pos hδpos _
  refine ⟨c⁻¹, inv_pos.mpr hcpos, ?_⟩
  intro x
  rw [D.normalizedSeparatorDensity_eq]
  have htpos := cliqueDensity_pos_of_lower_bound s W hδpos hδ
  apply (div_le_iff₀ htpos).2
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hcpos).2
  calc
    cliqueWeightOn (D.separator i) W x * c ≤ 1 * c :=
      mul_le_mul_of_nonneg_right
        (cliqueWeightOn_le_one (D.separator i) W x) hcpos.le
    _ = c := one_mul _
    _ ≤ cliqueDensity s W :=
      homDensity_lower_bound (⊤ : SimpleGraph (Fin s))
        W hδpos.le hδ

theorem lintegral_separatorTiltENN_eq_one
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∫⁻ x, D.separatorTiltENN W i x
        ∂assignmentMeasure V μ = 1 := by
  let x₀ : V → Ω := fun _ =>
    Classical.choice (nonempty_of_isProbabilityMeasure (α := Ω) μ)
  let k : (V → Ω) → ℝ≥0∞ := fun x =>
    (D.normalizedBagNewENN W i x)⁻¹ *
      D.normalizedSeparatorENN W i x
  have hkmeas : Measurable k :=
    (D.measurable_normalizedBagNewENN W i).inv.mul
      (D.measurable_normalizedSeparatorENN W i)
  have hkdep : FinsetDependsOn (D.separator i) k :=
    (D.normalizedBagNewENN_dependsOn W i).inv.mul
      (D.normalizedSeparatorENN_dependsOn W i)
  have hgself :
      lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
          (D.normalizedBagNewENN W i) =
        D.normalizedBagNewENN W i := by
    apply FinsetDependsOn.lmarginal_eq_self_of_disjoint
      (D.normalizedBagNewENN_dependsOn W i)
    exact (Finset.disjoint_sdiff
      (s := D.separator i) (t := Finset.univ)).symm
  have hmarg :
      lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
          (D.partialJunctionENN W m) =
        lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
          (D.normalizedBagNewENN W i) := by
    calc
      lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
          (D.partialJunctionENN W m) =
          D.normalizedBagNewENN W i :=
        D.partialJunctionENN_separatorMarginal W hδpos hδ i
      _ = lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
          (D.normalizedBagNewENN W i) := hgself.symm
  have htransfer :=
    lintegral_mul_eq_of_lmarginal_eq x₀
      (D.measurable_partialJunctionENN W m)
      (D.measurable_normalizedBagNewENN W i)
      hkmeas hkdep hmarg
  change
    (∫⁻ x, D.partialJunctionENN W m x * k x
      ∂Measure.pi (fun _ : V => μ)) = 1
  rw [htransfer]
  calc
    (∫⁻ x, D.normalizedBagNewENN W i x * k x
        ∂assignmentMeasure V μ) =
        ∫⁻ x, D.normalizedSeparatorENN W i x
          ∂assignmentMeasure V μ := by
      apply lintegral_congr
      intro x
      have hcancel :
          D.normalizedBagNewENN W i x *
              (D.normalizedBagNewENN W i x)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel
          (D.normalizedBagNewENN_ne_zero W hδpos hδ i x)
          (D.normalizedBagNewENN_ne_top W hδpos hδ i x)
      change D.normalizedBagNewENN W i x *
          ((D.normalizedBagNewENN W i x)⁻¹ *
            D.normalizedSeparatorENN W i x) =
        D.normalizedSeparatorENN W i x
      rw [← mul_assoc, hcancel, one_mul]
    _ = 1 :=
      D.lintegral_normalizedSeparatorENN_eq_one W hδpos hδ i

lemma separatorTiltENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.separatorTiltENN W i x ≠ 0 := by
  unfold separatorTiltENN
  exact mul_ne_zero
    (D.partialJunctionENN_ne_zero W hδpos hδ m x)
    (mul_ne_zero
      (ENNReal.inv_ne_zero.mpr
        (D.normalizedBagNewENN_ne_top W hδpos hδ i x))
      (D.normalizedSeparatorENN_ne_zero W hδpos hδ i x))

lemma separatorTiltENN_ne_top
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.separatorTiltENN W i x ≠ ∞ := by
  unfold separatorTiltENN
  exact ENNReal.mul_ne_top
    (D.partialJunctionENN_ne_top W hδpos hδ m x)
    (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr
        (D.normalizedBagNewENN_ne_zero W hδpos hδ i x))
      (D.normalizedSeparatorENN_ne_top W hδpos hδ i x))

lemma separatorTiltDensity_pos
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    0 < D.separatorTiltDensity W i x :=
  ENNReal.toReal_pos
    (D.separatorTiltENN_ne_zero W hδpos hδ i x)
    (D.separatorTiltENN_ne_top W hδpos hδ i x)

lemma separatorTiltDensity_eq
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    D.separatorTiltDensity W i x =
      D.junctionDensity W x *
        ((D.normalizedBagNewDensity W i x)⁻¹ *
          D.normalizedSeparatorDensity W i x) := by
  unfold separatorTiltDensity separatorTiltENN junctionDensity
    normalizedBagNewDensity normalizedSeparatorDensity
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]

lemma separatorTiltDensity_exists_lower_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∃ a > 0, ∀ x, a ≤ D.separatorTiltDensity W i x := by
  rcases D.junctionDensity_exists_lower_bound W hδpos hδ with
    ⟨p, hp, hpbound⟩
  rcases D.normalizedSeparatorDensity_exists_lower_bound
      W hδpos hδ i with ⟨s, hs, hsbound⟩
  rcases D.normalizedBagNewDensity_exists_upper_bound
      W hδpos hδ i with ⟨b, hb, hbbound⟩
  refine ⟨p * (b⁻¹ * s),
    mul_pos hp (mul_pos (inv_pos.mpr hb) hs), ?_⟩
  intro x
  rw [D.separatorTiltDensity_eq]
  have hbagpos : 0 < D.normalizedBagNewDensity W i x :=
    ENNReal.toReal_pos
      (D.normalizedBagNewENN_ne_zero W hδpos hδ i x)
      (D.normalizedBagNewENN_ne_top W hδpos hδ i x)
  have hinv :
      b⁻¹ ≤ (D.normalizedBagNewDensity W i x)⁻¹ :=
    (inv_le_inv₀ hb hbagpos).2 (hbbound x)
  exact mul_le_mul (hpbound x)
    (mul_le_mul hinv (hsbound x) hs.le
      (inv_pos.mpr hbagpos).le)
    (mul_nonneg (inv_pos.mpr hb).le hs.le)
    (D.junctionDensity_pos W hδpos hδ x).le

lemma separatorTiltDensity_exists_upper_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∃ b > 0, ∀ x, D.separatorTiltDensity W i x ≤ b := by
  rcases D.junctionDensity_exists_upper_bound W hδpos hδ with
    ⟨p, hp, hpbound⟩
  rcases D.normalizedSeparatorDensity_exists_upper_bound
      W hδpos hδ i with ⟨s, hs, hsbound⟩
  rcases D.normalizedBagNewDensity_exists_lower_bound
      W hδpos hδ i with ⟨a, ha, habound⟩
  refine ⟨p * (a⁻¹ * s),
    mul_pos hp (mul_pos (inv_pos.mpr ha) hs), ?_⟩
  intro x
  rw [D.separatorTiltDensity_eq]
  have hbagpos : 0 < D.normalizedBagNewDensity W i x :=
    ENNReal.toReal_pos
      (D.normalizedBagNewENN_ne_zero W hδpos hδ i x)
      (D.normalizedBagNewENN_ne_top W hδpos hδ i x)
  have hinv :
      (D.normalizedBagNewDensity W i x)⁻¹ ≤ a⁻¹ :=
    (inv_le_inv₀ hbagpos ha).2 (habound x)
  exact mul_le_mul (hpbound x)
    (mul_le_mul hinv (hsbound x)
      ENNReal.toReal_nonneg
      (inv_pos.mpr ha).le)
    (mul_nonneg (inv_pos.mpr hbagpos).le
      (ENNReal.toReal_nonneg))
    hp.le

lemma integrable_separatorTiltDensity
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    Integrable (D.separatorTiltDensity W i)
      (assignmentMeasure V μ) := by
  apply integrable_toReal_of_lintegral_ne_top
    (D.measurable_separatorTiltENN W i).aemeasurable
  rw [D.lintegral_separatorTiltENN_eq_one W hδpos hδ i]
  exact ENNReal.one_ne_top

theorem integral_separatorTiltDensity_eq_one
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∫ x, D.separatorTiltDensity W i x
        ∂assignmentMeasure V μ = 1 := by
  unfold separatorTiltDensity
  rw [integral_toReal
    (D.measurable_separatorTiltENN W i).aemeasurable
    (Filter.Eventually.of_forall fun x =>
      (D.separatorTiltENN_ne_top W hδpos hδ i x).lt_top)]
  rw [D.lintegral_separatorTiltENN_eq_one W hδpos hδ i]
  rfl

/-! ### The Gibbs gluing inequality for positive regularised kernels -/

theorem gibbs_junction_normalizedGraph_nonpos
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    ∫ x, D.junctionDensity W x *
        Real.log (normalizedGraphDensity (H := H) W x /
          D.junctionDensity W x)
        ∂assignmentMeasure V μ ≤ 0 := by
  apply integral_mul_log_div_nonpos_of_exists_bounds
    (D.measurable_junctionDensity W)
    (measurable_normalizedGraphDensity (H := H) W)
    (D.integrable_junctionDensity W hδpos hδ)
    (integrable_normalizedGraphDensity (H := H) W hδpos hδ)
    (D.integral_junctionDensity_eq_one W hδpos hδ)
    (integral_normalizedGraphDensity_eq_one
      (H := H) W hδpos hδ)
    (D.junctionDensity_exists_lower_bound W hδpos hδ)
    (normalizedGraphDensity_exists_lower_bound
      (H := H) W hδpos hδ)
    (D.junctionDensity_exists_upper_bound W hδpos hδ)
    (normalizedGraphDensity_exists_upper_bound
      (H := H) W hδpos hδ)

theorem gibbs_junction_separatorTilt_nonpos
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    ∫ x, D.junctionDensity W x *
        Real.log (D.separatorTiltDensity W i x /
          D.junctionDensity W x)
        ∂assignmentMeasure V μ ≤ 0 := by
  apply integral_mul_log_div_nonpos_of_exists_bounds
    (D.measurable_junctionDensity W)
    (D.measurable_separatorTiltDensity W i)
    (D.integrable_junctionDensity W hδpos hδ)
    (D.integrable_separatorTiltDensity W hδpos hδ i)
    (D.integral_junctionDensity_eq_one W hδpos hδ)
    (D.integral_separatorTiltDensity_eq_one W hδpos hδ i)
    (D.junctionDensity_exists_lower_bound W hδpos hδ)
    (D.separatorTiltDensity_exists_lower_bound W hδpos hδ i)
    (D.junctionDensity_exists_upper_bound W hδpos hδ)
    (D.separatorTiltDensity_exists_upper_bound W hδpos hδ i)

lemma separatorTilt_div_junction
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.separatorTiltDensity W i x / D.junctionDensity W x =
      D.normalizedSeparatorDensity W i x /
        D.normalizedBagNewDensity W i x := by
  rw [D.separatorTiltDensity_eq]
  have hp : D.junctionDensity W x ≠ 0 :=
    (D.junctionDensity_pos W hδpos hδ x).ne'
  field_simp

lemma separatorTilt_div_junction_eq_raw
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.separatorTiltDensity W i x / D.junctionDensity W x =
      (cliqueWeightOn (D.separator i) W x * cliqueDensity r W) /
        ((D.bagNewMarginalENN W i x).toReal *
          cliqueDensity (D.separator i).card W) := by
  rw [D.separatorTilt_div_junction W hδpos hδ i x,
    D.normalizedSeparatorDensity_eq,
    D.normalizedBagNewDensity_eq]
  have htr := cliqueDensity_pos_of_lower_bound r W hδpos hδ
  have hts := cliqueDensity_pos_of_lower_bound
    (D.separator i).card W hδpos hδ
  have hq := ENNReal.toReal_pos
    (D.bagNewMarginalENN_ne_zero W hδpos hδ i x)
    (D.bagNewMarginalENN_ne_top W i x)
  field_simp

lemma normalizedGraph_div_junction_eq_raw
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) (x : V → Ω) :
    normalizedGraphDensity (H := H) W x / D.junctionDensity W x =
      graphWeight H W x /
        (homDensity H W * D.junctionDensity W x) := by
  rw [normalizedGraphDensity_eq]
  ring

theorem prod_gibbs_ratios_eq_constant
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    (normalizedGraphDensity (H := H) W x /
        D.junctionDensity W x) *
        ∏ i : Fin m,
          (D.separatorTiltDensity W i x /
            D.junctionDensity W x) =
      (cliqueDensity r W) ^ m /
        (homDensity H W *
          ∏ i : Fin m, cliqueDensity (D.separator i).card W) := by
  rw [D.normalizedGraph_div_junction_eq_raw W x]
  simp_rw [D.separatorTilt_div_junction_eq_raw W hδpos hδ]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hP : D.junctionDensity W x ≠ 0 :=
    (D.junctionDensity_pos W hδpos hδ x).ne'
  have htH : homDensity H W ≠ 0 :=
    (homDensity_pos_of_lower_bound H W hδpos hδ).ne'
  have htr : cliqueDensity r W ≠ 0 :=
    (cliqueDensity_pos_of_lower_bound r W hδpos hδ).ne'
  have hq :
      (∏ i : Fin m, (D.bagNewMarginalENN W i x).toReal) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi =>
      (ENNReal.toReal_pos
        (D.bagNewMarginalENN_ne_zero W hδpos hδ i x)
        (D.bagNewMarginalENN_ne_top W i x)).ne'
  have hts :
      (∏ i : Fin m, cliqueDensity (D.separator i).card W) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi =>
      (cliqueDensity_pos_of_lower_bound
        (D.separator i).card W hδpos hδ).ne'
  have hfactor :=
    D.junctionDensity_mul_prod_bagNewMarginal
      W hδpos hδ x
  field_simp
  nlinarith

lemma integrable_gibbs_graph_integrand
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    Integrable (fun x => D.junctionDensity W x *
        Real.log (normalizedGraphDensity (H := H) W x /
          D.junctionDensity W x))
      (assignmentMeasure V μ) := by
  apply integrable_mul_log_div_of_exists_bounds
    (D.measurable_junctionDensity W)
    (measurable_normalizedGraphDensity (H := H) W)
    (D.junctionDensity_exists_lower_bound W hδpos hδ)
    (normalizedGraphDensity_exists_lower_bound
      (H := H) W hδpos hδ)
    (D.junctionDensity_exists_upper_bound W hδpos hδ)
    (normalizedGraphDensity_exists_upper_bound
      (H := H) W hδpos hδ)

lemma integrable_gibbs_separator_integrand
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    Integrable (fun x => D.junctionDensity W x *
        Real.log (D.separatorTiltDensity W i x /
          D.junctionDensity W x))
      (assignmentMeasure V μ) := by
  apply integrable_mul_log_div_of_exists_bounds
    (D.measurable_junctionDensity W)
    (D.measurable_separatorTiltDensity W i)
    (D.junctionDensity_exists_lower_bound W hδpos hδ)
    (D.separatorTiltDensity_exists_lower_bound W hδpos hδ i)
    (D.junctionDensity_exists_upper_bound W hδpos hδ)
    (D.separatorTiltDensity_exists_upper_bound W hδpos hδ i)

lemma sum_log_gibbs_ratios_eq_log_constant
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    Real.log (normalizedGraphDensity (H := H) W x /
        D.junctionDensity W x) +
        ∑ i : Fin m, Real.log
          (D.separatorTiltDensity W i x /
            D.junctionDensity W x) =
      Real.log ((cliqueDensity r W) ^ m /
        (homDensity H W *
          ∏ i : Fin m, cliqueDensity (D.separator i).card W)) := by
  have hgraph :
      normalizedGraphDensity (H := H) W x /
          D.junctionDensity W x ≠ 0 :=
    (div_pos
      (normalizedGraphDensity_pos (H := H) W hδpos hδ x)
      (D.junctionDensity_pos W hδpos hδ x)).ne'
  have hsep :
      ∀ i ∈ (Finset.univ : Finset (Fin m)),
        D.separatorTiltDensity W i x /
            D.junctionDensity W x ≠ 0 := by
    intro i hi
    exact (div_pos
      (D.separatorTiltDensity_pos W hδpos hδ i x)
      (D.junctionDensity_pos W hδpos hδ x)).ne'
  rw [← Real.log_prod hsep,
    ← Real.log_mul hgraph (Finset.prod_ne_zero_iff.mpr hsep)]
  exact congrArg Real.log
    (D.prod_gibbs_ratios_eq_constant W hδpos hδ x)

theorem log_gluing_ratio_nonpos
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    Real.log ((cliqueDensity r W) ^ m /
        (homDensity H W *
          ∏ i : Fin m, cliqueDensity (D.separator i).card W)) ≤ 0 := by
  let g₀ : (V → Ω) → ℝ := fun x =>
    D.junctionDensity W x *
      Real.log (normalizedGraphDensity (H := H) W x /
        D.junctionDensity W x)
  let g : Fin m → (V → Ω) → ℝ := fun i x =>
    D.junctionDensity W x *
      Real.log (D.separatorTiltDensity W i x /
        D.junctionDensity W x)
  have hg₀int : Integrable g₀ (assignmentMeasure V μ) :=
    D.integrable_gibbs_graph_integrand W hδpos hδ
  have hgint : ∀ i : Fin m, Integrable (g i) (assignmentMeasure V μ) :=
    fun i => D.integrable_gibbs_separator_integrand W hδpos hδ i
  have hsumInt :
      Integrable (fun x => ∑ i : Fin m, g i x)
        (assignmentMeasure V μ) :=
    integrable_finsetSum _ fun i hi => hgint i
  have hnonpos :
      (∫ x, g₀ x ∂assignmentMeasure V μ) +
          ∑ i : Fin m, ∫ x, g i x ∂assignmentMeasure V μ ≤ 0 := by
    apply add_nonpos
    · exact D.gibbs_junction_normalizedGraph_nonpos W hδpos hδ
    · exact Finset.sum_nonpos fun i hi =>
        D.gibbs_junction_separatorTilt_nonpos W hδpos hδ i
  have heq :
      (∫ x, g₀ x ∂assignmentMeasure V μ) +
          ∑ i : Fin m, ∫ x, g i x ∂assignmentMeasure V μ =
        Real.log ((cliqueDensity r W) ^ m /
          (homDensity H W *
            ∏ i : Fin m, cliqueDensity (D.separator i).card W)) := by
    rw [← integral_finsetSum (Finset.univ : Finset (Fin m))
      (fun i hi => hgint i),
      ← integral_add hg₀int hsumInt]
    calc
      (∫ x, g₀ x + ∑ i : Fin m, g i x
          ∂assignmentMeasure V μ) =
          ∫ x, D.junctionDensity W x *
            Real.log ((cliqueDensity r W) ^ m /
              (homDensity H W *
                ∏ i : Fin m,
                  cliqueDensity (D.separator i).card W))
            ∂assignmentMeasure V μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        change D.junctionDensity W x *
            Real.log (normalizedGraphDensity (H := H) W x /
              D.junctionDensity W x) +
            ∑ i : Fin m, D.junctionDensity W x *
              Real.log (D.separatorTiltDensity W i x /
                D.junctionDensity W x) = _
        rw [← Finset.mul_sum, ← mul_add,
          D.sum_log_gibbs_ratios_eq_log_constant W hδpos hδ x]
      _ = Real.log ((cliqueDensity r W) ^ m /
          (homDensity H W *
            ∏ i : Fin m,
              cliqueDensity (D.separator i).card W)) := by
        rw [integral_mul_const]
        change (∫ a, D.junctionDensity W a
          ∂Measure.pi (fun _ : V => μ)) * _ = _
        rw [D.integral_junctionDensity_eq_one W hδpos hδ, one_mul]
  rwa [heq] at hnonpos

/-- Clique-tree gluing for a uniformly positive graphon. -/
theorem homDensity_mul_sep_ge_cliqueDensity_pow_of_lower_bound
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    (cliqueDensity r W) ^ m ≤
      homDensity H W *
        ∏ i : Fin m, cliqueDensity (D.separator i).card W := by
  have hlog := D.log_gluing_ratio_nonpos W hδpos hδ
  have hdenpos :
      0 < homDensity H W *
        ∏ i : Fin m, cliqueDensity (D.separator i).card W := by
    exact mul_pos
      (homDensity_pos_of_lower_bound H W hδpos hδ)
      (Finset.prod_pos fun i _ =>
        cliqueDensity_pos_of_lower_bound
          (D.separator i).card W hδpos hδ)
  have hratio :
      (cliqueDensity r W) ^ m /
          (homDensity H W *
            ∏ i : Fin m, cliqueDensity (D.separator i).card W) ≤ 1 := by
    exact (Real.log_nonpos_iff (div_nonneg
      (pow_nonneg (cliqueDensity_nonneg r W) _)
      hdenpos.le)).mp hlog
  exact (div_le_one hdenpos).mp hratio

/-- Explicit continuity estimate for the separator product under regularization. -/
theorem abs_prod_separatorDensity_regularize_sub_le
    (W : Graphon Ω μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(∏ i : Fin m,
          cliqueDensity (D.separator i).card
            (W.regularize ε hε0 hε1)) -
        ∏ i : Fin m, cliqueDensity (D.separator i).card W|
      ≤ ∑ i : Fin m,
          ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
            ε := by
  calc
    |(∏ i : Fin m,
          cliqueDensity (D.separator i).card
            (W.regularize ε hε0 hε1)) -
        ∏ i : Fin m, cliqueDensity (D.separator i).card W|
        ≤ ∑ i : Fin m,
          |cliqueDensity (D.separator i).card
              (W.regularize ε hε0 hε1) -
            cliqueDensity (D.separator i).card W| := by
              apply abs_finset_prod_sub_prod_le_sum_abs
              · exact fun i _ => cliqueDensity_nonneg _ _
              · exact fun i _ => cliqueDensity_le_one _ _
              · exact fun i _ => cliqueDensity_nonneg _ _
              · exact fun i _ => cliqueDensity_le_one _ _
    _ ≤ ∑ i : Fin m,
          ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
            ε := by
      exact Finset.sum_le_sum fun i _ => by
        simpa [cliqueDensity] using
          abs_homDensity_regularize_sub_le
            (⊤ : SimpleGraph (Fin (D.separator i).card))
            W ε hε0 hε1

/-! ### Removing the regularisation by letting `ε → 0` -/

/-- Explicit continuity estimate for the full right side of clique-tree
gluing under regularization. -/
theorem abs_gluingRight_regularize_sub_le
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(homDensity H (W.regularize ε hε0 hε1) *
          ∏ i : Fin m, cliqueDensity (D.separator i).card
            (W.regularize ε hε0 hε1)) -
        homDensity H W *
          ∏ i : Fin m, cliqueDensity (D.separator i).card W|
      ≤ (H.edgeFinset.card : ℝ) * ε +
        ∑ i : Fin m,
          ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
            ε := by
  let Wε := W.regularize ε hε0 hε1
  let a := homDensity H Wε
  let b := homDensity H W
  let A := ∏ i : Fin m, cliqueDensity (D.separator i).card Wε
  let B := ∏ i : Fin m, cliqueDensity (D.separator i).card W
  have ha0 : 0 ≤ a := homDensity_nonneg H Wε
  have ha1 : a ≤ 1 := homDensity_le_one H Wε
  have hB0 : 0 ≤ B :=
    Finset.prod_nonneg fun i _ => cliqueDensity_nonneg _ W
  have hB1 : B ≤ 1 :=
    Finset.prod_le_one
      (fun i _ => cliqueDensity_nonneg _ W)
      (fun i _ => cliqueDensity_le_one _ W)
  have habs :
      |a * A - b * B| ≤ a * |A - B| + |a - b| * B := by
    calc
      |a * A - b * B| = |a * (A - B) + (a - b) * B| := by
        congr 1
        ring
      _ ≤ |a * (A - B)| + |(a - b) * B| := abs_add_le _ _
      _ = a * |A - B| + |a - b| * B := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hB0]
  change |a * A - b * B| ≤ _
  calc
    |a * A - b * B| ≤ a * |A - B| + |a - b| * B := habs
    _ ≤ 1 * (∑ i : Fin m,
          ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
            ε) +
        ((H.edgeFinset.card : ℝ) * ε) * 1 := by
      apply add_le_add
      · exact mul_le_mul ha1
          (D.abs_prod_separatorDensity_regularize_sub_le W ε hε0 hε1)
          (abs_nonneg _) zero_le_one
      · exact mul_le_mul
          (abs_homDensity_regularize_sub_le H W ε hε0 hε1)
          hB1 hB0
          (mul_nonneg (Nat.cast_nonneg _) hε0)
    _ = (H.edgeFinset.card : ℝ) * ε +
        ∑ i : Fin m,
          ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
            ε := by ring

/-- Cross-multiplied clique-tree gluing for an arbitrary graphon.  The
uniformly positive case is applied to `ε + (1-ε)W`; the explicit hom-density
continuity estimates then remove `ε`. -/
theorem homDensity_mul_sep_ge_cliqueDensity_pow
    [DecidableRel H.Adj] (W : Graphon Ω μ) :
    (cliqueDensity r W) ^ m ≤
      homDensity H W *
        ∏ i : Fin m, cliqueDensity (D.separator i).card W := by
  let C : ℝ :=
    (m : ℝ) *
        ((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) +
      (H.edgeFinset.card : ℝ) +
      ∑ i : Fin m,
        ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  apply le_of_forall_pos_le_add
  intro η hη
  let ε : ℝ := min 1 (η / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hεpos : 0 < ε := by
    exact lt_min zero_lt_one (div_pos hη hC1)
  have hε0 : 0 ≤ ε := hεpos.le
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεquot : ε ≤ η / (C + 1) := min_le_right _ _
  let Wε := W.regularize ε hε0 hε1
  have hWεlower : ∀ a b, ε ≤ Wε a b := by
    intro a b
    change ε ≤ ε + (1 - ε) * W a b
    exact le_add_of_nonneg_right <|
      mul_nonneg (sub_nonneg.mpr hε1) (W.nonneg a b)
  have hglue :
      (cliqueDensity r Wε) ^ m ≤
        homDensity H Wε *
          ∏ i : Fin m, cliqueDensity (D.separator i).card Wε := by
    exact D.homDensity_mul_sep_ge_cliqueDensity_pow_of_lower_bound
      Wε hεpos hWεlower
  have hleftAbs :
      |(cliqueDensity r Wε) ^ m - (cliqueDensity r W) ^ m| ≤
        (m : ℝ) *
          (((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) * ε) := by
    simpa [Wε, cliqueDensity] using
      abs_homDensity_regularize_pow_sub_le
        (⊤ : SimpleGraph (Fin r)) W ε hε0 hε1 m
  have hrightAbs :
      |(homDensity H Wε *
            ∏ i : Fin m, cliqueDensity (D.separator i).card Wε) -
          homDensity H W *
            ∏ i : Fin m, cliqueDensity (D.separator i).card W| ≤
        (H.edgeFinset.card : ℝ) * ε +
          ∑ i : Fin m,
            ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
              ε := by
    simpa [Wε] using D.abs_gluingRight_regularize_sub_le W ε hε0 hε1
  have hleft :
      (cliqueDensity r W) ^ m ≤
        (cliqueDensity r Wε) ^ m +
          (m : ℝ) *
            (((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) * ε) := by
    have := (abs_sub_le_iff.mp hleftAbs).2
    linarith
  have hright :
      homDensity H Wε *
          ∏ i : Fin m, cliqueDensity (D.separator i).card Wε ≤
        homDensity H W *
            ∏ i : Fin m, cliqueDensity (D.separator i).card W +
          ((H.edgeFinset.card : ℝ) * ε +
            ∑ i : Fin m,
              ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
                ε) := by
    have := (abs_sub_le_iff.mp hrightAbs).1
    linarith
  have herror :
      (m : ℝ) *
            (((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) * ε) +
          ((H.edgeFinset.card : ℝ) * ε +
            ∑ i : Fin m,
              ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
                ε) ≤ η := by
    have hfactor :
        (m : ℝ) *
              (((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) * ε) +
            ((H.edgeFinset.card : ℝ) * ε +
              ∑ i : Fin m,
                ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
                  ε) =
          C * ε := by
      rw [← Finset.sum_mul]
      dsimp [C]
      ring
    rw [hfactor]
    calc
      C * ε ≤ C * (η / (C + 1)) :=
        mul_le_mul_of_nonneg_left hεquot hC0
      _ ≤ (C + 1) * (η / (C + 1)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hη.le hC1.le)
      _ = η := by field_simp
  calc
    (cliqueDensity r W) ^ m
        ≤ (cliqueDensity r Wε) ^ m +
          (m : ℝ) *
            (((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) * ε) := hleft
    _ ≤ (homDensity H Wε *
            ∏ i : Fin m, cliqueDensity (D.separator i).card Wε) +
          (m : ℝ) *
            (((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) * ε) :=
      add_le_add_left hglue _
    _ ≤ (homDensity H W *
            ∏ i : Fin m, cliqueDensity (D.separator i).card W +
          ((H.edgeFinset.card : ℝ) * ε +
            ∑ i : Fin m,
              ((⊤ : SimpleGraph (Fin (D.separator i).card)).edgeFinset.card : ℝ) *
                ε)) +
          (m : ℝ) *
            (((⊤ : SimpleGraph (Fin r)).edgeFinset.card : ℝ) * ε) :=
      add_le_add_left hright _
    _ ≤ homDensity H W *
          ∏ i : Fin m, cliqueDensity (D.separator i).card W + η := by
      linarith

end PureCliqueTreeDecomp

end PureChordal
