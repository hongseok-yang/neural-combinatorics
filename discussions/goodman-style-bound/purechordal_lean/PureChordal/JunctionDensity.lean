import PureChordal.MarginalAlgebra

/-!
# The normalized junction-tree density

For each bag, divide its clique weight by the marginal over the vertices newly
introduced by that bag.  The resulting transition integrates to one in the new
coordinates.  Products over initial bag segments are the finite-dimensional
junction laws used in the entropy proof.
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

/-- The unnormalized clique weight of bag `i`. -/
noncomputable def bagWeightENN (W : Graphon Ω μ) (i : Fin m) :
    (V → Ω) → ℝ≥0∞ :=
  cliqueWeightOnENN (D.bag i) W

/-- The marginal of a bag weight over the vertices introduced at that bag. -/
noncomputable def bagNewMarginalENN (W : Graphon Ω μ) (i : Fin m) :
    (V → Ω) → ℝ≥0∞ :=
  lmarginal (fun _ : V => μ) (D.newVertices i) (D.bagWeightENN W i)

/-- Conditional extension factor for bag `i`. -/
noncomputable def bagTransitionENN (W : Graphon Ω μ) (i : Fin m) :
    (V → Ω) → ℝ≥0∞ :=
  fun x => (D.bagNewMarginalENN W i x)⁻¹ * D.bagWeightENN W i x

/-- Junction density formed from the bags with numerical index below `n`. -/
noncomputable def partialJunctionENN (W : Graphon Ω μ) (n : ℕ) :
    (V → Ω) → ℝ≥0∞ :=
  fun x => ∏ i ∈ D.bagIndicesLT n, D.bagTransitionENN W i x

/-- Common total mass of every `r`-clique bag. -/
noncomputable def cliqueMassENN
    (D : PureCliqueTreeDecomp H r m) (W : Graphon Ω μ) : ℝ≥0∞ :=
  ENNReal.ofReal (cliqueDensity r W)

/-- The normalized law carried by one bag. -/
noncomputable def normalizedBagENN (W : Graphon Ω μ) (i : Fin m) :
    (V → Ω) → ℝ≥0∞ :=
  fun x => (D.cliqueMassENN W)⁻¹ * D.bagWeightENN W i x

/-- Real-valued version of the completed junction law, used by Gibbs. -/
noncomputable def junctionDensity (W : Graphon Ω μ) :
    (V → Ω) → ℝ :=
  fun x => (D.partialJunctionENN W m x).toReal

lemma measurable_bagWeightENN (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.bagWeightENN W i) :=
  measurable_cliqueWeightOnENN (D.bag i) W

lemma measurable_bagNewMarginalENN (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.bagNewMarginalENN W i) :=
  (D.measurable_bagWeightENN W i).lmarginal _

lemma measurable_bagTransitionENN (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.bagTransitionENN W i) := by
  exact (D.measurable_bagNewMarginalENN W i).inv.mul
    (D.measurable_bagWeightENN W i)

lemma measurable_partialJunctionENN (W : Graphon Ω μ) (n : ℕ) :
    Measurable (D.partialJunctionENN W n) := by
  unfold partialJunctionENN
  exact Finset.measurable_fun_prod _ fun i _ =>
    D.measurable_bagTransitionENN W i

lemma measurable_normalizedBagENN (W : Graphon Ω μ) (i : Fin m) :
    Measurable (D.normalizedBagENN W i) := by
  exact measurable_const.mul (D.measurable_bagWeightENN W i)

lemma bag_sdiff_newVertices (i : Fin m) :
    D.bag i \ D.newVertices i = D.separator i := by
  ext v
  simp only [newVertices, Finset.mem_sdiff]
  constructor
  · rintro ⟨hvbag, hv⟩
    by_contra hvsep
    exact hv ⟨hvbag, hvsep⟩
  · intro hvsep
    refine ⟨D.separator_subset_bag i hvsep, ?_⟩
    rintro ⟨hvbag, hvnotsep⟩
    exact hvnotsep hvsep

lemma bagWeightENN_dependsOn (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (D.bag i) (D.bagWeightENN W i) := by
  intro x y hxy
  exact cliqueWeightOnENN_congr_on (D.bag i) W hxy

lemma bagNewMarginalENN_dependsOn (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (D.separator i) (D.bagNewMarginalENN W i) := by
  rw [← D.bag_sdiff_newVertices i]
  exact (D.bagWeightENN_dependsOn W i).lmarginal

lemma bagTransitionENN_dependsOn (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (D.bag i) (D.bagTransitionENN W i) := by
  apply FinsetDependsOn.mul
  · exact (D.bagNewMarginalENN_dependsOn W i).mono
      (D.separator_subset_bag i) |>.inv
  · exact D.bagWeightENN_dependsOn W i

lemma normalizedBagENN_dependsOn (W : Graphon Ω μ) (i : Fin m) :
    FinsetDependsOn (D.bag i) (D.normalizedBagENN W i) := by
  exact (FinsetDependsOn.const (D.bag i) (D.cliqueMassENN W)⁻¹).mul
    (D.bagWeightENN_dependsOn W i)

lemma partialJunctionENN_dependsOn (W : Graphon Ω μ) (n : ℕ) :
    FinsetDependsOn (D.accumulatedVerticesLT n)
      (D.partialJunctionENN W n) := by
  intro x y hxy
  unfold partialJunctionENN
  apply Finset.prod_congr rfl
  intro i hi
  apply D.bagTransitionENN_dependsOn W i
  intro v hvi
  apply hxy v
  rw [accumulatedVerticesLT, Finset.mem_biUnion]
  exact ⟨i, hi, hvi⟩

lemma partialJunctionENN_zero (W : Graphon Ω μ) :
    D.partialJunctionENN W 0 = fun _ => 1 := by
  funext x
  simp [partialJunctionENN, bagIndicesLT]

lemma partialJunctionENN_succ (W : Graphon Ω μ)
    {n : ℕ} (hn : n < m) :
    D.partialJunctionENN W (n + 1) =
      fun x => D.bagTransitionENN W ⟨n, hn⟩ x *
        D.partialJunctionENN W n x := by
  funext x
  unfold partialJunctionENN
  rw [D.bagIndicesLT_succ hn,
    Finset.prod_insert (D.index_not_mem_bagIndicesLT hn)]

lemma lmarginal_univ_bagWeightENN
    (W : Graphon Ω μ) (i : Fin m) :
    lmarginal (fun _ : V => μ) Finset.univ
        (D.bagWeightENN W i) =
      fun _ => D.cliqueMassENN W := by
  funext x
  rw [lmarginal_univ]
  unfold bagWeightENN cliqueWeightOnENN cliqueMassENN
  have h := ofReal_integral_eq_lintegral_ofReal
    (integrable_cliqueWeightOn (D.bag i) W)
    (Filter.Eventually.of_forall fun y =>
      cliqueWeightOn_nonneg (D.bag i) W y)
  rw [integral_cliqueWeightOn, D.bag_card i] at h
  exact h.symm

lemma newVertices_root :
    D.newVertices D.root = D.bag D.root := by
  simp [newVertices]

lemma bagNewMarginalENN_root
    (W : Graphon Ω μ) :
    D.bagNewMarginalENN W D.root =
      fun _ => D.cliqueMassENN W := by
  rw [bagNewMarginalENN, D.newVertices_root]
  calc
    lmarginal (fun _ : V => μ) (D.bag D.root)
        (D.bagWeightENN W D.root) =
        lmarginal (fun _ : V => μ) Finset.univ
          (D.bagWeightENN W D.root) := by
      unfold bagWeightENN
      simpa using
        (lmarginal_cliqueWeightOnENN_compl_eq_diff
          (S := ∅) (A := D.bag D.root)
          (by simp) W).symm
    _ = fun _ => D.cliqueMassENN W :=
      D.lmarginal_univ_bagWeightENN W D.root

lemma bagTransitionENN_root
    (W : Graphon Ω μ) :
    D.bagTransitionENN W D.root =
      D.normalizedBagENN W D.root := by
  funext x
  rw [bagTransitionENN, normalizedBagENN, D.bagNewMarginalENN_root W]

lemma bagNewMarginalENN_eq_separatorMarginal
    (W : Graphon Ω μ) (i : Fin m) :
    D.bagNewMarginalENN W i =
      lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
        (D.bagWeightENN W i) := by
  rw [bagNewMarginalENN, bagWeightENN, newVertices]
  exact (lmarginal_cliqueWeightOnENN_compl_eq_diff
    (D.separator_subset_bag i) W).symm

lemma bagNewMarginalENN_eq_parentSeparatorMarginal
    (W : Graphon Ω μ) {i : Fin m} (hi : i ≠ D.root) :
    D.bagNewMarginalENN W i =
      lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
        (D.bagWeightENN W (D.parent i)) := by
  rw [D.bagNewMarginalENN_eq_separatorMarginal W i]
  unfold bagWeightENN
  apply cliqueWeightOnENN_separatorMarginal_eq
  · exact D.separator_subset_bag i
  · rw [D.separator_of_ne_root hi]
    exact Finset.inter_subset_right
  · rw [D.bag_card i, D.bag_card (D.parent i)]

lemma bagNewMarginalENN_le_one
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    D.bagNewMarginalENN W i x ≤ 1 := by
  unfold bagNewMarginalENN bagWeightENN
  calc
    lmarginal (fun _ : V => μ) (D.newVertices i)
        (cliqueWeightOnENN (D.bag i) W) x ≤
        lmarginal (fun _ : V => μ) (D.newVertices i)
          (fun _ => 1) x :=
      lmarginal_mono (fun y => cliqueWeightOnENN_le_one (D.bag i) W y) x
    _ = 1 := by
      unfold lmarginal
      simp

lemma bagNewMarginalENN_lower_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    ENNReal.ofReal (δ ^ (pairsIn (D.bag i)).card) ≤
      D.bagNewMarginalENN W i x := by
  unfold bagNewMarginalENN bagWeightENN
  calc
    ENNReal.ofReal (δ ^ (pairsIn (D.bag i)).card) =
        lmarginal (fun _ : V => μ) (D.newVertices i)
          (fun _ => ENNReal.ofReal
            (δ ^ (pairsIn (D.bag i)).card)) x := by
      unfold lmarginal
      simp
    _ ≤ lmarginal (fun _ : V => μ) (D.newVertices i)
          (cliqueWeightOnENN (D.bag i) W) x :=
      lmarginal_mono
        (fun y => cliqueWeightOnENN_lower_bound
          (D.bag i) W hδ0 hδ y) x

lemma bagNewMarginalENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.bagNewMarginalENN W i x ≠ 0 := by
  have hlower := D.bagNewMarginalENN_lower_bound W hδpos.le hδ i x
  exact ne_of_gt <| lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr (pow_pos hδpos _)) hlower

lemma bagNewMarginalENN_ne_top
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    D.bagNewMarginalENN W i x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (D.bagNewMarginalENN_le_one W i x)

lemma bagWeightENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.bagWeightENN W i x ≠ 0 := by
  have hlower := cliqueWeightOnENN_lower_bound
    (D.bag i) W hδpos.le hδ x
  exact ne_of_gt <| lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr (pow_pos hδpos _)) hlower

lemma bagWeightENN_ne_top
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    D.bagWeightENN W i x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (cliqueWeightOnENN_le_one (D.bag i) W x)

lemma bagTransitionENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.bagTransitionENN W i x ≠ 0 := by
  unfold bagTransitionENN
  exact mul_ne_zero
    (ENNReal.inv_ne_zero.mpr (D.bagNewMarginalENN_ne_top W i x))
    (D.bagWeightENN_ne_zero W hδpos hδ i x)

lemma bagTransitionENN_ne_top
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    D.bagTransitionENN W i x ≠ ∞ := by
  unfold bagTransitionENN
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr
      (D.bagNewMarginalENN_ne_zero W hδpos hδ i x))
    (D.bagWeightENN_ne_top W i x)

lemma partialJunctionENN_ne_zero
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (n : ℕ) (x : V → Ω) :
    D.partialJunctionENN W n x ≠ 0 := by
  unfold partialJunctionENN
  exact Finset.prod_ne_zero_iff.mpr fun i hi =>
    D.bagTransitionENN_ne_zero W hδpos hδ i x

lemma partialJunctionENN_ne_top
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (n : ℕ) (x : V → Ω) :
    D.partialJunctionENN W n x ≠ ∞ := by
  unfold partialJunctionENN
  exact ENNReal.prod_ne_top fun i hi =>
    D.bagTransitionENN_ne_top W hδpos hδ i x

lemma junctionDensity_pos
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    0 < D.junctionDensity W x := by
  exact ENNReal.toReal_pos
    (D.partialJunctionENN_ne_zero W hδpos hδ m x)
    (D.partialJunctionENN_ne_top W hδpos hδ m x)

lemma bagTransition_toReal_lower_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    δ ^ (pairsIn (D.bag i)).card ≤
      (D.bagTransitionENN W i x).toReal := by
  have hqle :
      (D.bagNewMarginalENN W i x).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono
      ENNReal.one_ne_top
      (D.bagNewMarginalENN_le_one W i x)
  have hbin :
      δ ^ (pairsIn (D.bag i)).card ≤
        (D.bagWeightENN W i x).toReal := by
    have h := ENNReal.toReal_mono
      (D.bagWeightENN_ne_top W i x)
      (cliqueWeightOnENN_lower_bound
        (D.bag i) W hδpos.le hδ x)
    simpa [ENNReal.toReal_ofReal (pow_pos hδpos _).le] using h
  change δ ^ (pairsIn (D.bag i)).card ≤
    ((D.bagNewMarginalENN W i x)⁻¹ *
      D.bagWeightENN W i x).toReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  exact hbin.trans <| (le_mul_iff_one_le_left
    (ENNReal.toReal_pos
      (D.bagWeightENN_ne_zero W hδpos hδ i x)
      (D.bagWeightENN_ne_top W i x))).2 <|
        (one_le_inv₀
          (ENNReal.toReal_pos
            (D.bagNewMarginalENN_ne_zero W hδpos hδ i x)
            (D.bagNewMarginalENN_ne_top W i x))).2 hqle

lemma bagTransition_toReal_upper_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) (x : V → Ω) :
    (D.bagTransitionENN W i x).toReal ≤
      (δ ^ (pairsIn (D.bag i)).card)⁻¹ := by
  have hq :
      δ ^ (pairsIn (D.bag i)).card ≤
        (D.bagNewMarginalENN W i x).toReal := by
    have h := ENNReal.toReal_mono
      (D.bagNewMarginalENN_ne_top W i x)
      (D.bagNewMarginalENN_lower_bound W hδpos.le hδ i x)
    simpa [ENNReal.toReal_ofReal (pow_pos hδpos _).le] using h
  have hb :
      (D.bagWeightENN W i x).toReal ≤ 1 := by
    change (cliqueWeightOnENN (D.bag i) W x).toReal ≤ 1
    simpa using ENNReal.toReal_mono
      ENNReal.one_ne_top
      (cliqueWeightOnENN_le_one (D.bag i) W x)
  change
    ((D.bagNewMarginalENN W i x)⁻¹ *
      D.bagWeightENN W i x).toReal ≤ _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  calc
    (D.bagNewMarginalENN W i x).toReal⁻¹ *
        (D.bagWeightENN W i x).toReal ≤
        (D.bagNewMarginalENN W i x).toReal⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr <|
        ENNReal.toReal_nonneg)
    _ ≤ (δ ^ (pairsIn (D.bag i)).card)⁻¹ := by
      simpa only [mul_one] using (inv_le_inv₀
        (ENNReal.toReal_pos
          (D.bagNewMarginalENN_ne_zero W hδpos hδ i x)
          (D.bagNewMarginalENN_ne_top W i x))
        (pow_pos hδpos _)).2 hq

lemma junctionDensity_exists_lower_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    ∃ a > 0, ∀ x, a ≤ D.junctionDensity W x := by
  refine ⟨∏ i : Fin m, δ ^ (pairsIn (D.bag i)).card,
    Finset.prod_pos fun i _ => pow_pos hδpos _, ?_⟩
  intro x
  rw [junctionDensity, partialJunctionENN,
    D.bagIndicesLT_card, ENNReal.toReal_prod]
  exact Finset.prod_le_prod
    (fun i _ => (pow_pos hδpos _).le)
    (fun i _ =>
      D.bagTransition_toReal_lower_bound W hδpos hδ i x)

lemma junctionDensity_exists_upper_bound
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    ∃ b > 0, ∀ x, D.junctionDensity W x ≤ b := by
  refine ⟨∏ i : Fin m, (δ ^ (pairsIn (D.bag i)).card)⁻¹,
    Finset.prod_pos fun i _ => inv_pos.mpr (pow_pos hδpos _), ?_⟩
  intro x
  rw [junctionDensity, partialJunctionENN,
    D.bagIndicesLT_card, ENNReal.toReal_prod]
  exact Finset.prod_le_prod
    (fun i _ => ENNReal.toReal_nonneg)
    (fun i _ =>
      D.bagTransition_toReal_upper_bound W hδpos hδ i x)

theorem lmarginal_bagTransitionENN_eq_one
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    lmarginal (fun _ : V => μ) (D.newVertices i)
        (D.bagTransitionENN W i) =
      fun _ => 1 := by
  exact lmarginal_inv_marginal_mul_eq_one
    (D.newVertices i) (D.measurable_bagWeightENN W i)
    (D.bagNewMarginalENN_ne_zero W hδpos hδ i)
    (D.bagNewMarginalENN_ne_top W i)

lemma lmarginal_normalizedBagENN_compl
    (W : Graphon Ω μ) (i : Fin m) :
    lmarginal (fun _ : V => μ) (Finset.univ \ D.bag i)
        (D.normalizedBagENN W i) =
      D.normalizedBagENN W i := by
  apply FinsetDependsOn.lmarginal_eq_self_of_disjoint
    (D.normalizedBagENN_dependsOn W i)
  exact (Finset.disjoint_sdiff
    (s := D.bag i) (t := Finset.univ)).symm

lemma lmarginal_normalizedBagENN_separator
    (W : Graphon Ω μ) {i : Fin m} (hi : i ≠ D.root) :
    lmarginal (fun _ : V => μ) (D.bag (D.parent i) \ D.separator i)
        (D.normalizedBagENN W (D.parent i)) =
      fun x => (D.cliqueMassENN W)⁻¹ *
        D.bagNewMarginalENN W i x := by
  have hsepParent : D.separator i ⊆ D.bag (D.parent i) := by
    rw [D.separator_of_ne_root hi]
    exact Finset.inter_subset_right
  calc
    lmarginal (fun _ : V => μ)
        (D.bag (D.parent i) \ D.separator i)
        (D.normalizedBagENN W (D.parent i)) =
        lmarginal (fun _ : V => μ)
          (D.bag (D.parent i) \ D.separator i)
          (lmarginal (fun _ : V => μ)
            (Finset.univ \ D.bag (D.parent i))
            (D.normalizedBagENN W (D.parent i))) := by
      rw [D.lmarginal_normalizedBagENN_compl W (D.parent i)]
    _ = lmarginal (fun _ : V => μ)
          (Finset.univ \ D.separator i)
          (D.normalizedBagENN W (D.parent i)) := by
      exact (lmarginal_compl_subset hsepParent
        (D.measurable_normalizedBagENN W (D.parent i))).symm
    _ = fun x => (D.cliqueMassENN W)⁻¹ *
          lmarginal (fun _ : V => μ)
            (Finset.univ \ D.separator i)
            (D.bagWeightENN W (D.parent i)) x := by
      change lmarginal (fun _ : V => μ)
          (Finset.univ \ D.separator i)
          (fun x => (D.cliqueMassENN W)⁻¹ *
            D.bagWeightENN W (D.parent i) x) =
        fun x => (D.cliqueMassENN W)⁻¹ *
          lmarginal (fun _ : V => μ)
            (Finset.univ \ D.separator i)
            (D.bagWeightENN W (D.parent i)) x
      apply lmarginal_mul_of_left_updateInvariant
      · exact measurable_const
      · exact D.measurable_bagWeightENN W (D.parent i)
      · intro x y
        rfl
    _ = fun x => (D.cliqueMassENN W)⁻¹ *
          D.bagNewMarginalENN W i x := by
      rw [D.bagNewMarginalENN_eq_parentSeparatorMarginal W hi]

lemma lmarginal_normalizedBagENN_ownSeparator
    (W : Graphon Ω μ) (i : Fin m) :
    lmarginal (fun _ : V => μ) (D.bag i \ D.separator i)
        (D.normalizedBagENN W i) =
      fun x => (D.cliqueMassENN W)⁻¹ *
        D.bagNewMarginalENN W i x := by
  calc
    lmarginal (fun _ : V => μ) (D.bag i \ D.separator i)
        (D.normalizedBagENN W i) =
        lmarginal (fun _ : V => μ) (D.bag i \ D.separator i)
          (lmarginal (fun _ : V => μ) (Finset.univ \ D.bag i)
            (D.normalizedBagENN W i)) := by
      rw [D.lmarginal_normalizedBagENN_compl W i]
    _ = lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
          (D.normalizedBagENN W i) := by
      exact (lmarginal_compl_subset (D.separator_subset_bag i)
        (D.measurable_normalizedBagENN W i)).symm
    _ = fun x => (D.cliqueMassENN W)⁻¹ *
          lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
            (D.bagWeightENN W i) x := by
      change lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
          (fun x => (D.cliqueMassENN W)⁻¹ * D.bagWeightENN W i x) =
        fun x => (D.cliqueMassENN W)⁻¹ *
          lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
            (D.bagWeightENN W i) x
      apply lmarginal_mul_of_left_updateInvariant
      · exact measurable_const
      · exact D.measurable_bagWeightENN W i
      · intro x y
        rfl
    _ = fun x => (D.cliqueMassENN W)⁻¹ *
          D.bagNewMarginalENN W i x := by
      rw [D.bagNewMarginalENN_eq_separatorMarginal W i]

/-- Every bag already inserted into an initial junction product has its
normalized clique law as marginal. -/
theorem partialJunctionENN_bagMarginal
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    ∀ n : ℕ, n ≤ m → ∀ j : Fin m, j.val < n →
      lmarginal (fun _ : V => μ) (Finset.univ \ D.bag j)
          (D.partialJunctionENN W n) =
        D.normalizedBagENN W j := by
  intro n
  induction n with
  | zero =>
      intro hn j hj
      omega
  | succ n ih =>
      intro hn j hj
      have hnlt : n < m := by omega
      let i : Fin m := ⟨n, hnlt⟩
      rw [D.partialJunctionENN_succ W hnlt]
      by_cases hji : j = i
      · subst j
        by_cases hn0 : n = 0
        · subst n
          dsimp [i]
          have hiRoot : (⟨0, hnlt⟩ : Fin m) = D.root := by
            apply Fin.ext
            simpa using D.root_val.symm
          rw [D.partialJunctionENN_zero W]
          simp only [mul_one]
          rw [hiRoot, D.bagTransitionENN_root W]
          exact D.lmarginal_normalizedBagENN_compl W D.root
        · have hiRoot : i ≠ D.root := by
            intro hir
            have hval := congrArg Fin.val hir
            dsimp [i] at hval
            rw [D.root_val] at hval
            exact hn0 hval
          have hpOld : (D.parent i).val < n := by
            exact D.parent_lt i hiRoot
          have hparentMarg :
              lmarginal (fun _ : V => μ)
                  (Finset.univ \ D.bag (D.parent i))
                  (D.partialJunctionENN W n) =
                D.normalizedBagENN W (D.parent i) :=
            ih (by omega) (D.parent i) hpOld
          have hseparatorMarg :
              lmarginal (fun _ : V => μ)
                  (Finset.univ \ D.separator i)
                  (D.partialJunctionENN W n) =
                fun x => (D.cliqueMassENN W)⁻¹ *
                  D.bagNewMarginalENN W i x := by
            calc
              lmarginal (fun _ : V => μ)
                  (Finset.univ \ D.separator i)
                  (D.partialJunctionENN W n) =
                  lmarginal (fun _ : V => μ)
                    (D.bag (D.parent i) \ D.separator i)
                    (lmarginal (fun _ : V => μ)
                      (Finset.univ \ D.bag (D.parent i))
                      (D.partialJunctionENN W n)) := by
                apply lmarginal_compl_subset
                · rw [D.separator_of_ne_root hiRoot]
                  exact Finset.inter_subset_right
                · exact D.measurable_partialJunctionENN W n
              _ = lmarginal (fun _ : V => μ)
                    (D.bag (D.parent i) \ D.separator i)
                    (D.normalizedBagENN W (D.parent i)) := by
                rw [hparentMarg]
              _ = fun x => (D.cliqueMassENN W)⁻¹ *
                    D.bagNewMarginalENN W i x :=
                D.lmarginal_normalizedBagENN_separator W hiRoot
          have hbagMargToSep :
              lmarginal (fun _ : V => μ)
                  (Finset.univ \ D.bag i)
                  (D.partialJunctionENN W n) =
                lmarginal (fun _ : V => μ)
                  (Finset.univ \ D.separator i)
                  (D.partialJunctionENN W n) := by
            apply FinsetDependsOn.lmarginal_compl_eq_of_inter
              (D.partialJunctionENN_dependsOn W n)
              (D.measurable_partialJunctionENN W n)
              (D.separator_subset_bag i)
            simpa [i] using D.accumulatedVerticesLT_inter_bag i
          calc
            lmarginal (fun _ : V => μ) (Finset.univ \ D.bag i)
                (fun x => D.bagTransitionENN W i x *
                  D.partialJunctionENN W n x) =
                fun x => D.bagTransitionENN W i x *
                  lmarginal (fun _ : V => μ)
                    (Finset.univ \ D.bag i)
                    (D.partialJunctionENN W n) x := by
              apply lmarginal_mul_of_left_updateInvariant
              · exact D.measurable_bagTransitionENN W i
              · exact D.measurable_partialJunctionENN W n
              · exact (D.bagTransitionENN_dependsOn W i).updateInvariant_of_disjoint
                  ((Finset.disjoint_sdiff
                    (s := D.bag i) (t := Finset.univ)).symm)
            _ = fun x => D.bagTransitionENN W i x *
                  ((D.cliqueMassENN W)⁻¹ *
                    D.bagNewMarginalENN W i x) := by
              rw [hbagMargToSep, hseparatorMarg]
            _ = D.normalizedBagENN W i := by
              funext x
              have hq :
                  (D.bagNewMarginalENN W i x)⁻¹ *
                    D.bagNewMarginalENN W i x = 1 :=
                ENNReal.inv_mul_cancel
                  (D.bagNewMarginalENN_ne_zero W hδpos hδ i x)
                  (D.bagNewMarginalENN_ne_top W i x)
              change
                ((D.bagNewMarginalENN W i x)⁻¹ *
                    D.bagWeightENN W i x) *
                    ((D.cliqueMassENN W)⁻¹ *
                      D.bagNewMarginalENN W i x) =
                  (D.cliqueMassENN W)⁻¹ *
                    D.bagWeightENN W i x
              calc
                ((D.bagNewMarginalENN W i x)⁻¹ *
                    D.bagWeightENN W i x) *
                    ((D.cliqueMassENN W)⁻¹ *
                      D.bagNewMarginalENN W i x) =
                    (D.cliqueMassENN W)⁻¹ *
                      D.bagWeightENN W i x *
                      ((D.bagNewMarginalENN W i x)⁻¹ *
                        D.bagNewMarginalENN W i x) := by
                  ac_rfl
                _ = (D.cliqueMassENN W)⁻¹ *
                      D.bagWeightENN W i x := by
                  rw [hq, mul_one]
      · have hjOld : j.val < n := by
          by_contra hnot
          have hjval : j.val = n := by omega
          exact hji (Fin.ext hjval)
        calc
          lmarginal (fun _ : V => μ) (Finset.univ \ D.bag j)
              (fun x => D.bagTransitionENN W i x *
                D.partialJunctionENN W n x) =
              lmarginal (fun _ : V => μ) (Finset.univ \ D.bag j)
                (fun x => D.partialJunctionENN W n x *
                  D.bagTransitionENN W i x) := by
            congr 2
            funext x
            exact mul_comm _ _
          _ = lmarginal (fun _ : V => μ) (Finset.univ \ D.bag j)
                (D.partialJunctionENN W n) := by
            apply lmarginal_mul_preserve_of_fresh
            · exact D.measurable_partialJunctionENN W n
            · exact D.measurable_bagTransitionENN W i
            · exact D.partialJunctionENN_dependsOn W n
            · exact D.bag_subset_accumulatedVerticesLT hjOld
            · simpa [i] using D.newVertices_disjoint_accumulatedVerticesLT i
            · exact D.lmarginal_bagTransitionENN_eq_one W hδpos hδ i
          _ = D.normalizedBagENN W j := ih (by omega) j hjOld

theorem partialJunctionENN_separatorMarginal
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (i : Fin m) :
    lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
        (D.partialJunctionENN W m) =
      fun x => (D.cliqueMassENN W)⁻¹ *
        D.bagNewMarginalENN W i x := by
  have hbag :=
    D.partialJunctionENN_bagMarginal W hδpos hδ m le_rfl i i.isLt
  calc
    lmarginal (fun _ : V => μ) (Finset.univ \ D.separator i)
        (D.partialJunctionENN W m) =
        lmarginal (fun _ : V => μ) (D.bag i \ D.separator i)
          (lmarginal (fun _ : V => μ) (Finset.univ \ D.bag i)
            (D.partialJunctionENN W m)) := by
      exact lmarginal_compl_subset (D.separator_subset_bag i)
        (D.measurable_partialJunctionENN W m)
    _ = lmarginal (fun _ : V => μ) (D.bag i \ D.separator i)
          (D.normalizedBagENN W i) := by rw [hbag]
    _ = fun x => (D.cliqueMassENN W)⁻¹ *
          D.bagNewMarginalENN W i x :=
      D.lmarginal_normalizedBagENN_ownSeparator W i

theorem lmarginal_univ_partialJunctionENN_eq_one
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    lmarginal (fun _ : V => μ) Finset.univ
        (D.partialJunctionENN W m) =
      fun _ => 1 := by
  have hroot :
      lmarginal (fun _ : V => μ) (Finset.univ \ D.bag D.root)
          (D.partialJunctionENN W m) =
        D.normalizedBagENN W D.root :=
    D.partialJunctionENN_bagMarginal W hδpos hδ m le_rfl
      D.root D.root.isLt
  calc
    lmarginal (fun _ : V => μ) Finset.univ
        (D.partialJunctionENN W m) =
        lmarginal (fun _ : V => μ) (D.bag D.root)
          (lmarginal (fun _ : V => μ)
            (Finset.univ \ D.bag D.root)
            (D.partialJunctionENN W m)) := by
      simpa using lmarginal_compl_subset (μ := μ)
        (S := (∅ : Finset V)) (A := D.bag D.root)
        (Finset.empty_subset _) (D.measurable_partialJunctionENN W m)
    _ = lmarginal (fun _ : V => μ) (D.bag D.root)
          (D.normalizedBagENN W D.root) := by
      rw [hroot]
    _ = fun _ => 1 := by
      rw [← D.bagTransitionENN_root W, ← D.newVertices_root]
      exact D.lmarginal_bagTransitionENN_eq_one W hδpos hδ D.root

theorem lintegral_partialJunctionENN_eq_one
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    ∫⁻ x, D.partialJunctionENN W m x
        ∂Measure.pi (fun _ : V => μ) = 1 := by
  let x₀ : V → Ω :=
    fun _ => Classical.choice
      (nonempty_of_isProbabilityMeasure (α := Ω) μ)
  have h := congrFun
    (D.lmarginal_univ_partialJunctionENN_eq_one W hδpos hδ) x₀
  rw [lmarginal_univ] at h
  exact h

lemma measurable_junctionDensity (W : Graphon Ω μ) :
    Measurable (D.junctionDensity W) := by
  exact (D.measurable_partialJunctionENN W m).ennreal_toReal

lemma integrable_junctionDensity
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    Integrable (D.junctionDensity W)
      (Measure.pi fun _ : V => μ) := by
  apply integrable_toReal_of_lintegral_ne_top
    (D.measurable_partialJunctionENN W m).aemeasurable
  rw [D.lintegral_partialJunctionENN_eq_one W hδpos hδ]
  exact ENNReal.one_ne_top

theorem integral_junctionDensity_eq_one
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) :
    ∫ x, D.junctionDensity W x
        ∂Measure.pi (fun _ : V => μ) = 1 := by
  unfold junctionDensity
  rw [integral_toReal
    (D.measurable_partialJunctionENN W m).aemeasurable
    (ae_lt_top (D.measurable_partialJunctionENN W m) (by
      rw [D.lintegral_partialJunctionENN_eq_one W hδpos hδ]
      exact ENNReal.one_ne_top))]
  rw [D.lintegral_partialJunctionENN_eq_one W hδpos hδ]
  rfl

lemma bagWeightENN_toReal
    (W : Graphon Ω μ) (i : Fin m) (x : V → Ω) :
    (D.bagWeightENN W i x).toReal =
      cliqueWeightOn (D.bag i) W x := by
  rw [bagWeightENN, cliqueWeightOnENN,
    ENNReal.toReal_ofReal (cliqueWeightOn_nonneg (D.bag i) W x)]

/-- Before applying logarithms, the quotient cancellations are recorded in
cross-multiplied form. -/
theorem partialJunctionENN_mul_prod_bagNewMarginalENN
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    D.partialJunctionENN W m x *
        ∏ i : Fin m, D.bagNewMarginalENN W i x =
      ∏ i : Fin m, D.bagWeightENN W i x := by
  rw [partialJunctionENN, D.bagIndicesLT_card,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hq :
      (D.bagNewMarginalENN W i x)⁻¹ *
          D.bagNewMarginalENN W i x = 1 :=
    ENNReal.inv_mul_cancel
      (D.bagNewMarginalENN_ne_zero W hδpos hδ i x)
      (D.bagNewMarginalENN_ne_top W i x)
  change
    ((D.bagNewMarginalENN W i x)⁻¹ *
        D.bagWeightENN W i x) *
        D.bagNewMarginalENN W i x =
      D.bagWeightENN W i x
  calc
    ((D.bagNewMarginalENN W i x)⁻¹ *
        D.bagWeightENN W i x) *
        D.bagNewMarginalENN W i x =
      D.bagWeightENN W i x *
        ((D.bagNewMarginalENN W i x)⁻¹ *
          D.bagNewMarginalENN W i x) := by
      ac_rfl
    _ = D.bagWeightENN W i x := by rw [hq, mul_one]

/-- Pointwise factorization used in the entropy calculation.  It avoids all
division by cross-multiplying the raw separator marginals. -/
theorem junctionDensity_mul_prod_bagNewMarginal
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ a b, δ ≤ W a b) (x : V → Ω) :
    D.junctionDensity W x *
        ∏ i : Fin m, (D.bagNewMarginalENN W i x).toReal =
      graphWeight H W x *
        ∏ i : Fin m, cliqueWeightOn (D.separator i) W x := by
  have h := congrArg ENNReal.toReal
    (D.partialJunctionENN_mul_prod_bagNewMarginalENN
      W hδpos hδ x)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_prod] at h
  change
    D.junctionDensity W x *
        ∏ i : Fin m, (D.bagNewMarginalENN W i x).toReal =
      ∏ i : Fin m, (D.bagWeightENN W i x).toReal at h
  simp_rw [D.bagWeightENN_toReal W] at h
  rw [D.prod_cliqueWeightOn_bags W x] at h
  exact h

end PureCliqueTreeDecomp

end PureChordal
