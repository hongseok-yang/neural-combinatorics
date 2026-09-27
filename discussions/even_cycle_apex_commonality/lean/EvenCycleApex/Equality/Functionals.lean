import EvenCycleApex.Main
import EvenCycleApex.Equality.Spectral

/-!
# `L¹`-continuous graphon functionals

The equality proof (DEVIATIONS X4) transfers finite-host inequalities between graphon functionals
that are `L¹`-continuous (`L1ContAt`): Lipschitz functionals are continuous
(`L1ContAt.of_lipschitz`), and continuity survives pairing and composition with a function that is
continuous at the value (`L1ContAt.prod`, `L1ContAt.comp`).  `le_of_step_graphons_cont` is the
transfer: an inequality `F ≤ G` on every step graphon holds at every graphon at which `F` and `G`
are continuous.

The functionals: the signed densities `t(F, U)` (`signedDensity`, `U = 2W − 1`) and the colour
densities `t(F, S_σ)` (`colourDensity`), with their step values (the host densities of `U` and
`S_σ`) and `L¹`-Lipschitz bounds.  The scalars `m, b, c, q` of `def:integral-scalars` are signed
densities of an edge, a two-edge path, the four-cycle and the triangle with a pendant edge
(`graphonM`, `graphonB`, `graphonC`, `graphonQ`), and `X = 1 + 2m² + 8b + c + 4q`.
-/

open MeasureTheory

set_option linter.unusedSectionVars false

namespace EvenCycleApex

open Foundation SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Continuity and the transfer -/

/-- `L¹`-continuity of a graphon functional at `W` (tested on graphons). -/
def L1ContAt {α : Type*} [PseudoMetricSpace α] (μ : Measure Ω) (F : (Ω → Ω → ℝ) → α)
    (W : Ω → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ V, IsGraphon V μ → l1norm μ (fun x y => W x y - V x y) < δ →
    dist (F V) (F W) < ε

lemma L1ContAt.of_lipschitz {F : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ V, IsGraphon V μ → |F W - F V| ≤ C * l1norm μ (fun x y => W x y - V x y)) :
    L1ContAt μ F W := by
  intro ε hε
  refine ⟨ε / (C + 1), by positivity, fun V hV hδ => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have hl := l1norm_nonneg (μ := μ) (fun x y => W x y - V x y)
  calc |F W - F V| ≤ C * l1norm μ (fun x y => W x y - V x y) := h V hV
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hδ.le hC
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

lemma L1ContAt.const {α : Type*} [PseudoMetricSpace α] (a : α) (W : Ω → Ω → ℝ) :
    L1ContAt μ (fun _ => a) W :=
  fun ε hε => ⟨1, one_pos, fun _ _ _ => by simpa using hε⟩

lemma L1ContAt.prod {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {F : (Ω → Ω → ℝ) → α} {G : (Ω → Ω → ℝ) → β} {W : Ω → Ω → ℝ} (hF : L1ContAt μ F W)
    (hG : L1ContAt μ G W) : L1ContAt μ (fun V => (F V, G V)) W := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hF ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hG ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun V hV hδ => ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨h₁ V hV (lt_of_lt_of_le hδ (min_le_left _ _)),
    h₂ V hV (lt_of_lt_of_le hδ (min_le_right _ _))⟩

lemma L1ContAt.comp {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {F : (Ω → Ω → ℝ) → α} {W : Ω → Ω → ℝ} (hF : L1ContAt μ F W) {φ : α → β}
    (hφ : ContinuousAt φ (F W)) : L1ContAt μ (fun V => φ (F V)) W := by
  intro ε hε
  obtain ⟨η, hη, hφ'⟩ := Metric.continuousAt_iff.mp hφ ε hε
  obtain ⟨δ, hδ, hF'⟩ := hF η hη
  exact ⟨δ, hδ, fun V hV hδV => hφ' (hF' V hV hδV)⟩

/-- **Transfer of a closed inequality between `L¹`-continuous functionals.** -/
theorem le_of_step_graphons_cont {F G : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ}
    (hW : IsGraphon W μ) (hF : L1ContAt μ F W) (hG : L1ContAt μ G W)
    (hstep : ∀ V, IsGraphon V μ → IsStepKernel V → F V ≤ G V) : F W ≤ G W := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, h₁⟩ := hF (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hG (ε / 2) (by positivity)
  obtain ⟨V, hV, hVs, hclose⟩ := exists_stepGraphon_l1_close hW (lt_min hδ₁ hδ₂)
  have a₁ := h₁ V hV (lt_of_lt_of_le hclose (min_le_left _ _))
  have a₂ := h₂ V hV (lt_of_lt_of_le hclose (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at a₁ a₂
  have := hstep V hV hVs
  linarith

/-- The transfer, specialised to host values: if `F V = f(host)` and `G V = g(host)` on step
graphons and `f ≤ g` on every finite host, then `F W ≤ G W`. -/
theorem le_of_hosts_cont {F G : (Ω → Ω → ℝ) → ℝ} {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hF : L1ContAt μ F W) (hG : L1ContAt μ G W)
    (hstep : ∀ {d : ℕ} {σ : Ω → Fin d} (_hσ : Measurable σ) (M : Fin d → Fin d → ℝ)
      (_hsym : ∀ i j, M i j = M j i) (_h0 : ∀ i j, 0 ≤ M i j) (_h1 : ∀ i j, M i j ≤ 1)
      (V : Ω → Ω → ℝ), (∀ x y, V x y = M (σ x) (σ y)) → F V ≤ G V) : F W ≤ G W :=
  le_of_step_graphons_cont hW hF hG fun V hV hVs => by
    obtain ⟨d, σ, M, hσ, hVM, hsym, h0, h1⟩ := exists_host_of_isStepKernel hV hVs
    exact hstep hσ M hsym h0 h1 V hVM

/-! ### Signed and colour densities -/

lemma l1norm_signed_sub (W V : Ω → Ω → ℝ) :
    l1norm μ (fun x y => signedKernel W x y - signedKernel V x y)
      = 2 * l1norm μ (fun x y => W x y - V x y) := by
  have h : ∀ x y, |signedKernel W x y - signedKernel V x y| = 2 * |W x y - V x y| := fun x y => by
    simp only [signedKernel]
    rw [show 2 * W x y - 1 - (2 * V x y - 1) = 2 * (W x y - V x y) by ring, abs_mul,
      abs_two]
  simp only [l1norm, h, integral_const_mul]

lemma abs_signedKernel_le {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) (x y : Ω) :
    |signedKernel W x y| ≤ 1 := by
  have h0 := hW.nonneg x y
  have h1 := hW.le_one x y
  rw [signedKernel, abs_le]
  constructor <;> linarith

lemma measurable_signedKernel {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    Measurable (Function.uncurry (signedKernel W)) :=
  (measurable_const.mul hW.meas).sub measurable_const

/-- The signed density `t(F, U)` of `U = 2W − 1`. -/
noncomputable def signedDensity {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  homDensity F (signedKernel W) μ

theorem signedDensity_lipschitz {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {W V : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hV : IsGraphon V μ) :
    |signedDensity F μ W - signedDensity F μ V|
      ≤ 2 * (edgePairs F).card * l1norm μ (fun x y => W x y - V x y) := by
  have h := homDensity_L1_lipschitz (μ := μ) F (measurable_signedKernel hW)
    (measurable_signedKernel hV) le_rfl (abs_signedKernel_le hW) (abs_signedKernel_le hV)
  rw [one_pow, mul_one, l1norm_signed_sub] at h
  rw [signedDensity, signedDensity]
  linarith

lemma signedDensity_cont {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : L1ContAt μ (signedDensity F μ) W :=
  L1ContAt.of_lipschitz (by positivity) fun V hV => signedDensity_lipschitz F hW hV

theorem signedDensity_step {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] {d : ℕ}
    {σ : Ω → Fin d} (hσ : Measurable σ) (M : Fin d → Fin d → ℝ) (hsym : ∀ i j, M i j = M j i)
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i j, M i j ≤ 1) {V : Ω → Ω → ℝ}
    (hV : ∀ x y, V x y = M (σ x) (σ y)) :
    signedDensity F μ V = hostDensity (hostOfStep (μ := μ) hσ M hsym h0 h1).w F
      (hostOfStep (μ := μ) hσ M hsym h0 h1).U :=
  step_homDensity_eq_host F hσ _ fun x y => by simp only [signedKernel, hV]; rfl

/-- The colour density `t(F, S_σ)`, `S_σ = 1 + σU`. -/
noncomputable def colourDensity {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (σ : ℝ) (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  homDensity F (colourKernel σ (signedKernel W)) μ

theorem colourDensity_lipschitz {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {W V : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hV : IsGraphon V μ) :
    |colourDensity F σ μ W - colourDensity F σ μ V|
      ≤ (edgePairs F).card * 2 ^ ((edgePairs F).card - 1) * 2
          * l1norm μ (fun x y => W x y - V x y) := by
  have hb : ∀ {U : Ω → Ω → ℝ}, IsGraphon U μ → ∀ x y, |colourKernel σ (signedKernel U) x y| ≤ 2 :=
    fun hU x y => by
      have := abs_le.mp (abs_signedKernel_le hU x y)
      rw [colourKernel, abs_le]
      rcases hσ with rfl | rfl <;> constructor <;> linarith [this.1, this.2]
  have hm : ∀ {U : Ω → Ω → ℝ}, IsGraphon U μ →
      Measurable (Function.uncurry (colourKernel σ (signedKernel U))) := fun hU =>
    measurable_const.add (measurable_const.mul (measurable_signedKernel hU))
  have h := homDensity_L1_lipschitz (μ := μ) F (hm hW) (hm hV) (by norm_num) (hb hW) (hb hV)
  have hl : l1norm μ (fun x y => colourKernel σ (signedKernel W) x y - colourKernel σ (signedKernel V) x y)
      = 2 * l1norm μ (fun x y => W x y - V x y) := by
    rw [← l1norm_signed_sub]
    unfold l1norm
    congr 1
    funext x
    congr 1
    funext y
    show |1 + σ * signedKernel W x y - (1 + σ * signedKernel V x y)|
      = |signedKernel W x y - signedKernel V x y|
    rw [show 1 + σ * signedKernel W x y - (1 + σ * signedKernel V x y)
      = σ * (signedKernel W x y - signedKernel V x y) by ring, abs_mul]
    rcases hσ with rfl | rfl <;> simp
  rw [hl] at h
  rw [colourDensity, colourDensity]
  linarith

lemma colourDensity_cont {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    L1ContAt μ (colourDensity F σ μ) W :=
  L1ContAt.of_lipschitz (by positivity) fun V hV => colourDensity_lipschitz F hσ hW hV

theorem colourDensity_step {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] (c : ℝ)
    {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ) (M : Fin d → Fin d → ℝ)
    (hsym : ∀ i j, M i j = M j i) (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i j, M i j ≤ 1)
    {V : Ω → Ω → ℝ} (hV : ∀ x y, V x y = M (σ x) (σ y)) :
    colourDensity F c μ V = hostDensity (hostOfStep (μ := μ) hσ M hsym h0 h1).w F
      ((hostOfStep (μ := μ) hσ M hsym h0 h1).S c) :=
  step_homDensity_eq_host F hσ _ fun x y => by
    simp only [colourKernel, signedKernel, hV]; rfl

/-! ### The scalars `m, b, c, q, X` -/

/-- The graph on `Fin v` with the given (sorted) edge pairs. -/
def graphOf {v : ℕ} (E : Finset (Fin v × Fin v)) : SimpleGraph (Fin v) where
  Adj i j := i ≠ j ∧ ((i, j) ∈ E ∨ (j, i) ∈ E)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {v : ℕ} (E : Finset (Fin v × Fin v)) : DecidableRel (graphOf E).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ((i, j) ∈ E ∨ (j, i) ∈ E)))

/-- `m = t(K₂, U)`. -/
noncomputable def graphonM (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  signedDensity (graphOf ({(0, 1)} : Finset (Fin 2 × Fin 2))) μ W

/-- `b = t(P₂, U)`. -/
noncomputable def graphonB (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  signedDensity (graphOf ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3))) μ W

/-- `c = t(C₄, U)`. -/
noncomputable def graphonC (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  signedDensity (cycleGraph 4) μ W

/-- `q`, the density of the triangle with a pendant edge. -/
noncomputable def graphonQ (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  signedDensity (graphOf trianglePendantEdges) μ W

/-- `X = 1 + 2m² + 8b + c + 4q`. -/
noncomputable def graphonX (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  1 + 2 * graphonM μ W ^ 2 + 8 * graphonB μ W + graphonC μ W + 4 * graphonQ μ W

section Host

variable {d : ℕ} (K : FiniteKernel d)

lemma host_m : hostDensity K.w (graphOf ({(0, 1)} : Finset (Fin 2 × Fin 2))) K.U = K.m := by
  rw [hostDensity_eq_edgeDensity, show edgePairs (graphOf ({(0, 1)} : Finset (Fin 2 × Fin 2)))
    = {(0, 1)} by decide, ← K.m_eq_edgeDensity]

lemma host_b : hostDensity K.w (graphOf ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3))) K.U = K.b := by
  rw [hostDensity_eq_edgeDensity, show edgePairs (graphOf ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3)))
    = {(0, 1), (1, 2)} by decide, ← K.b_eq_edgeDensity]

lemma host_c : hostDensity K.w (cycleGraph 4) K.U = K.c := K.c_eq_hostDensity.symm

lemma host_q : hostDensity K.w (graphOf trianglePendantEdges) K.U = K.q := by
  rw [hostDensity_eq_edgeDensity, show edgePairs (graphOf trianglePendantEdges)
    = trianglePendantEdges by decide, ← K.q_eq_edgeDensity]

end Host

/-- The step values of `m, b, c, q, X`. -/
theorem graphonScalars_step {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ) (M : Fin d → Fin d → ℝ)
    (hsym : ∀ i j, M i j = M j i) (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i j, M i j ≤ 1)
    {V : Ω → Ω → ℝ} (hV : ∀ x y, V x y = M (σ x) (σ y)) :
    graphonM μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).m ∧
      graphonB μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).b ∧
      graphonC μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).c ∧
      graphonQ μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).q ∧
      graphonX μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).EPi 1 := by
  have hm : graphonM μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).m := by
    rw [graphonM, signedDensity_step _ hσ M hsym h0 h1 hV, host_m]
  have hb : graphonB μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).b := by
    rw [graphonB, signedDensity_step _ hσ M hsym h0 h1 hV, host_b]
  have hc : graphonC μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).c := by
    rw [graphonC, signedDensity_step _ hσ M hsym h0 h1 hV, host_c]
  have hq : graphonQ μ V = (hostOfStep (μ := μ) hσ M hsym h0 h1).q := by
    rw [graphonQ, signedDensity_step _ hσ M hsym h0 h1 hV, host_q]
  refine ⟨hm, hb, hc, hq, ?_⟩
  rw [graphonX, hm, hb, hc, hq, FiniteKernel.EPi_one, FiniteKernel.a]

lemma graphonM_cont {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : L1ContAt μ (graphonM μ) W :=
  signedDensity_cont _ hW
lemma graphonB_cont {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : L1ContAt μ (graphonB μ) W :=
  signedDensity_cont _ hW
lemma graphonC_cont {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : L1ContAt μ (graphonC μ) W :=
  signedDensity_cont _ hW
lemma graphonQ_cont {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : L1ContAt μ (graphonQ μ) W :=
  signedDensity_cont _ hW

lemma graphonX_cont {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) : L1ContAt μ (graphonX μ) W := by
  have h := ((graphonM_cont hW).prod ((graphonB_cont hW).prod
    ((graphonC_cont hW).prod (graphonQ_cont hW)))).comp
    (φ := fun p : ℝ × ℝ × ℝ × ℝ => 1 + 2 * p.1 ^ 2 + 8 * p.2.1 + p.2.2.1 + 4 * p.2.2.2)
    (by fun_prop)
  exact h

lemma normalizedApexDensity_cont {n k : ℕ} (hn : 3 ≤ n) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    L1ContAt μ (fun V => normalizedApexDensity V μ n k) W :=
  L1ContAt.of_lipschitz (by positivity) fun V hV => normalizedApexDensity_lipschitz hW hV hn

lemma normalizedCycleDensity_cont {n : ℕ} (hn : 3 ≤ n) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    L1ContAt μ (fun V => normalizedCycleDensity V μ n) W :=
  L1ContAt.of_lipschitz (by positivity) fun V hV => normalizedCycleDensity_lipschitz hW hV hn

end EvenCycleApex
