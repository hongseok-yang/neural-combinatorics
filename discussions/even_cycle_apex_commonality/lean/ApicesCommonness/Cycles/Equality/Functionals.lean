import ApicesCommonness.Cycles.Main
import ApicesCommonness.Cycles.Equality.Spectral
import ApicesCommonness.Common.Transfer

/-!
# `L¹`-continuous graphon functionals

The equality proof transfers finite-host inequalities between `L¹`-continuous graphon
functionals with `le_of_step_graphons_cont` (`Common/Transfer.lean`).

The functionals: the signed densities `t(F, U)` (`signedDensity`, `U = 2W − 1`) and the colour
densities `t(F, S_σ)` (`colourDensity`), with their step values (the host densities of `U` and
`S_σ`) and `L¹`-Lipschitz bounds.  The scalars `m, b, c, q` of `def:integral-scalars` are signed
densities of an edge, a two-edge path, the four-cycle and the triangle with a pendant edge
(`graphonM`, `graphonB`, `graphonC`, `graphonQ`), and `X = 1 + 2m² + 8b + c + 4q`.
-/

open MeasureTheory

set_option linter.unusedSectionVars false

namespace ApicesCommonness

open Foundation SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

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

end ApicesCommonness
