import EvenCycleApex.Host.Defs
import EvenCycleApex.Foundation.Factored

/-!
# Step kernels are finite hosts

Blueprint `lem:step-matrix`, weighted version (plan D3).

* `step_homDensity_eq_host`: if `K x y = M (σ x) (σ y)` for a measurable `σ : Ω → Fin d`, then for
  **every** finite graph `F`, `t(F, K)` on `(Ω, μ)` equals the host density of `F` in `M` with the
  cell weights `wᵢ = μ(σ⁻¹{i})`.  The proof pushes `μ^{⊗v}` forward along `σ` coordinatewise and
  evaluates the integral over the finite space as a sum (the argument of the copied
  `cycleDensity_of_factored`, for an arbitrary edge set).
* `exists_host_of_isStepKernel`: a step graphon (`IsGraphon` + `IsStepKernel`, the output of
  `exists_stepGraphon_l1_close`) factors through a measurable map onto `Fin d` whose matrix is
  symmetric and `[0,1]`-valued at **every** entry.  Restricting the finite type of the step kernel to
  the range of its map makes every cell the image of a point of `Ω`, where the graphon's pointwise
  bounds apply.
-/

open MeasureTheory Finset

namespace EvenCycleApex

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The cell weights `wᵢ = μ(σ⁻¹{i})` of a measurable map to `Fin d`. -/
noncomputable def cellWeights {d : ℕ} (μ : Measure Ω) (σ : Ω → Fin d) : Fin d → ℝ :=
  fun i => (μ.map σ).real {i}

omit [IsProbabilityMeasure μ] in
lemma cellWeights_nonneg {d : ℕ} (σ : Ω → Fin d) (i : Fin d) : 0 ≤ cellWeights μ σ i :=
  measureReal_nonneg

lemma cellWeights_sum {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ) :
    ∑ i, cellWeights μ σ i = 1 := by
  haveI : IsProbabilityMeasure (μ.map σ) := Measure.isProbabilityMeasure_map hσ.aemeasurable
  simp only [cellWeights]
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

/-- **`lem:step-matrix`, weighted.**  The density of any finite graph in a step kernel is the
host density of its matrix, with the cell masses as weights. -/
theorem step_homDensity_eq_host {v d : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {σ : Ω → Fin d} (hσ : Measurable σ) (M : Fin d → Fin d → ℝ) {K : Ω → Ω → ℝ}
    (hK : ∀ x y, K x y = M (σ x) (σ y)) :
    homDensity F K μ = hostDensity (cellWeights μ σ) F M := by
  classical
  set ν : Measure (Fin d) := μ.map σ with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hσ.aemeasurable
  set G : (Fin v → Fin d) → ℝ := fun u => ∏ p ∈ edgePairs F, M (u p.1) (u p.2) with hG
  have hpres : MeasurePreserving (fun (x : Fin v → Ω) (i : Fin v) => σ (x i))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => ν) :=
    measurePreserving_pi _ _ fun _ => ⟨hσ, rfl⟩
  have h1 : homDensity F K μ = ∫ x, G (fun i => σ (x i)) ∂(Measure.pi fun _ => μ) := by
    rw [homDensity_eq_integral_edgeProd]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact Finset.prod_congr rfl fun p _ => hK _ _
  have hmap : ∫ u, G u ∂(Measure.pi fun _ => ν)
      = ∫ x, G (fun i => σ (x i)) ∂(Measure.pi fun _ => μ) := by
    rw [← hpres.map_eq]
    exact integral_map hpres.measurable.aemeasurable (measurable_of_finite G).aestronglyMeasurable
  rw [h1, ← hmap, integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hsingle : (Measure.pi fun _ : Fin v => ν) {u} = ∏ i, ν {u i} := by
    have huniv : ({u} : Set (Fin v → Fin d)) = Set.univ.pi fun i => {u i} := by
      ext w
      constructor
      · rintro rfl
        exact fun i _ => rfl
      · intro hw
        funext i
        exact hw i (Set.mem_univ i)
    rw [huniv, Measure.pi_pi]
  rw [smul_eq_mul]
  congr 1
  rw [Measure.real, hsingle, ENNReal.toReal_prod]
  rfl

omit [IsProbabilityMeasure μ] in
/-- A step graphon factors through a measurable map onto some `Fin d` with a symmetric,
`[0,1]`-valued matrix. -/
theorem exists_host_of_isStepKernel {V : Ω → Ω → ℝ} (hV : Foundation.IsGraphon V μ)
    (hstep : IsStepKernel V) :
    ∃ (d : ℕ) (σ : Ω → Fin d) (M : Fin d → Fin d → ℝ), Measurable σ ∧
      (∀ x y, V x y = M (σ x) (σ y)) ∧ (∀ i j, M i j = M j i) ∧
      (∀ i j, 0 ≤ M i j) ∧ (∀ i j, M i j ≤ 1) := by
  classical
  obtain ⟨ι, hfin, hms, hsing, τ, M₀, hτ, heq⟩ := hstep
  -- restrict to the range of `τ`, so that every cell contains a point of `Ω`
  set R := Set.range τ with hR
  haveI : Fintype R := Fintype.ofFinite R
  set e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R with he
  set σ : Ω → Fin (Fintype.card R) := fun x => e ⟨τ x, Set.mem_range_self x⟩ with hσdef
  set M : Fin (Fintype.card R) → Fin (Fintype.card R) → ℝ :=
    fun i j => M₀ (e.symm i).1 (e.symm j).1 with hMdef
  have hMσ : ∀ x y, M (σ x) (σ y) = V x y := by
    intro x y
    simp only [hMdef, hσdef, Equiv.symm_apply_apply]
    exact (heq x y).symm
  -- every index is the cell of some point
  have hsurj : ∀ i, ∃ x, σ x = i := by
    intro i
    obtain ⟨x, hx⟩ := (e.symm i).2
    refine ⟨x, ?_⟩
    simp only [hσdef]
    rw [show (⟨τ x, Set.mem_range_self x⟩ : R) = e.symm i from Subtype.ext hx]
    exact e.apply_symm_apply i
  refine ⟨Fintype.card R, σ, M, ?_, fun x y => (hMσ x y).symm, fun i j => ?_, fun i j => ?_,
    fun i j => ?_⟩
  · refine measurable_to_countable' fun i => ?_
    have : σ ⁻¹' {i} = τ ⁻¹' {(e.symm i).1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hσdef]
      constructor
      · intro h; rw [← h, e.symm_apply_apply]
      · intro h
        rw [show (⟨τ x, Set.mem_range_self x⟩ : R) = e.symm i from Subtype.ext h]
        exact e.apply_symm_apply i
    rw [this]
    exact hτ (measurableSet_singleton _)
  · obtain ⟨x, rfl⟩ := hsurj i
    obtain ⟨y, rfl⟩ := hsurj j
    rw [hMσ, hMσ, hV.symm]
  · obtain ⟨x, rfl⟩ := hsurj i
    obtain ⟨y, rfl⟩ := hsurj j
    rw [hMσ]; exact hV.nonneg x y
  · obtain ⟨x, rfl⟩ := hsurj i
    obtain ⟨y, rfl⟩ := hsurj j
    rw [hMσ]; exact hV.le_one x y

end EvenCycleApex
