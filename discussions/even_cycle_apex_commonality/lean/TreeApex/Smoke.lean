import EvenCycleApex.Graph.Lipschitz
import EvenCycleApex.Graph.DensityAlgebra
import EvenCycleApex.Host.Bridge
import EvenCycleApex.Host.EdgeDensity

/-!
# T0 smoke test: the imported even-cycle transfer pipeline

`smoke_density_near_host` exercises the four even-cycle facts the tree development rests on
(plan T-D3, T-D6): relabelling invariance (`homDensity_comap_equiv`), `L¹` step approximation
(`exists_stepGraphon_l1_close`), step graphons as weighted hosts (`exists_host_of_isStepKernel`,
`step_homDensity_eq_host`) and the `L¹`-Lipschitz bound (`homDensity_L1_lipschitz`): the density of
any relabelled graph in a graphon is within `e · ε` of a weighted host density with a symmetric
`[0,1]` kernel.
-/

open MeasureTheory

namespace TreeApex

open EvenCycleApex EvenCycleApex.Foundation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem smoke_density_near_host {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {v : ℕ}
    (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] (e : Fin v ≃ Fin v) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (w : Fin d → ℝ) (M : Fin d → Fin d → ℝ), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i j, M i j = M j i) ∧ (∀ i j, 0 ≤ M i j) ∧ (∀ i j, M i j ≤ 1) ∧
      |homDensity (F.comap e) W μ - hostDensity w F M| ≤ (edgePairs F).card * ε := by
  obtain ⟨V, hV, hVs, hclose⟩ := exists_stepGraphon_l1_close hW hε
  obtain ⟨d, σ, M, hσ, hVM, hsym, h0, h1⟩ := exists_host_of_isStepKernel hV hVs
  have hb : ∀ {U : Ω → Ω → ℝ}, IsGraphon U μ → ∀ x y, |U x y| ≤ 1 := fun hU x y => by
    rw [abs_le]; exact ⟨by linarith [hU.nonneg x y], hU.le_one x y⟩
  have hlip := homDensity_L1_lipschitz (μ := μ) F hW.meas hV.meas le_rfl (hb hW) (hb hV)
  rw [one_pow, mul_one] at hlip
  refine ⟨d, cellWeights μ σ, M, cellWeights_nonneg σ, cellWeights_sum hσ, hsym, h0, h1, ?_⟩
  rw [homDensity_comap_equiv F e hW.symm, ← step_homDensity_eq_host F hσ M hVM]
  calc |homDensity F W μ - homDensity F V μ|
      ≤ (edgePairs F).card * l1norm μ (fun x y => W x y - V x y) := hlip
    _ ≤ (edgePairs F).card * ε := by gcongr

end TreeApex
