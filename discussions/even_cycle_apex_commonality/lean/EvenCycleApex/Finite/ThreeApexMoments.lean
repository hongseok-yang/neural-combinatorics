import EvenCycleApex.Finite.ThreeApexGraphs

/-!
# The three-apex moments are the certificate polynomials

Blueprint `def:three-apex-polynomial`, `def:majority`, `lem:codegree-moments` (`E Π₃ − Z₃ =
eval_U(P_mean,3)`) and the conditional graph expansion of `lem:GH`:

```
  𝓕 = 2Π₃ − D₃²,   𝒥₀ = E 𝓕 = eval_U(F₀),   𝒥_σ = E σ𝓕 = eval_U(F₁),   𝒥_𝒫 = E 𝒫𝓕 = eval_U(P_△ · F₀),
```

where `𝒫 = U₀₁ + U₀₂ + U₁₂ − U₀₁U₀₂U₁₂` is the majority polynomial of the apex triple.  Each is proved
pointwise in the six vertices (`polyAt`): the colour average of `∏_{E₃} S_σ` is the even part of
`E₃` (`polyAt_parityPoly_even`), and `P_△ · F₀` factors because the apex edges are disjoint from
`E₃` (`polyAt_mul`).
-/

open Finset

namespace EvenCycleApex

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

/-- `𝓕 = 2Π₃ − D₃²` (`def:three-apex-polynomial`; it may take either sign). -/
noncomputable def threeF (ω : Sample d 3) : ℝ := 2 * K.condPi ω - K.condD ω ^ 2

/-- `𝒥₀ = E 𝓕`. -/
noncomputable def J0 : ℝ := K.E K.threeF

/-- `𝒥_σ = E σ𝓕`. -/
noncomputable def Jσ : ℝ := K.E fun ω => colour ω.1 * K.threeF ω

/-- The majority polynomial `𝒫 = U₀₁ + U₀₂ + U₁₂ − U₀₁U₀₂U₁₂` of the apex triple. -/
def majority (z : Fin 3 → Fin d) : ℝ :=
  K.U (z 0) (z 1) + K.U (z 0) (z 2) + K.U (z 1) (z 2) -
    K.U (z 0) (z 1) * K.U (z 0) (z 2) * K.U (z 1) (z 2)

/-- `𝒥_𝒫 = E 𝒫𝓕`. -/
noncomputable def JP : ℝ := K.E fun ω => K.majority ω.2 * K.threeF ω

/-! ### Six-vertex forms -/

/-- `∏_{e ∈ E} S_σ(e)` with `S_σ = 1 + σU`, for the two colours. -/
private lemma prod_S_true (E : Finset (Fin 6 × Fin 6)) (x : Fin 6 → Fin d) :
    ∏ p ∈ E, K.S 1 (x p.1) (x p.2) = ∏ p ∈ E, (1 + K.U (x p.1) (x p.2)) := by
  simp [FiniteKernel.S_apply]

private lemma prod_S_false (E : Finset (Fin 6 × Fin 6)) (x : Fin 6 → Fin d) :
    ∏ p ∈ E, K.S (-1) (x p.1) (x p.2) = ∏ p ∈ E, (1 + -K.U (x p.1) (x p.2)) := by
  simp [FiniteKernel.S_apply]

/-- `E_z [G(z) Π₃(b, z)]` over six vertices. -/
lemma sum_condPi (G : (Fin 3 → Fin d) → ℝ) (b : Bool) :
    ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * (G z * K.condPi (b, z))
      = ∑ x : Fin 6 → Fin d, (∏ i, K.w (x i)) * G (apexOf x) *
          ∏ p ∈ pi3Edges, K.S (colour b) (x p.1) (x p.2) := by
  rw [← sum_three_apex_Pi K.w (K.S (colour b)) G]
  refine sum_congr rfl fun z _ => ?_
  simp only [condPi, condA, condH]
  ring

/-- `E_z [G(z) D₃(b, z)²]` over six vertices. -/
lemma sum_condD_sq (G : (Fin 3 → Fin d) → ℝ) (b : Bool) :
    ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * (G z * K.condD (b, z) ^ 2)
      = ∑ x : Fin 6 → Fin d, (∏ i, K.w (x i)) * G (apexOf x) *
          ∏ p ∈ d3Edges, K.S (colour b) (x p.1) (x p.2) := by
  rw [← sum_three_apex_D_sq K.w K.w_sum (K.S (colour b)) G]
  refine sum_congr rfl fun z _ => ?_
  simp only [condD, condH]
  ring

/-- `E_z [G(z) 𝓕(b, z)]` over six vertices. -/
lemma sum_threeF (G : (Fin 3 → Fin d) → ℝ) (b : Bool) :
    ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * (G z * K.threeF (b, z))
      = ∑ x : Fin 6 → Fin d, (∏ i, K.w (x i)) * G (apexOf x) *
          (2 * ∏ p ∈ pi3Edges, K.S (colour b) (x p.1) (x p.2)
            - ∏ p ∈ d3Edges, K.S (colour b) (x p.1) (x p.2)) := by
  have h1 := K.sum_condPi G b
  have h2 := K.sum_condD_sq G b
  have hl : ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * (G z * K.threeF (b, z))
      = 2 * ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * (G z * K.condPi (b, z))
        - ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * (G z * K.condD (b, z) ^ 2) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun z _ => by rw [threeF]; ring
  have hr : ∑ x : Fin 6 → Fin d, (∏ i, K.w (x i)) * G (apexOf x) *
        (2 * ∏ p ∈ pi3Edges, K.S (colour b) (x p.1) (x p.2)
          - ∏ p ∈ d3Edges, K.S (colour b) (x p.1) (x p.2))
      = 2 * ∑ x : Fin 6 → Fin d, (∏ i, K.w (x i)) * G (apexOf x) *
          ∏ p ∈ pi3Edges, K.S (colour b) (x p.1) (x p.2)
        - ∑ x : Fin 6 → Fin d, (∏ i, K.w (x i)) * G (apexOf x) *
          ∏ p ∈ d3Edges, K.S (colour b) (x p.1) (x p.2) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [hl, hr, h1, h2]

/-! ### The identifications -/

/-- The pointwise value of `F_ε` in terms of the two colour products. -/
private lemma polyAt_polyF_zero (x : Fin 6 → Fin d) :
    polyAt K.U (polyF 0) x
      = 2 * (((∏ p ∈ pi3Edges, (1 + K.U (x p.1) (x p.2))) + ∏ p ∈ pi3Edges, (1 + -K.U (x p.1) (x p.2))) / 2)
        - ((∏ p ∈ d3Edges, (1 + K.U (x p.1) (x p.2))) + ∏ p ∈ d3Edges, (1 + -K.U (x p.1) (x p.2))) / 2 := by
  rw [polyF, polyAt_append, polyAt_scale, polyAt_scale, polyAt_parityPoly_even,
    polyAt_parityPoly_even, maskEdges_edgesE_three, maskEdges_edgesB_three]
  push_cast
  ring

private lemma polyAt_polyF_one (x : Fin 6 → Fin d) :
    polyAt K.U (polyF 1) x
      = 2 * (((∏ p ∈ pi3Edges, (1 + K.U (x p.1) (x p.2))) - ∏ p ∈ pi3Edges, (1 + -K.U (x p.1) (x p.2))) / 2)
        - ((∏ p ∈ d3Edges, (1 + K.U (x p.1) (x p.2))) - ∏ p ∈ d3Edges, (1 + -K.U (x p.1) (x p.2))) / 2 := by
  rw [polyF, polyAt_append, polyAt_scale, polyAt_scale, polyAt_parityPoly_odd,
    polyAt_parityPoly_odd, maskEdges_edgesE_three, maskEdges_edgesB_three]
  push_cast
  ring

/-- **`𝒥₀ = eval_U(F₀)`.** -/
theorem J0_eq : K.J0 = evalPoly K (polyF 0) := by
  rw [J0, E_eq_colours, evalPoly_eq_sum_polyAt]
  have ht := K.sum_threeF (fun _ => 1) true
  have hf := K.sum_threeF (fun _ => 1) false
  simp only [one_mul, mul_one] at ht hf
  rw [ht, hf, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun x _ => ?_
  simp only [colour_true, colour_false]
  rw [polyAt_polyF_zero, prod_S_true, prod_S_true, prod_S_false,
    prod_S_false]
  ring

/-- **`𝒥_σ = eval_U(F₁)`.** -/
theorem Jσ_eq : K.Jσ = evalPoly K (polyF 1) := by
  rw [Jσ, E_eq_colours, evalPoly_eq_sum_polyAt]
  have ht := K.sum_threeF (fun _ => 1) true
  have hf := K.sum_threeF (fun _ => 1) false
  simp only [one_mul, mul_one] at ht hf
  have hc : ∀ b : Bool, ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * (colour b * K.threeF (b, z))
      = colour b * ∑ z : Fin 3 → Fin d, (∏ j, K.w (z j)) * K.threeF (b, z) := fun b => by
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by ring
  simp only at hc ⊢
  rw [hc true, hc false, ht, hf, colour_true, colour_false, one_mul, neg_one_mul, ← sub_eq_add_neg,
    ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [polyAt_polyF_one, prod_S_true, prod_S_true, prod_S_false,
    prod_S_false]
  ring

/-! ### The majority polynomial and `𝒥_𝒫` -/

lemma apexOf_zero (x : Fin 6 → Fin d) : apexOf x 0 = x 0 := rfl
lemma apexOf_one (x : Fin 6 → Fin d) : apexOf x 1 = x 1 := rfl
lemma apexOf_two (x : Fin 6 → Fin d) : apexOf x 2 = x 2 := rfl

/-- The pointwise value of `P_△` is the majority polynomial of the apices. -/
private lemma polyAt_polyPtri (x : Fin 6 → Fin d) : polyAt K.U polyPtri x = K.majority (apexOf x) := by
  have h01 : maskEdges (edgeMask [(0, 1)]) = {(0, 1)} := by decide +kernel
  have h02 : maskEdges (edgeMask [(0, 2)]) = {(0, 2)} := by decide +kernel
  have h12 : maskEdges (edgeMask [(1, 2)]) = {(1, 2)} := by decide +kernel
  have htri : maskEdges (edgeMask [(0, 1), (0, 2), (1, 2)]) = {(0, 1), (0, 2), (1, 2)} := by
    decide +kernel
  simp only [polyPtri, mono, polyAt, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, h01, h02, h12, htri, prod_singleton]
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton]
  simp only [majority, apexOf_zero, apexOf_one, apexOf_two]
  push_cast
  ring

/-- The apex edges of `P_△` are disjoint from the edges of `F₀`. -/
private lemma disjoint_polyPtri_polyF : ∀ p ∈ polyPtri, ∀ q ∈ polyF 0,
    Disjoint (maskEdges p.2) (maskEdges q.2) := by
  have hapex : ∀ p ∈ polyPtri, maskEdges p.2 ⊆ {(0, 1), (0, 2), (1, 2)} := by
    intro p hp
    simp only [polyPtri, mono, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | rfl) | rfl <;> decide +kernel
  have hE : ∀ q ∈ polyF 0, maskEdges q.2 ⊆ pi3Edges := by
    intro q hq
    simp only [polyF, polyScale, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · show maskEdges y.2 ⊆ pi3Edges
      rw [← maskEdges_edgesE_three]
      exact maskEdges_subset_of_mem_parityPoly hy
    · show maskEdges y.2 ⊆ pi3Edges
      refine (maskEdges_subset_of_mem_parityPoly hy).trans ?_
      rw [maskEdges_edgesB_three]
      decide
  intro p hp q hq
  refine Disjoint.mono (hapex p hp) (hE q hq) ?_
  decide

/-- **`𝒥_𝒫 = eval_U(P_△ · F₀)`.** -/
theorem JP_eq : K.JP = evalPoly K (polyMul polyPtri (polyF 0)) := by
  rw [JP, E_eq_colours, evalPoly_eq_sum_polyAt]
  have ht := K.sum_threeF K.majority true
  have hf := K.sum_threeF K.majority false
  rw [ht, hf, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun x _ => ?_
  simp only [colour_true, colour_false]
  rw [polyAt_mul K.U disjoint_polyPtri_polyF, polyAt_polyPtri, K.polyAt_polyF_zero, prod_S_true,
    prod_S_true, prod_S_false, prod_S_false]
  ring

/-- **`E Π₃ − Z₃ = eval_U(P_mean,3)`** (`lem:codegree-moments`, three apices). -/
theorem EPi_three_sub_Z_three : K.EPi 3 - K.Z 3 = evalPoly K targetMeanThree := by
  rw [EPi, Z, E_eq_colours, E_eq_colours, evalPoly_eq_sum_polyAt]
  have hpt := K.sum_condPi (fun _ => 1) true
  have hpf := K.sum_condPi (fun _ => 1) false
  have hdt := K.sum_condD_sq (fun _ => 1) true
  have hdf := K.sum_condD_sq (fun _ => 1) false
  simp only [one_mul, mul_one] at hpt hpf hdt hdf
  rw [hpt, hpf, hdt, hdf, div_sub_div_same, ← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib,
    sum_div]
  refine sum_congr rfl fun x _ => ?_
  simp only [colour_true, colour_false]
  rw [targetMeanThree, polyAt_append, polyAt_scale, polyAt_parityPoly_even, polyAt_parityPoly_even,
    maskEdges_edgesE_three, maskEdges_edgesB_three, prod_S_true, prod_S_true, prod_S_false,
    prod_S_false]
  push_cast
  ring

/-! ### The scalar masks of `def:certificate-targets` -/

lemma evalPoly_polyC : evalPoly K polyC = K.R 4 := by
  have hE : maskEdges (edgeMask [(0, 1), (1, 2), (2, 3), (0, 3)]) = castAddEdges 2 c4Edges := by
    decide +kernel
  rw [polyC, evalPoly_parityPoly_even, hE, edgeDensity_castAdd K.w K.w_sum,
    edgeDensity_castAdd K.w K.w_sum, R, hostDensity_eq_edgeDensity, hostDensity_eq_edgeDensity,
    edgePairs_cycleGraph_four]

lemma evalMask_M : evalMask K (edgeMask [(0, 1)]) = K.m := by
  have hE : maskEdges (edgeMask [(0, 1)]) = castAddEdges 4 ({(0, 1)} : Finset (Fin 2 × Fin 2)) := by
    decide +kernel
  rw [evalMask, hE, edgeDensity_castAdd K.w K.w_sum, m_eq_edgeDensity]

lemma evalMask_T : evalMask K (edgeMask [(0, 1), (0, 2), (1, 2)]) = K.τ := by
  have hE : maskEdges (edgeMask [(0, 1), (0, 2), (1, 2)]) = castAddEdges 3 c3Edges := by
    decide +kernel
  rw [evalMask, hE, edgeDensity_castAdd K.w K.w_sum, τ_eq_edgeDensity]

lemma evalMask_A : evalMask K (edgeMask [(0, 1), (2, 3)]) = K.a := by
  have hE : maskEdges (edgeMask [(0, 1), (2, 3)])
      = castAddEdges 2 ({(0, 1), (2, 3)} : Finset (Fin 4 × Fin 4)) := by
    decide +kernel
  rw [evalMask, hE, edgeDensity_castAdd K.w K.w_sum, matching4]

lemma evalMask_P3 : evalMask K (edgeMask [(0, 1), (1, 2), (2, 3)]) = K.p3 := by
  have hE : maskEdges (edgeMask [(0, 1), (1, 2), (2, 3)])
      = castAddEdges 2 ({(0, 1), (1, 2), (2, 3)} : Finset (Fin 4 × Fin 4)) := by
    decide +kernel
  rw [evalMask, hE, edgeDensity_castAdd K.w K.w_sum, p3_eq_edgeDensity]

lemma evalMask_MT : evalMask K (edgeMask [(0, 1), (2, 3), (2, 4), (3, 4)]) = K.m * K.τ := by
  have hE : maskEdges (edgeMask [(0, 1), (2, 3), (2, 4), (3, 4)])
      = castAddEdges 1 (castAddEdges 3 ({(0, 1)} : Finset (Fin 2 × Fin 2)) ∪ natAddEdges 2 c3Edges) := by
    decide +kernel
  rw [evalMask, hE, edgeDensity_castAdd K.w K.w_sum, edgeDensity_append, m_eq_edgeDensity,
    τ_eq_edgeDensity]

/-! ### `lem:GH` -/

/-- `G = 3𝒥₀ − 3R₄ + 𝒥_σ − 𝒥_𝒫 − 13m − τ − 12a + 4mτ − 12p₃`. -/
noncomputable def certG : ℝ :=
  3 * K.J0 - 3 * K.R 4 + K.Jσ - K.JP - 13 * K.m - K.τ - 12 * K.a + 4 * (K.m * K.τ) - 12 * K.p3

/-- `H = 6𝒥₀ − 6R₄ + 𝒥_σ + 𝒥_𝒫 − 19m − 23τ + 12a − 4mτ − 24p₃`. -/
noncomputable def certH : ℝ :=
  6 * K.J0 - 6 * K.R 4 + K.Jσ + K.JP - 19 * K.m - 23 * K.τ + 12 * K.a - 4 * (K.m * K.τ) - 24 * K.p3

lemma certG_eq : K.certG = evalPoly K targetNeg := by
  simp only [targetNeg, evalPoly_append, evalPoly_scale, evalPoly_mono, evalMask_M, evalMask_T,
    evalMask_A, evalMask_MT, evalMask_P3, evalPoly_polyC, ← K.J0_eq, ← K.Jσ_eq, ← K.JP_eq, certG]
  push_cast
  ring

lemma certH_eq : K.certH = evalPoly K targetPos := by
  simp only [targetPos, evalPoly_append, evalPoly_scale, evalPoly_mono, evalMask_M, evalMask_T,
    evalMask_A, evalMask_MT, evalMask_P3, evalPoly_polyC, ← K.J0_eq, ← K.Jσ_eq, ← K.JP_eq, certH]
  push_cast
  ring

/-- **`lem:GH`.**  `G ≥ 0` and `H ≥ 0` on every finite host (no sign condition on `m`). -/
theorem weighted_certificate_inequalities : 0 ≤ K.certG ∧ 0 ≤ K.certH := by
  obtain ⟨-, hneg, hpos⟩ := three_universal_graph_inequalities K
  exact ⟨K.certG_eq ▸ hneg, K.certH_eq ▸ hpos⟩

/-- `E Π₃ ≥ Z₃` (`cor:reference-mean`, the certificate part). -/
theorem EPi_three_ge_Z_three : K.Z 3 ≤ K.EPi 3 := by
  have h := (three_universal_graph_inequalities K).1
  rw [← K.EPi_three_sub_Z_three] at h
  linarith

end FiniteKernel

end EvenCycleApex
