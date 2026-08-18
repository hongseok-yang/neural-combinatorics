import Taeyoung.Methods.Atlas148.GeoMean
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Integral

/-!
# Atlas 148: the fractionally degree-weighted edge

The low interval needs two facts about the cube-root moment
`M = ∫ d^{1/3}` and the fractionally weighted edge

```
N = ∫∫ W(x,y)·d(x)^{1/3}d(y)^{1/3} dμ²,
```

namely `M³ ≤ p` and `N³ ≥ p⁵` — the note's Lemma 3.1 at `α = 1/3`, squared and
cubed so that everything downstream stays polynomial.  They are what
`LowScalar.paw_scalar_*` consume as `z ≤ p` and `p⁵ ≤ z²s³`, because the tilt
sends `z = M³` and `s = N/M²`, so `z²s³ = N³` identically.

The note derives `N ≥ p^{5/3}` from a three-factor Hölder inequality with the
unbounded quotients `W/d(x)`.  A shorter route uses one *two*-factor
Cauchy--Schwarz instead:

```
p² = (∫∫ W)² ≤ (∫∫ W/(u_xu_y))·(∫∫ W u_xu_y) ≤ M·N,
```

with `u = d^{1/3}`, the first factor bounded by `M` through arithmetic--
geometric mean and Fubini.  Combined with `M ≤ p^{1/3}` this gives
`p² ≤ p^{1/3}N`, hence `p⁵ ≤ N³`.  Unboundedness is handled exactly as in
`GeoMean.lean`, by shifting the degree to `d + δ³` and letting `δ → 0`; the
shift is written as a cube so that `(d+δ³)^{1/3} ≤ d^{1/3} + δ`.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Cube roots -/

lemma cube_rpow_third {a : ℝ} (ha : 0 ≤ a) : (a ^ ((1:ℝ)/3)) ^ (3:ℕ) = a := by
  rw [← Real.rpow_natCast (a ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul ha]
  norm_num

lemma rpow_third_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ ((1:ℝ)/3) ≤ a ^ ((1:ℝ)/3) + b ^ ((1:ℝ)/3) := by
  have hA : (0:ℝ) ≤ a ^ ((1:ℝ)/3) := Real.rpow_nonneg ha _
  have hB : (0:ℝ) ≤ b ^ ((1:ℝ)/3) := Real.rpow_nonneg hb _
  have hA3 := cube_rpow_third ha
  have hB3 := cube_rpow_third hb
  have hle : a + b ≤ (a ^ ((1:ℝ)/3) + b ^ ((1:ℝ)/3)) ^ (3:ℕ) := by
    nlinarith [hA3, hB3, mul_nonneg (mul_nonneg hA hA) hB,
      mul_nonneg (mul_nonneg hA hB) hB]
  calc (a + b) ^ ((1:ℝ)/3)
      ≤ ((a ^ ((1:ℝ)/3) + b ^ ((1:ℝ)/3)) ^ (3:ℕ)) ^ ((1:ℝ)/3) :=
        Real.rpow_le_rpow (by linarith) hle (by norm_num)
    _ = a ^ ((1:ℝ)/3) + b ^ ((1:ℝ)/3) := by
        rw [← Real.rpow_natCast (a ^ ((1:ℝ)/3) + b ^ ((1:ℝ)/3)) 3,
          ← Real.rpow_mul (by linarith)]
        norm_num

/-! ### The two quantities -/

/-- `M = ∫ d^{1/3}`. -/
noncomputable def cubeMoment (W : Graphon Ω μ) : ℝ := momentR W ((1:ℝ)/3)

/-- `N = ∫∫ W·d(x)^{1/3}d(y)^{1/3}`. -/
noncomputable def fracEdge (W : Graphon Ω μ) : ℝ :=
  ∫ q, W q.1 q.2 * (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3)) ∂(μ.prod μ)

lemma cubeMoment_nonneg (W : Graphon Ω μ) : 0 ≤ cubeMoment W :=
  integral_nonneg fun x ↦ degree_rpow_nonneg W _ x

lemma cubeMoment_le_one (W : Graphon Ω μ) : cubeMoment W ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd
    (measurable_degree_rpow W (by norm_num)) fun x ↦ ?_)
  rw [abs_of_nonneg (degree_rpow_nonneg W _ x)]
  exact degree_rpow_le_one W (by norm_num) x

lemma measurable_fracEdge_integrand (W : Graphon Ω μ) :
    Measurable fun q : Ω × Ω ↦
      W q.1 q.2 * (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3)) :=
  W.measurable.mul
    (((measurable_degree_rpow W (by norm_num)).comp measurable_fst).mul
      ((measurable_degree_rpow W (by norm_num)).comp measurable_snd))

lemma integrable_fracEdge (W : Graphon Ω μ) :
    Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3))) (μ.prod μ) := by
  refine integrable_prod_of_bdd (measurable_fracEdge_integrand W) (C := 1) fun q ↦ ?_
  have hd : 0 ≤ degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) :=
    mul_nonneg (degree_rpow_nonneg W _ _) (degree_rpow_nonneg W _ _)
  rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) hd)]
  exact mul_le_one₀ (W.le_one _ _) hd
    (mul_le_one₀ (degree_rpow_le_one W (by norm_num) _) (degree_rpow_nonneg W _ _)
      (degree_rpow_le_one W (by norm_num) _))

lemma fracEdge_nonneg (W : Graphon Ω μ) : 0 ≤ fracEdge W :=
  integral_nonneg fun q ↦ mul_nonneg (W.nonneg _ _)
    (mul_nonneg (degree_rpow_nonneg W _ _) (degree_rpow_nonneg W _ _))

/-! ### `M³ ≤ p`, by Jensen for the concave cube root -/

/-- **The cube-root moment is dominated by the cube root of the density.** -/
theorem cube_cubeMoment_le (W : Graphon Ω μ) :
    cubeMoment W ^ 3 ≤ cliqueDensity 2 W := by
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  have hj := ConcaveOn.le_map_integral (μ := μ) (s := Set.Ici (0:ℝ))
    (g := fun t : ℝ ↦ t ^ ((1:ℝ)/3)) (f := degree W)
    (Real.concaveOn_rpow (by norm_num) (by norm_num))
    ((Real.continuous_rpow_const (by norm_num)).continuousOn) isClosed_Ici
    (ae_of_all _ fun x ↦ degree_nonneg W x)
    (integrable_degree W) (integrable_degree_rpow W (by norm_num))
  rw [integral_degree] at hj
  have hM : cubeMoment W ≤ cliqueDensity 2 W ^ ((1:ℝ)/3) := hj
  calc cubeMoment W ^ 3 ≤ (cliqueDensity 2 W ^ ((1:ℝ)/3)) ^ (3:ℕ) :=
        pow_le_pow_left₀ (cubeMoment_nonneg W) hM 3
    _ = cliqueDensity 2 W := cube_rpow_third hp0

/-! ### The shifted cube root -/

section Shift

variable (W : Graphon Ω μ) {δ : ℝ}

/-- `u_δ(x) = (d(x) + δ³)^{1/3}`. -/
noncomputable def cbrtShift (W : Graphon Ω μ) (δ : ℝ) (x : Ω) : ℝ :=
  (degree W x + δ ^ 3) ^ ((1:ℝ)/3)

lemma cbrtShift_pos (hδ : 0 < δ) (x : Ω) : 0 < cbrtShift W δ x :=
  Real.rpow_pos_of_pos (by linarith [degree_nonneg W x, pow_pos hδ 3]) _

lemma cbrtShift_cube (hδ : 0 < δ) (x : Ω) :
    cbrtShift W δ x ^ (3:ℕ) = degree W x + δ ^ 3 :=
  cube_rpow_third (by linarith [degree_nonneg W x, pow_pos hδ 3])

lemma cbrtShift_ge (hδ : 0 < δ) (x : Ω) : δ ≤ cbrtShift W δ x := by
  have h : (δ ^ 3) ^ ((1:ℝ)/3) ≤ cbrtShift W δ x :=
    Real.rpow_le_rpow (by positivity) (by linarith [degree_nonneg W x]) (by norm_num)
  have he : (δ ^ 3) ^ ((1:ℝ)/3) = δ := by
    rw [← Real.rpow_natCast δ 3, ← Real.rpow_mul hδ.le]
    norm_num
  linarith [he ▸ h]

lemma cbrtShift_le (hδ : 0 < δ) (x : Ω) :
    cbrtShift W δ x ≤ degree W x ^ ((1:ℝ)/3) + δ := by
  have he : (δ ^ 3) ^ ((1:ℝ)/3) = δ := by
    rw [← Real.rpow_natCast δ 3, ← Real.rpow_mul hδ.le]
    norm_num
  have h := rpow_third_add_le (degree_nonneg W x)
    (by positivity : (0:ℝ) ≤ δ ^ 3)
  rw [he] at h
  rw [cbrtShift]
  exact h

lemma measurable_cbrtShift : Measurable (cbrtShift W δ) :=
  (Real.continuous_rpow_const (by norm_num)).measurable.comp
    ((measurable_degree W).add measurable_const)

/-- `ι_δ(x) = 1/u_δ(x)`, bounded by `1/δ`. -/
noncomputable def cbrtShiftInv (W : Graphon Ω μ) (δ : ℝ) (x : Ω) : ℝ :=
  (cbrtShift W δ x)⁻¹

lemma cbrtShiftInv_pos (hδ : 0 < δ) (x : Ω) : 0 < cbrtShiftInv W δ x :=
  inv_pos.mpr (cbrtShift_pos W hδ x)

lemma cbrtShiftInv_le (hδ : 0 < δ) (x : Ω) : cbrtShiftInv W δ x ≤ δ⁻¹ :=
  inv_anti₀ hδ (cbrtShift_ge W hδ x)

lemma measurable_cbrtShiftInv : Measurable (cbrtShiftInv W δ) :=
  (measurable_cbrtShift W).inv

lemma cbrtShiftInv_mul (hδ : 0 < δ) (x : Ω) :
    cbrtShiftInv W δ x * cbrtShift W δ x = 1 :=
  inv_mul_cancel₀ (ne_of_gt (cbrtShift_pos W hδ x))

/-- `ι²·d ≤ u`, the pointwise fact behind the Fubini bound. -/
lemma sq_cbrtShiftInv_mul_degree_le (hδ : 0 < δ) (x : Ω) :
    cbrtShiftInv W δ x ^ 2 * degree W x ≤ cbrtShift W δ x := by
  have hu := cbrtShift_pos W hδ x
  have hc := cbrtShift_cube W hδ x
  have hmul := cbrtShiftInv_mul W hδ x
  have hkey : cbrtShiftInv W δ x ^ 2 * cbrtShift W δ x ^ (3:ℕ) = cbrtShift W δ x := by
    calc cbrtShiftInv W δ x ^ 2 * cbrtShift W δ x ^ (3:ℕ)
        = (cbrtShiftInv W δ x * cbrtShift W δ x) ^ 2 * cbrtShift W δ x := by ring
      _ = cbrtShift W δ x := by rw [hmul, one_pow, one_mul]
  have hle : cbrtShiftInv W δ x ^ 2 * degree W x
      ≤ cbrtShiftInv W δ x ^ 2 * cbrtShift W δ x ^ (3:ℕ) := by
    rw [hc]
    exact mul_le_mul_of_nonneg_left
      (by linarith [pow_pos hδ 3] : degree W x ≤ degree W x + δ ^ 3) (sq_nonneg _)
  linarith [hkey ▸ hle]

end Shift

/-! ### The shifted Cauchy--Schwarz -/

set_option maxHeartbeats 1000000 in
/-- `p² ≤ (M + δ)(N + 2δ + δ²)` for every `0 < δ ≤ 1`. -/
theorem sq_le_shifted (W : Graphon Ω μ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    cliqueDensity 2 W ^ 2
      ≤ (cubeMoment W + δ) * (fracEdge W + 2 * δ + δ ^ 2) := by
  set c := δ⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hmi := measurable_cbrtShiftInv W (δ := δ)
  have hmu := measurable_cbrtShift W (δ := δ)
  have hi0 : ∀ x : Ω, 0 ≤ cbrtShiftInv W δ x := fun x ↦ (cbrtShiftInv_pos W hδ x).le
  have hu0 : ∀ x : Ω, 0 ≤ cbrtShift W δ x := fun x ↦ (cbrtShift_pos W hδ x).le
  have hub : ∀ x : Ω, cbrtShift W δ x ≤ 1 + δ := fun x ↦ by
    have := cbrtShift_le W hδ x
    have := degree_rpow_le_one W (by norm_num : (0:ℝ) ≤ 1/3) x
    linarith
  -- the weight `A = W·ι_xι_y`
  have hA0 : ∀ q : Ω × Ω, 0 ≤ W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2) :=
    fun q ↦ mul_nonneg (W.nonneg _ _) (mul_nonneg (hi0 _) (hi0 _))
  have hiA : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hmi.comp measurable_fst).mul (hmi.comp measurable_snd))) (C := c ^ 2) fun q ↦ ?_
    rw [abs_of_nonneg (hA0 q)]
    calc W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2)
        ≤ 1 * (c * c) :=
          mul_le_mul (W.le_one _ _) (mul_le_mul (cbrtShiftInv_le W hδ _)
            (cbrtShiftInv_le W hδ _) (hi0 _) hc0)
            (mul_nonneg (hi0 _) (hi0 _)) zero_le_one
      _ = c ^ 2 := by ring
  have hiU : Integrable (fun q : Ω × Ω ↦
      W q.1 q.2 * (cbrtShift W δ q.1 * cbrtShift W δ q.2)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (W.measurable.mul
      ((hmu.comp measurable_fst).mul (hmu.comp measurable_snd)))
      (C := (1 + δ) ^ 2) fun q ↦ ?_
    rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) (mul_nonneg (hu0 _) (hu0 _)))]
    calc W q.1 q.2 * (cbrtShift W δ q.1 * cbrtShift W δ q.2)
        ≤ 1 * ((1 + δ) * (1 + δ)) :=
          mul_le_mul (W.le_one _ _) (mul_le_mul (hub _) (hub _) (hu0 _) (by linarith))
            (mul_nonneg (hu0 _) (hu0 _)) zero_le_one
      _ = (1 + δ) ^ 2 := by ring
  have hiW : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) :=
    integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ by
      show |W q.1 q.2| ≤ 1
      rw [abs_of_nonneg (W.nonneg _ _)]; exact W.le_one _ _
  -- `Aη = W` and `Aη² = W·u_xu_y`
  have hAη : ∀ q : Ω × Ω,
      W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2) *
        (cbrtShift W δ q.1 * cbrtShift W δ q.2) = W q.1 q.2 := by
    intro q
    calc W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2) *
          (cbrtShift W δ q.1 * cbrtShift W δ q.2)
        = W q.1 q.2 * ((cbrtShiftInv W δ q.1 * cbrtShift W δ q.1) *
            (cbrtShiftInv W δ q.2 * cbrtShift W δ q.2)) := by ring
      _ = W q.1 q.2 := by
          rw [cbrtShiftInv_mul W hδ, cbrtShiftInv_mul W hδ, one_mul, mul_one]
  have hAη2 : ∀ q : Ω × Ω,
      W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2) *
        (cbrtShift W δ q.1 * cbrtShift W δ q.2) ^ 2
        = W q.1 q.2 * (cbrtShift W δ q.1 * cbrtShift W δ q.2) := by
    intro q
    calc W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2) *
          (cbrtShift W δ q.1 * cbrtShift W δ q.2) ^ 2
        = (W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2) *
            (cbrtShift W δ q.1 * cbrtShift W δ q.2)) *
            (cbrtShift W δ q.1 * cbrtShift W δ q.2) := by ring
      _ = _ := by rw [hAη q]
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ)
    (A := fun q : Ω × Ω ↦ W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2))
    (η := fun q : Ω × Ω ↦ cbrtShift W δ q.1 * cbrtShift W δ q.2)
    hiA (hiW.congr (ae_of_all _ fun q ↦ (hAη q).symm))
    (hiU.congr (ae_of_all _ fun q ↦ (hAη2 q).symm)) hA0
  rw [integral_congr_ae (ae_of_all _ hAη), integral_congr_ae (ae_of_all _ hAη2),
    integral_prod_edge] at hcs
  -- the first factor is at most `M + δ`
  have hfirst : (∫ q, W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2)
      ∂(μ.prod μ)) ≤ cubeMoment W + δ := by
    have hisq : Integrable (fun q : Ω × Ω ↦
        W q.1 q.2 * cbrtShiftInv W δ q.1 ^ 2) (μ.prod μ) := by
      refine integrable_prod_of_bdd (W.measurable.mul
        ((hmi.comp measurable_fst).pow_const 2)) (C := c ^ 2) fun q ↦ ?_
      rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) (sq_nonneg _))]
      calc W q.1 q.2 * cbrtShiftInv W δ q.1 ^ 2 ≤ 1 * c ^ 2 :=
            mul_le_mul (W.le_one _ _)
              (pow_le_pow_left₀ (hi0 _) (cbrtShiftInv_le W hδ _) 2) (sq_nonneg _)
              zero_le_one
        _ = c ^ 2 := one_mul _
    have hisq' : Integrable (fun q : Ω × Ω ↦
        W q.1 q.2 * cbrtShiftInv W δ q.2 ^ 2) (μ.prod μ) := by
      refine integrable_prod_of_bdd (W.measurable.mul
        ((hmi.comp measurable_snd).pow_const 2)) (C := c ^ 2) fun q ↦ ?_
      rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) (sq_nonneg _))]
      calc W q.1 q.2 * cbrtShiftInv W δ q.2 ^ 2 ≤ 1 * c ^ 2 :=
            mul_le_mul (W.le_one _ _)
              (pow_le_pow_left₀ (hi0 _) (cbrtShiftInv_le W hδ _) 2) (sq_nonneg _)
              zero_le_one
        _ = c ^ 2 := one_mul _
    have hsum : Integrable (fun q : Ω × Ω ↦
        (W q.1 q.2 * cbrtShiftInv W δ q.1 ^ 2 +
          W q.1 q.2 * cbrtShiftInv W δ q.2 ^ 2) / 2) (μ.prod μ) :=
      ((hisq.add hisq').div_const 2).congr (ae_of_all _ fun q ↦ rfl)
    have hamgm : (∫ q, W q.1 q.2 * (cbrtShiftInv W δ q.1 * cbrtShiftInv W δ q.2)
        ∂(μ.prod μ)) ≤ ∫ q, (W q.1 q.2 * cbrtShiftInv W δ q.1 ^ 2 +
          W q.1 q.2 * cbrtShiftInv W δ q.2 ^ 2) / 2 ∂(μ.prod μ) := by
      refine integral_mono hiA hsum fun q ↦ ?_
      nlinarith [sq_nonneg (cbrtShiftInv W δ q.1 - cbrtShiftInv W δ q.2),
        W.nonneg q.1 q.2]
    have hL : (∫ q, W q.1 q.2 * cbrtShiftInv W δ q.1 ^ 2 ∂(μ.prod μ))
        = ∫ x, cbrtShiftInv W δ x ^ 2 * degree W x ∂μ :=
      integral_edge_left W (hmi.pow_const 2) (C := c ^ 2) fun x ↦ by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hi0 x) (cbrtShiftInv_le W hδ x) 2
    have hR : (∫ q, W q.1 q.2 * cbrtShiftInv W δ q.2 ^ 2 ∂(μ.prod μ))
        = ∫ y, cbrtShiftInv W δ y ^ 2 * degree W y ∂μ :=
      integral_edge_snd W (hmi.pow_const 2) (C := c ^ 2) fun x ↦ by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hi0 x) (cbrtShiftInv_le W hδ x) 2
    have hbnd : (∫ x, cbrtShiftInv W δ x ^ 2 * degree W x ∂μ) ≤ cubeMoment W + δ := by
      have hi1 : Integrable (fun x ↦ cbrtShiftInv W δ x ^ 2 * degree W x) μ :=
        integrable_of_bdd ((hmi.pow_const 2).mul (measurable_degree W)) (C := c ^ 2)
          fun x ↦ by
            rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (degree_nonneg W x))]
            calc cbrtShiftInv W δ x ^ 2 * degree W x ≤ c ^ 2 * 1 :=
                  mul_le_mul (pow_le_pow_left₀ (hi0 x) (cbrtShiftInv_le W hδ x) 2)
                    (degree_le_one W x) (degree_nonneg W x) (by positivity)
              _ = c ^ 2 := mul_one _
      have hi2 : Integrable (fun x ↦ degree W x ^ ((1:ℝ)/3) + δ) μ :=
        (integrable_degree_rpow W (by norm_num)).add (integrable_const _)
      calc (∫ x, cbrtShiftInv W δ x ^ 2 * degree W x ∂μ)
          ≤ ∫ x, (degree W x ^ ((1:ℝ)/3) + δ) ∂μ :=
            integral_mono hi1 hi2 fun x ↦
              le_trans (sq_cbrtShiftInv_mul_degree_le W hδ x) (cbrtShift_le W hδ x)
        _ = cubeMoment W + δ := by
            rw [integral_add (integrable_degree_rpow W (by norm_num))
              (integrable_const _), integral_const]
            simp [cubeMoment, momentR]
    have hhalf : (∫ q, (W q.1 q.2 * cbrtShiftInv W δ q.1 ^ 2 +
        W q.1 q.2 * cbrtShiftInv W δ q.2 ^ 2) / 2 ∂(μ.prod μ))
        = ((∫ q, W q.1 q.2 * cbrtShiftInv W δ q.1 ^ 2 ∂(μ.prod μ)) +
            ∫ q, W q.1 q.2 * cbrtShiftInv W δ q.2 ^ 2 ∂(μ.prod μ)) / 2 := by
      rw [integral_div]
      congr 1
      exact integral_add hisq hisq'
    rw [hhalf, hL, hR] at hamgm
    linarith
  -- the second factor is at most `N + 2δ + δ²`
  have hsecond : (∫ q, W q.1 q.2 * (cbrtShift W δ q.1 * cbrtShift W δ q.2)
      ∂(μ.prod μ)) ≤ fracEdge W + 2 * δ + δ ^ 2 := by
    have hi2 : Integrable (fun q : Ω × Ω ↦
        W q.1 q.2 * (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3))
          + W q.1 q.2 * (2 * δ + δ ^ 2)) (μ.prod μ) :=
      ((integrable_fracEdge W).add (hiW.mul_const _)).congr (ae_of_all _ fun q ↦ rfl)
    have hmono : (∫ q, W q.1 q.2 * (cbrtShift W δ q.1 * cbrtShift W δ q.2)
        ∂(μ.prod μ)) ≤ ∫ q, (W q.1 q.2 *
          (degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3))
            + W q.1 q.2 * (2 * δ + δ ^ 2)) ∂(μ.prod μ) := by
      refine integral_mono hiU hi2 fun q ↦ ?_
      have h1 := cbrtShift_le W hδ q.1
      have h2 := cbrtShift_le W hδ q.2
      have hd1 := degree_rpow_nonneg W ((1:ℝ)/3) q.1
      have hd2 := degree_rpow_nonneg W ((1:ℝ)/3) q.2
      have he1 := degree_rpow_le_one W (by norm_num : (0:ℝ) ≤ 1/3) q.1
      have he2 := degree_rpow_le_one W (by norm_num : (0:ℝ) ≤ 1/3) q.2
      have hW := W.nonneg q.1 q.2
      have hprod : cbrtShift W δ q.1 * cbrtShift W δ q.2
          ≤ degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) + (2 * δ + δ ^ 2) := by
        nlinarith [hu0 q.1, hu0 q.2, hδ.le]
      nlinarith [mul_le_mul_of_nonneg_left hprod hW]
    rw [integral_add (integrable_fracEdge W) (hiW.mul_const _), integral_mul_const,
      integral_prod_edge, ← fracEdge] at hmono
    have hp1 : cliqueDensity 2 W ≤ 1 := cliqueDensity_le_one 2 W
    nlinarith [hmono, hδ.le, cliqueDensity_nonneg 2 W]
  -- combine
  have hnn : 0 ≤ ∫ q, W q.1 q.2 * (cbrtShift W δ q.1 * cbrtShift W δ q.2) ∂(μ.prod μ) :=
    integral_nonneg fun q ↦ mul_nonneg (W.nonneg _ _) (mul_nonneg (hu0 _) (hu0 _))
  have hMδ : 0 ≤ cubeMoment W + δ := by linarith [cubeMoment_nonneg W, hδ.le]
  nlinarith [hcs, hfirst, hsecond, hnn, hMδ]

/-! ### The two low-interval inputs -/

/-- `p² ≤ M·N`. -/
theorem sq_le_cubeMoment_mul_fracEdge (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 2 ≤ cubeMoment W * fracEdge W := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ := min 1 (ε / 7) with hδdef
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδe : 7 * δ ≤ ε := by
    have := min_le_right (1:ℝ) (ε / 7)
    linarith [this]
  have hM1 : cubeMoment W ≤ 1 := cubeMoment_le_one W
  have hM0 : 0 ≤ cubeMoment W := cubeMoment_nonneg W
  have hN0 : 0 ≤ fracEdge W := fracEdge_nonneg W
  have hN1 : fracEdge W ≤ 1 := by
    refine le_of_abs_le (abs_integral_le_of_bdd (measurable_fracEdge_integrand W)
      fun q ↦ ?_)
    have hd : 0 ≤ degree W q.1 ^ ((1:ℝ)/3) * degree W q.2 ^ ((1:ℝ)/3) :=
      mul_nonneg (degree_rpow_nonneg W _ _) (degree_rpow_nonneg W _ _)
    rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) hd)]
    exact mul_le_one₀ (W.le_one _ _) hd
      (mul_le_one₀ (degree_rpow_le_one W (by norm_num) _) (degree_rpow_nonneg W _ _)
        (degree_rpow_le_one W (by norm_num) _))
  have hshift := sq_le_shifted W hδ hδ1
  nlinarith [hshift, hδ.le, hδ1, hδe, hM0, hM1, hN0, hN1]

/-- **The fractional edge bound.**  `p⁵ ≤ N³`, the note's Lemma 3.1 at
`α = 1/3`. -/
theorem pow_five_le_fracEdge_cube (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 5 ≤ fracEdge W ^ 3 := by
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  have hM := cube_cubeMoment_le W
  have hMN := sq_le_cubeMoment_mul_fracEdge W
  have hM0 : 0 ≤ cubeMoment W := cubeMoment_nonneg W
  have hN0 : 0 ≤ fracEdge W := fracEdge_nonneg W
  -- `p⁶ = (p²)³ ≤ (MN)³ = M³N³ ≤ p·N³`
  have hcube : cliqueDensity 2 W ^ 6 ≤ cubeMoment W ^ 3 * fracEdge W ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hMN 3
    calc cliqueDensity 2 W ^ 6 = (cliqueDensity 2 W ^ 2) ^ 3 := by ring
      _ ≤ (cubeMoment W * fracEdge W) ^ 3 := this
      _ = cubeMoment W ^ 3 * fracEdge W ^ 3 := by ring
  rcases eq_or_lt_of_le hp0 with hz | hpos
  · rw [← hz]
    simpa using pow_nonneg (fracEdge_nonneg W) 3
  · have hstep : cliqueDensity 2 W * cliqueDensity 2 W ^ 5
        ≤ cliqueDensity 2 W * fracEdge W ^ 3 := by
      calc cliqueDensity 2 W * cliqueDensity 2 W ^ 5 = cliqueDensity 2 W ^ 6 := by ring
        _ ≤ cubeMoment W ^ 3 * fracEdge W ^ 3 := hcube
        _ ≤ cliqueDensity 2 W * fracEdge W ^ 3 :=
            mul_le_mul_of_nonneg_right hM (by positivity)
    exact le_of_mul_le_mul_left hstep hpos

end Taeyoung.Methods.Atlas148
