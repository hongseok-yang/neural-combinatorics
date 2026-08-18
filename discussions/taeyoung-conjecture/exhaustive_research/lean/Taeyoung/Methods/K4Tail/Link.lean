import Taeyoung.Methods.K4Tail.Scalar
import Taeyoung.Methods.CliqueLeaf.Density
import Taeyoung.Methods.BookTail.Core

/-!
# `K₄` with a two-edge tail: the link reduction

`notes/k4_two_edge_tail.tex` §3.  Conditioning the three non-tail clique
vertices through the link measure at `x` turns the rooted `K₄` density into
`d(x)³·t(K₃, W_x)`, and Goodman inside the link bounds that below.  Combined
with the pointwise `τ ≥ 2A - p` and monotonicity of `z ↦ z(2z-1)_+`, this gives
the completely elementary pointwise statement

```
d(x)·κ₄(x) ≥ u·(2u - d(x)²)_+,      u = (2A(x) - p)_+,
```

which is exactly the left-hand side of `K4Tail.plane_le_trunc`.  Everything the
note calls `F_p(d,a)` is carried in this truncated form, so no division by `d`
is ever performed and the zero-degree set needs no separate convention.

Goodman itself is the pure-chordal clique bound at `r = 3` — `cliquePoly 3 z =
z(2z-1)` — extended below the threshold by nonnegativity.
-/

open MeasureTheory

namespace Taeyoung.Methods.K4Tail

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.CliqueLeaf
  Taeyoung.Methods.BookTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Goodman for an arbitrary graphon -/

/-- **Goodman.**  `t(K₃,V) ≥ z(2z-1)` with no density hypothesis: above `1/2` it
is the pure-chordal clique bound at `r = 3`, below it the right side is
negative. -/
theorem goodman {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    [IsProbabilityMeasure ν] (V : Graphon Ω' ν) :
    cliqueDensity 2 V * (2 * cliqueDensity 2 V - 1) ≤ cliqueDensity 3 V := by
  rcases le_total (1 / 2 : ℝ) (cliqueDensity 2 V) with h | h
  · have hthr : (1 : ℝ) - 1 / (((3 - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 V := by
      norm_num
      linarith
    have hkey := cliqueDensity_ge_cliquePoly V (r := 3) (by norm_num) hthr
      (le_refl 3)
    have hpoly : cliquePoly 3 (cliqueDensity 2 V) =
        cliqueDensity 2 V * (2 * cliqueDensity 2 V - 1) := by
      simp only [cliquePoly, Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
      ring
    rwa [hpoly] at hkey
  · have h0 : 0 ≤ cliqueDensity 3 V := cliqueDensity_nonneg 3 V
    nlinarith [cliqueDensity_nonneg 2 V]

/-! ### `A ≤ d` -/

lemma pathOp_le_degree (W : Graphon Ω μ) (x : Ω) : pathOp W x ≤ degree W x := by
  have hint : Integrable (fun y ↦ W x y * degree W y) μ :=
    integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_degree W))
      (C := 1) fun y ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
        exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
  have hint2 : Integrable (fun y ↦ W x y) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  exact integral_mono hint hint2 fun y ↦ by
    nlinarith [W.nonneg x y, degree_le_one W y, degree_nonneg W y]

/-! ### The rooted `K₄` density -/

/-- `κ₄(x)`, the `K₄` density rooted at `x`: the rooted density of `K₃`. -/
noncomputable def rootedK4 (W : Graphon Ω μ) (x : Ω) : ℝ :=
  rootedDensity (⊤ : SimpleGraph (Fin 3)) W x

lemma rootedK4_nonneg (W : Graphon Ω μ) (x : Ω) : 0 ≤ rootedK4 W x :=
  rootedDensity_nonneg _ W x

lemma measurable_rootedK4 (W : Graphon Ω μ) : Measurable (rootedK4 W) :=
  measurable_rootedDensity _ W

lemma rootedK4_le_one (W : Graphon Ω μ) (x : Ω) : rootedK4 W x ≤ 1 :=
  rootedDensity_le_one _ W x

/-- **The pointwise link bound.**  Multiplied by `d(x)` so that the zero-degree
set needs no convention. -/
theorem mul_rootedK4_ge (W : Graphon Ω μ) (x : Ω) :
    max (2 * pathOp W x - cliqueDensity 2 W) 0 *
        max (2 * max (2 * pathOp W x - cliqueDensity 2 W) 0 - degree W x ^ 2) 0 ≤
      degree W x * rootedK4 W x := by
  set p := cliqueDensity 2 W with hpdef
  set u := max (2 * pathOp W x - p) 0 with hudef
  have hu0 : 0 ≤ u := le_max_right _ _
  rcases eq_or_lt_of_le (degree_nonneg W x) with hd0 | hdpos
  · -- degree zero: `A ≤ d = 0` and `p ≥ 0` force `u = 0`
    have hdz : degree W x = 0 := hd0.symm
    have hA : pathOp W x = 0 :=
      le_antisymm (by rw [← hdz]; exact pathOp_le_degree W x) (pathOp_nonneg W x)
    have huz : u = 0 := by
      rw [hudef, hA]
      exact max_eq_right (by linarith [cliqueDensity_nonneg 2 W])
    rw [huz, hdz]
    simp
  · haveI := isProbabilityMeasure_linkMeasure W hdpos
    -- the rooted densities in terms of the link
    have hτ : degree W x ^ 2 * cliqueDensity 2 (linkGraphon W x) =
        rootedTriangle W x := by
      rw [← rootedDensity_top_two W x, cliqueDensity,
        rootedDensity_eq (⊤ : SimpleGraph (Fin 2)) W hdpos]
    have hκ : rootedK4 W x =
        degree W x ^ 3 * cliqueDensity 3 (linkGraphon W x) := by
      rw [rootedK4, cliqueDensity, rootedDensity_eq _ W hdpos]
    -- Goodman inside the link, scaled back
    have hgood := goodman (linkGraphon W x)
    have hscale : rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2) ≤
        degree W x * rootedK4 W x := by
      have hpow : (0 : ℝ) ≤ degree W x ^ 4 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hgood hpow
      have heq : rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2) =
          degree W x ^ 4 * (cliqueDensity 2 (linkGraphon W x) *
            (2 * cliqueDensity 2 (linkGraphon W x) - 1)) := by
        rw [← hτ]; ring
      have heq2 : degree W x * rootedK4 W x =
          degree W x ^ 4 * cliqueDensity 3 (linkGraphon W x) := by
        rw [hκ]; ring
      rw [heq, heq2]
      exact hmul
    have hnn : 0 ≤ degree W x * rootedK4 W x :=
      mul_nonneg hdpos.le (rootedK4_nonneg W x)
    -- `τ ≥ u`, and `t ↦ t(2t - d²)` is nondecreasing where `2t ≥ d²`
    have hτu : u ≤ rootedTriangle W x :=
      max_le (rootedTriangle_ge W x) (rootedTriangle_nonneg W x)
    rcases le_total (2 * u - degree W x ^ 2) 0 with hv | hv
    · rw [max_eq_right hv, mul_zero]
      exact hnn
    · rw [max_eq_left hv]
      have hstep : u * (2 * u - degree W x ^ 2) ≤
          rootedTriangle W x * (2 * rootedTriangle W x - degree W x ^ 2) := by
        nlinarith [hτu, hu0, hv]
      linarith [hstep, hscale]

/-- **The pointwise supporting-plane bound.**  The scalar lemma, transported to
a point of the graphon. -/
theorem plane_le_rootedK4 (W : Graphon Ω μ)
    (hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W) (x : Ω) :
    plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ≤
      pathOp W x * rootedK4 W x := by
  set p := cliqueDensity 2 W with hpdef
  have hp1 : p ≤ 1 := cliqueDensity_le_one 2 W
  have hd0 : 0 ≤ degree W x := degree_nonneg W x
  have hA0 : 0 ≤ pathOp W x := pathOp_nonneg W x
  have hAd : pathOp W x ≤ degree W x := pathOp_le_degree W x
  have hscalar := plane_le_trunc (p := p) (d := degree W x) (a := pathOp W x)
    hp hp1 hd0 hA0 hAd
  rcases eq_or_lt_of_le hd0 with hd | hdpos
  · -- degree zero
    have hdz : degree W x = 0 := hd.symm
    have hAz : pathOp W x = 0 := le_antisymm (by rw [← hdz]; exact hAd) hA0
    have hnn : 0 ≤ pathOp W x * rootedK4 W x :=
      mul_nonneg hA0 (rootedK4_nonneg W x)
    refine le_trans ?_ hnn
    rw [hdz, hAz]
    have hval : plane p 0 0 = -(2 * p ^ 4 * (12 * p - 7)) := by
      simp only [plane, targetT]
      ring
    rw [hval]
    have h12 := pos_twelve (by linarith : (2:ℝ)/3 ≤ p)
    have hppos : (0:ℝ) < p := by linarith
    nlinarith [h12, pow_pos hppos 4]
  · have hlink := mul_rootedK4_ge W x
    have hmul : pathOp W x * (max (2 * pathOp W x - p) 0 *
        max (2 * max (2 * pathOp W x - p) 0 - degree W x ^ 2) 0) ≤
        pathOp W x * (degree W x * rootedK4 W x) :=
      mul_le_mul_of_nonneg_left hlink hA0
    have hchain : degree W x * plane p (degree W x) (pathOp W x) ≤
        degree W x * (pathOp W x * rootedK4 W x) := by
      calc degree W x * plane p (degree W x) (pathOp W x)
          ≤ pathOp W x * max (2 * pathOp W x - p) 0 *
              max (2 * max (2 * pathOp W x - p) 0 - degree W x ^ 2) 0 := hscalar
        _ = pathOp W x * (max (2 * pathOp W x - p) 0 *
              max (2 * max (2 * pathOp W x - p) 0 - degree W x ^ 2) 0) := by ring
        _ ≤ pathOp W x * (degree W x * rootedK4 W x) := hmul
        _ = degree W x * (pathOp W x * rootedK4 W x) := by ring
    exact le_of_mul_le_mul_left hchain hdpos

end Taeyoung.Methods.K4Tail
