import Taeyoung.Methods.Peeling
import Taeyoung.Methods.BookTail.Core
import Taeyoung.Methods.K4Tail.Link
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 100: a triangle with a two-leaf broom

`notes/triangle_two_leaf_broom.tex`.  The graph is a triangle rooted at `o`
with a further vertex `u` joined to `o`, and two leaves on `u`.  Peeling gives

```
t(B,W) = ∫ τ(x)·C(x) dμ(x),      C = T_W(d²).
```

Two pointwise facts reduce it to a scalar pair `(d,a) = (d(x), A(x))`:
`C ≥ A²/d` (Cauchy–Schwarz in the row measure) and `τ ≥ (2A-p)₊` (Goodman).
The supporting plane

```
L_p(d,a) = 2p⁴(1-4p) + p³(10p-3)d + 2p²(3p-1)(a - d²)
```

integrates to `p⁴(2p-1)` exactly, because `∫d = p` and `∫A = ∫d²`.

**The scalar lemma is proved differently from the note.**  The note splits the
active case `a ≥ p/2` into subcases and, for each, runs a discriminant argument
on a cubic.  Here the whole active case is one chain.  In the coordinates
`α = a - p²`, `δ = d - p` — the equality point of the extremal graphon — the
cleared inequality is the `ring` identity

```
a²(2a-p) - d·L_p = p(6p-1)α² - 2p²(3p-1)αδ + p³(8p-3)δ² + 2α³ + 2p²(3p-1)δ³,
```

and the two cubic terms are absorbed using only `a ≥ p/2` and `d ≥ p/2` (both
of which hold in the active case, since `d ≥ a`):

```
2α³ ≥ (p - 2p²)α²,      2p²(3p-1)δ³ ≥ -p³(3p-1)δ².
```

What is left, `4p²α² - 2p²(3p-1)αδ + p³(5p-2)δ²`, is positive definite on
`p ≥ 1/2`:

```
16p²·(that) = (8p²α - 2p²(3p-1)δ)² + 4p⁴(11p² - 2p - 1)δ²,
```

and `11p² - 2p - 1 ≥ 3/4` there.  No cubic discriminant appears.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.Broom

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.BookTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Two rooted facts shared with Atlas 97

`A ≤ d` is `K4Tail.pathOp_le_degree`; the lower bound and the second moment
operator are new. -/

/-- `A(x) ≥ d(x) + p - 1`, from `rs ≥ r + s - 1` on `[0,1]²`. -/
theorem le_pathOp (W : Graphon Ω μ) (x : Ω) :
    degree W x + cliqueDensity 2 W - 1 ≤ pathOp W x := by
  have hint : Integrable (fun y ↦ W x y * degree W y) μ :=
    integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_degree W))
      (C := 1) fun y ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
        exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
  have hlin : Integrable (fun y ↦ W x y + degree W y - 1) μ := by
    refine Integrable.sub (Integrable.add ?_ (integrable_degree W))
      (integrable_const 1)
    exact integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  have hmono : (∫ y, (W x y + degree W y - 1) ∂μ) ≤ ∫ y, W x y * degree W y ∂μ :=
    integral_mono hlin hint fun y ↦ by
      nlinarith [W.nonneg x y, W.le_one x y, degree_nonneg W y, degree_le_one W y]
  have hW : Integrable (fun y ↦ W x y) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  have hval : (∫ y, (W x y + degree W y - 1) ∂μ) =
      degree W x + cliqueDensity 2 W - 1 := by
    have e1 : (∫ y, (W x y + degree W y - 1) ∂μ) =
        (∫ y, (W x y + degree W y) ∂μ) - ∫ _y : Ω, (1 : ℝ) ∂μ :=
      integral_sub (hW.add (integrable_degree W)) (integrable_const 1)
    have e2 : (∫ y, (W x y + degree W y) ∂μ) =
        (∫ y, W x y ∂μ) + ∫ y, degree W y ∂μ :=
      integral_add hW (integrable_degree W)
    have hone : (∫ _y : Ω, (1 : ℝ) ∂μ) = 1 := by simp
    rw [e1, e2, integral_degree, hone]
    rfl
  rw [hval] at hmono
  exact hmono

/-- `C(x) = ∫ W(x,y)d(y)² dμ(y)`, the second-moment row operator. -/
noncomputable def sqOp (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ y, W x y * degree W y ^ 2 ∂μ

section SqOp

variable (W : Graphon Ω μ)

lemma measurable_sqOp : Measurable (sqOp W) := by
  have h : StronglyMeasurable
      (Function.uncurry fun x y ↦ W x y * degree W y ^ 2) := by
    refine (W.measurable.mul ?_).stronglyMeasurable
    exact ((measurable_degree W).comp measurable_snd).pow_const 2
  exact (h.integral_prod_right' (ν := μ)).measurable

lemma sqOp_nonneg (x : Ω) : 0 ≤ sqOp W x :=
  integral_nonneg fun y ↦
    mul_nonneg (W.nonneg x y) (pow_nonneg (degree_nonneg W y) 2)

lemma integrable_sqOp_row (x : Ω) :
    Integrable (fun y ↦ W x y * degree W y ^ 2) μ :=
  integrable_of_bdd ((measurable_row W.measurable x).mul
    ((measurable_degree W).pow_const 2)) (C := 1) fun y ↦ by
      have h0 : 0 ≤ W x y * degree W y ^ 2 :=
        mul_nonneg (W.nonneg x y) (pow_nonneg (degree_nonneg W y) 2)
      rw [abs_of_nonneg h0]
      exact mul_le_one₀ (W.le_one x y) (pow_nonneg (degree_nonneg W y) 2)
        (pow_le_one₀ (degree_nonneg W y) (degree_le_one W y))

lemma sqOp_le_one (x : Ω) : sqOp W x ≤ 1 := by
  calc sqOp W x ≤ ∫ _y : Ω, (1 : ℝ) ∂μ :=
        integral_mono (integrable_sqOp_row W x) (integrable_const _) fun y ↦
          mul_le_one₀ (W.le_one x y) (pow_nonneg (degree_nonneg W y) 2)
            (pow_le_one₀ (degree_nonneg W y) (degree_le_one W y))
    _ = 1 := by simp

/-- **`A² ≤ d·C`**, Cauchy–Schwarz in the row measure `W(x,·)dμ`. -/
theorem sq_pathOp_le (x : Ω) : pathOp W x ^ 2 ≤ degree W x * sqOp W x := by
  have hW : Integrable (fun y ↦ W x y) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  have hWd : Integrable (fun y ↦ W x y * degree W y) μ :=
    integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_degree W))
      (C := 1) fun y ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
        exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
  exact integral_mul_sq_le_integral_mul_integral_mul_sq (μ := μ)
    (A := fun y ↦ W x y) (η := degree W) hW hWd (integrable_sqOp_row W x)
    fun y ↦ W.nonneg x y

end SqOp

/-! ### The scalar supporting plane -/

/-- `L_p(d,a)`. -/
noncomputable def plane (p d a : ℝ) : ℝ :=
  2 * p ^ 4 * (1 - 4 * p) + p ^ 3 * (10 * p - 3) * d +
    2 * p ^ 2 * (3 * p - 1) * (a - d ^ 2)

/-- The active case, after clearing `d`. -/
theorem plane_le_active {p d a : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (had : a ≤ d) (hact : p / 2 ≤ a) :
    d * plane p d a ≤ a ^ 2 * (2 * a - p) := by
  have hd2 : p / 2 ≤ d := le_trans hact had
  -- the exact expansion around `(d,a) = (p,p²)`
  have hexp : a ^ 2 * (2 * a - p) - d * plane p d a =
      p * (6 * p - 1) * (a - p ^ 2) ^ 2 -
        2 * p ^ 2 * (3 * p - 1) * (a - p ^ 2) * (d - p) +
        p ^ 3 * (8 * p - 3) * (d - p) ^ 2 +
        2 * (a - p ^ 2) ^ 3 + 2 * p ^ 2 * (3 * p - 1) * (d - p) ^ 3 := by
    simp only [plane]
    ring
  -- absorb the two cubic terms
  have hcube1 : (p - 2 * p ^ 2) * (a - p ^ 2) ^ 2 ≤ 2 * (a - p ^ 2) ^ 3 := by
    have h : 2 * (a - p ^ 2) ^ 3 - (p - 2 * p ^ 2) * (a - p ^ 2) ^ 2 =
        2 * (a - p ^ 2) ^ 2 * (a - p / 2) := by ring
    have hnn : 0 ≤ 2 * (a - p ^ 2) ^ 2 * (a - p / 2) :=
      mul_nonneg (by positivity) (by linarith)
    linarith [h, hnn]
  have hcube2 : -(p ^ 3 * (3 * p - 1)) * (d - p) ^ 2 ≤
      2 * p ^ 2 * (3 * p - 1) * (d - p) ^ 3 := by
    have h : 2 * p ^ 2 * (3 * p - 1) * (d - p) ^ 3 +
        p ^ 3 * (3 * p - 1) * (d - p) ^ 2 =
        2 * p ^ 2 * (3 * p - 1) * (d - p) ^ 2 * (d - p / 2) := by ring
    have hnn : 0 ≤ 2 * p ^ 2 * (3 * p - 1) * (d - p) ^ 2 * (d - p / 2) :=
      mul_nonneg (mul_nonneg
        (by nlinarith [hp] : (0:ℝ) ≤ 2 * p ^ 2 * (3 * p - 1))
        (sq_nonneg (d - p))) (by linarith)
    linarith [h, hnn]
  -- the remaining quadratic form is positive definite
  have hpd : 0 ≤ 4 * p ^ 2 * (a - p ^ 2) ^ 2 -
      2 * p ^ 2 * (3 * p - 1) * (a - p ^ 2) * (d - p) +
      p ^ 3 * (5 * p - 2) * (d - p) ^ 2 := by
    have hid : 16 * p ^ 2 * (4 * p ^ 2 * (a - p ^ 2) ^ 2 -
        2 * p ^ 2 * (3 * p - 1) * (a - p ^ 2) * (d - p) +
        p ^ 3 * (5 * p - 2) * (d - p) ^ 2) =
        (8 * p ^ 2 * (a - p ^ 2) - 2 * p ^ 2 * (3 * p - 1) * (d - p)) ^ 2 +
          4 * p ^ 4 * (11 * p ^ 2 - 2 * p - 1) * (d - p) ^ 2 := by ring
    have h11 : (0 : ℝ) ≤ 11 * p ^ 2 - 2 * p - 1 := by nlinarith [hp, hp1]
    have hppos : (0 : ℝ) < p := by linarith
    nlinarith [hid, sq_nonneg (8 * p ^ 2 * (a - p ^ 2) -
      2 * p ^ 2 * (3 * p - 1) * (d - p)),
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * p ^ 4) h11)
        (sq_nonneg (d - p)), pow_pos hppos 2]
  linarith [hexp, hcube1, hcube2, hpd]

/-- The inactive case: below `a = p/2` the plane is nonpositive. -/
theorem plane_nonpos {p d a : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (had : a ≤ d) (hd1 : d ≤ 1) (hact : a ≤ p / 2) :
    plane p d a ≤ 0 := by
  have hd0 : (0 : ℝ) ≤ d := le_trans ha0 had
  have hγ : (0 : ℝ) < 2 * p ^ 2 * (3 * p - 1) := by nlinarith [hp]
  rcases le_total d (p / 2) with hdl | hdg
  · -- `a ≤ d ≤ p/2`: push `a` up to `d`
    have hstep : plane p d a ≤ plane p d d := by
      simp only [plane]
      nlinarith [hγ, had]
    have hQ1 : 0 ≤ 2 * (3 * p - 1) * d ^ 2 +
        (-10 * p ^ 2 - 3 * p + 2) * d + (8 * p ^ 3 - 2 * p ^ 2) := by
      have hmid : 2 * (3 * p - 1) * d ^ 2 +
          (-10 * p ^ 2 - 3 * p + 2) * d + (8 * p ^ 3 - 2 * p ^ 2) -
          p * (9 * p ^ 2 - 8 * p + 2) / 2 =
          (d - p / 2) * (2 * (3 * p - 1) * (d + p / 2) +
            (-10 * p ^ 2 - 3 * p + 2)) := by ring
      have hslope : 2 * (3 * p - 1) * (d + p / 2) +
          (-10 * p ^ 2 - 3 * p + 2) ≤ 0 := by nlinarith [hp, hp1, hdl, hd0]
      have hmin : 0 < p * (9 * p ^ 2 - 8 * p + 2) / 2 := by nlinarith [hp, hp1]
      nlinarith [hmid, hslope, hdl, hmin]
    have hval : plane p d d = -(p ^ 2 * (2 * (3 * p - 1) * d ^ 2 +
        (-10 * p ^ 2 - 3 * p + 2) * d + (8 * p ^ 3 - 2 * p ^ 2))) := by
      simp only [plane]; ring
    nlinarith [hstep, hval, hQ1, sq_nonneg p]
  · -- `d ≥ p/2`: push `a` up to `p/2`
    have hstep : plane p d a ≤ plane p d (p / 2) := by
      simp only [plane]
      nlinarith [hγ, hact]
    have hQ2 : 0 ≤ 2 * (3 * p - 1) * d ^ 2 +
        (-10 * p ^ 2 + 3 * p) * d + (8 * p ^ 3 - 5 * p ^ 2 + p) := by
      have hid : 8 * (3 * p - 1) * (2 * (3 * p - 1) * d ^ 2 +
          (-10 * p ^ 2 + 3 * p) * d + (8 * p ^ 3 - 5 * p ^ 2 + p)) =
          (4 * (3 * p - 1) * d + (-10 * p ^ 2 + 3 * p)) ^ 2 +
            p * (2 * p - 1) ^ 2 * (23 * p - 8) := by ring
      have h1 : (0 : ℝ) ≤ p * (2 * p - 1) ^ 2 * (23 * p - 8) := by
        refine mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
      nlinarith [hid, sq_nonneg (4 * (3 * p - 1) * d + (-10 * p ^ 2 + 3 * p)),
        h1, hp]
    have hval : plane p d (p / 2) = -(p ^ 2 * (2 * (3 * p - 1) * d ^ 2 +
        (-10 * p ^ 2 + 3 * p) * d + (8 * p ^ 3 - 5 * p ^ 2 + p))) := by
      simp only [plane]; ring
    nlinarith [hstep, hval, hQ2, sq_nonneg p]

/-- **The pointwise supporting-plane bound**, cleared of the division by `d`. -/
theorem mul_plane_le {p d a c τ : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (had : a ≤ d) (hd1 : d ≤ 1)
    (hc : a ^ 2 ≤ d * c) (hτ : 2 * a - p ≤ τ) (hτ0 : 0 ≤ τ) (hc0 : 0 ≤ c) :
    d * plane p d a ≤ d * (τ * c) := by
  have hd0 : (0 : ℝ) ≤ d := le_trans ha0 had
  rcases le_total a (p / 2) with hin | hact
  · have := plane_nonpos hp hp1 ha0 had hd1 hin
    have hrhs : 0 ≤ d * (τ * c) := mul_nonneg hd0 (mul_nonneg hτ0 hc0)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hd0 this, hrhs]
  · have hstep := plane_le_active hp hp1 had hact
    have h2a : 0 ≤ 2 * a - p := by linarith
    have h1 : a ^ 2 * (2 * a - p) ≤ (d * c) * (2 * a - p) :=
      mul_le_mul_of_nonneg_right hc h2a
    have h2 : (d * c) * (2 * a - p) ≤ (d * c) * τ :=
      mul_le_mul_of_nonneg_left hτ (mul_nonneg hd0 hc0)
    nlinarith [hstep, h1, h2]

/-! ### The pointwise bound at a point of the graphon -/

lemma sqOp_le_degree (W : Graphon Ω μ) (x : Ω) : sqOp W x ≤ degree W x := by
  have hW : Integrable (fun y ↦ W x y) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  exact integral_mono (integrable_sqOp_row W x) hW fun y ↦
    mul_le_of_le_one_right (W.nonneg x y)
      (pow_le_one₀ (degree_nonneg W y) (degree_le_one W y))

/-- **The supporting plane lies under `τ·C` at every point.** -/
theorem plane_le_rooted (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) (x : Ω) :
    plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ≤
      rootedTriangle W x * sqOp W x := by
  set p := cliqueDensity 2 W with hpdef
  have hp1 : p ≤ 1 := cliqueDensity_le_one 2 W
  have hd0 : 0 ≤ degree W x := degree_nonneg W x
  have hd1 : degree W x ≤ 1 := degree_le_one W x
  have hA0 : 0 ≤ pathOp W x := pathOp_nonneg W x
  have hAd : pathOp W x ≤ degree W x := K4Tail.pathOp_le_degree W x
  rcases eq_or_lt_of_le hd0 with hd | hdpos
  · -- degree zero
    have hdz : degree W x = 0 := hd.symm
    have hAz : pathOp W x = 0 := le_antisymm (by rw [← hdz]; exact hAd) hA0
    have hCz : sqOp W x = 0 :=
      le_antisymm (by rw [← hdz]; exact sqOp_le_degree W x) (sqOp_nonneg W x)
    have hnn : 0 ≤ rootedTriangle W x * sqOp W x :=
      mul_nonneg (rootedTriangle_nonneg W x) (sqOp_nonneg W x)
    refine le_trans ?_ hnn
    rw [hdz, hAz]
    have hval : plane p 0 0 = 2 * p ^ 4 * (1 - 4 * p) := by
      simp only [plane]; ring
    rw [hval]
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ p) 4, hp]
  · have hchain := mul_plane_le (p := p) (d := degree W x) (a := pathOp W x)
      (c := sqOp W x) (τ := rootedTriangle W x) hp hp1 hA0 hAd hd1
      (sq_pathOp_le W x) (by rw [hpdef]; exact rootedTriangle_ge W x)
      (rootedTriangle_nonneg W x) (sqOp_nonneg W x)
    exact le_of_mul_le_mul_left hchain hdpos

/-! ### The graph and its peeling -/

/-- Triangle `0,1,2`; `3` joined to the root `0`; leaves `4,5` on `3`. -/
def broom : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4), (3, 5)]

instance : DecidableRel broom.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_broom :
    broom.edgeFinset = {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(3, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_broom (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight broom W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 3) (x 4) * W (x 3) (x 5) := by
  rw [graphWeight, edgeFinset_broom]
  simp
  ring

section Peel

variable (W : Graphon Ω μ)

private lemma meas_broom : Measurable fun y : Fin 6 → Ω ↦
    W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 3) (y 4) * W (y 3) (y 5) :=
  (((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 3)).mul
    (measurable_coord_pair W 3 4)).mul (measurable_coord_pair W 3 5)

private lemma bdd_broom (x : Fin 6 → Ω) :
    |W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 3) (x 4) * W (x 3) (x 5)| ≤ 1 := by
  have h0 : 0 ≤ W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 3) (x 4) * W (x 3) (x 5) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _)

/-- **The density of Atlas 100 is `∫ τ·C`.** -/
theorem homDensity_broom :
    homDensity broom W = ∫ x, rootedTriangle W x * sqOp W x ∂μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_broom W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
        W a3 a4 * W a3 a5)
      (meas_broom W) (bdd_broom W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  have hinner : ∀ a1 a2 : Ω,
      (∫ a3, ∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
          W a3 a4 * W a3 a5 ∂μ ∂μ ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * sqOp W a0 := by
    intro a1 a2
    have h5 : ∀ a3 a4 : Ω,
        (∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a3 a4 * W a3 a5 ∂μ) =
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * degree W a3 := by
      intro a3 a4
      have hre : ∀ a5 : Ω,
          W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a3 a4 * W a3 a5 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * W a3 a5 :=
        fun a5 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      rfl
    have h4 : ∀ a3 : Ω,
        (∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
            W a3 a4 * W a3 a5 ∂μ ∂μ) =
          (W a0 a1 * W a0 a2 * W a1 a2) * (W a0 a3 * degree W a3 ^ 2) := by
      intro a3
      rw [integral_congr_ae (ae_of_all _ (h5 a3))]
      have hre : ∀ a4 : Ω,
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * degree W a3 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * degree W a3) *
              W a3 a4 := fun a4 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      show ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * degree W a3) *
          degree W a3 = _
      ring
    rw [integral_congr_ae (ae_of_all _ h4), integral_const_mul, ← sqOp]
  have h12 : (∫ a1, ∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) * sqOp W a0 ∂μ ∂μ) =
      rootedTriangle W a0 * sqOp W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) * sqOp W a0 ∂μ) =
          sqOp W a0 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 ↦ by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul]
    show sqOp W a0 * rootedTriangle W a0 = _
    ring
  rw [← h12]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  exact hinner a1 a2

end Peel

/-! ### Integrating the plane -/

theorem integral_plane (W : Graphon Ω μ) :
    (∫ x, plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ∂μ) =
      cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1) := by
  have hd := integrable_degree W
  have hA := integrable_pathOp W
  have hd2 := integrable_degree_pow W 2
  have i0 : Integrable (fun _ : Ω ↦
      2 * cliqueDensity 2 W ^ 4 * (1 - 4 * cliqueDensity 2 W) -
        2 * cliqueDensity 2 W ^ 2 * (3 * cliqueDensity 2 W - 1) * 0) μ :=
    integrable_const _
  have hfun : ∀ x : Ω,
      plane (cliqueDensity 2 W) (degree W x) (pathOp W x) =
        2 * cliqueDensity 2 W ^ 4 * (1 - 4 * cliqueDensity 2 W) +
          cliqueDensity 2 W ^ 3 * (10 * cliqueDensity 2 W - 3) * degree W x +
          2 * cliqueDensity 2 W ^ 2 * (3 * cliqueDensity 2 W - 1) * pathOp W x -
          2 * cliqueDensity 2 W ^ 2 * (3 * cliqueDensity 2 W - 1) *
            degree W x ^ 2 := by
    intro x
    simp only [plane]
    ring
  have j0 : Integrable (fun _ : Ω ↦
      2 * cliqueDensity 2 W ^ 4 * (1 - 4 * cliqueDensity 2 W)) μ :=
    integrable_const _
  have j1 : Integrable (fun x : Ω ↦
      cliqueDensity 2 W ^ 3 * (10 * cliqueDensity 2 W - 3) * degree W x) μ :=
    hd.const_mul _
  have j2 : Integrable (fun x : Ω ↦
      2 * cliqueDensity 2 W ^ 2 * (3 * cliqueDensity 2 W - 1) * pathOp W x) μ :=
    hA.const_mul _
  have j3 : Integrable (fun x : Ω ↦
      2 * cliqueDensity 2 W ^ 2 * (3 * cliqueDensity 2 W - 1) *
        degree W x ^ 2) μ := hd2.const_mul _
  have e1 := integral_sub ((j0.add j1).add j2) j3
  have e2 := integral_add (j0.add j1) j2
  have e3 := integral_add j0 j1
  simp only [Pi.add_apply] at e1 e2 e3
  rw [integral_congr_ae (ae_of_all _ hfun), e1, e2, e3, integral_const,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_degree, integral_pathOp, moment]
  simp
  ring

/-! ### The bound -/

/-- **Atlas 100 dominates its target.** -/
theorem broom_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1) ≤ homDensity broom W := by
  have hint1 : Integrable
      (fun x ↦ plane (cliqueDensity 2 W) (degree W x) (pathOp W x)) μ := by
    have hfun : ∀ x : Ω,
        plane (cliqueDensity 2 W) (degree W x) (pathOp W x) =
          2 * cliqueDensity 2 W ^ 4 * (1 - 4 * cliqueDensity 2 W) +
            cliqueDensity 2 W ^ 3 * (10 * cliqueDensity 2 W - 3) * degree W x +
            2 * cliqueDensity 2 W ^ 2 * (3 * cliqueDensity 2 W - 1) * pathOp W x -
            2 * cliqueDensity 2 W ^ 2 * (3 * cliqueDensity 2 W - 1) *
              degree W x ^ 2 := by
      intro x; simp only [plane]; ring
    refine Integrable.congr ?_ (ae_of_all _ fun x ↦ (hfun x).symm)
    exact (((integrable_const _).add ((integrable_degree W).const_mul _)).add
      ((integrable_pathOp W).const_mul _)).sub
      ((integrable_degree_pow W 2).const_mul _)
  have hint2 : Integrable (fun x ↦ rootedTriangle W x * sqOp W x) μ :=
    integrable_of_bdd ((measurable_rootedTriangle W).mul (measurable_sqOp W))
      (C := 1) fun x ↦ by
        have h0 : 0 ≤ rootedTriangle W x * sqOp W x :=
          mul_nonneg (rootedTriangle_nonneg W x) (sqOp_nonneg W x)
        rw [abs_of_nonneg h0]
        exact mul_le_one₀ (rootedTriangle_le_one W x) (sqOp_nonneg W x)
          (sqOp_le_one W x)
  have hmono := integral_mono hint1 hint2 (plane_le_rooted W hp)
  rw [integral_plane W] at hmono
  rw [homDensity_broom W]
  exact hmono

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_100 (z : ℝ) :
    affineProd [0, 1, 1, 1, 1, 2] z = z ^ 4 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃`, then `3` on the root `0`, then the two leaves on `3`. -/
def iso100 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {none}) {some none} ≃g
      broom where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom100 : IsChromaticPolynomial broom
    ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := broom) iso100
    (isClique_singleton _ (some none))
    (isChromaticPolynomial_attachVertex (isClique_singleton _ none)
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count100 (k : ℕ) :
    properAssignmentCount broom k =
      (k - 1) * ((k - 1) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := broom) iso100
      (isClique_singleton _ (some none)) k,
    properAssignmentCount_attachVertex (isClique_singleton _ none),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num100 : IsChromaticNumber broom 3 where
  positive := by rw [count100]; decide
  zero_below k hk := by
    rw [count100, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 100 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_100 : Taeyoung.SatisfiesLowerBound broom := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := broom) hP chrom100
  have hreq : r = 3 := IsChromaticNumber.unique (H := broom) hr num100
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := broom_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 1, 2] (by norm_num) hone,
      affineProd_100]
    exact hkey

end Taeyoung.Methods.Broom
