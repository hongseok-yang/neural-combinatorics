import Taeyoung.Methods.Broom

/-!
# Atlas 97: adjacent triangle roots carrying a leaf and a two-edge tail

`notes/triangle_adjacent_leaf_tail.tex`.  The graph is a triangle `o,r,s` with a
two-edge path `o–u–v` at `o` and a single leaf `w` at the *adjacent* triangle
vertex `r`.  Because the two attachments sit at different roots, the one-root
mixed-branch theorem does not apply.  Peeling gives

```
t(H,W) = ∫ A(x)·E(x) dμ(x),   A = T_W d,
         E(x) = ∫∫ W(x,y)W(x,z)W(y,z)·d(y) dμ(y)dμ(z).
```

A two-edge inclusion–exclusion `W(x,z)W(y,z) ≥ W(x,z) + W(y,z) - 1` inside the
triangle gives `E ≥ C - (1-d)A` with `C = T_W(d²)`, and `A² ≤ d·C` is
Cauchy–Schwarz in the row measure.  So the whole row reduces to the scalar pair
`(d,a) = (d(x), A(x))` against the supporting plane

```
L_p(d,a) = p⁴(3-8p) + 2p³(5p-2)d + p²(5p-2)(a - d²),
```

which integrates to `p⁴(2p-1)` exactly, because `∫d = p` and `∫A = ∫d²`.

**The scalar lemma is proved differently from the note.**  The note runs a
discriminant argument on the cubic `G_p(d,·) = a³ + a²d² - a²d - d·L_p`: it
evaluates `G_p` at both branches of the feasible lower endpoint, certifies a
degree-12 Bernstein expansion of a sextic in `√(1-p)`, and certifies an `8×7`
Bernstein coefficient matrix for the cubic's discriminant.  Here the active case
is a single algebraic identity.  Expanding around the equality point
`(d,a) = (p,p²)` and writing `X = a - pd`, `Y = d - p`,

```
a²(a + d² - d) - d·L_p = (a - p²)²·(a + d² - d)
                       + p²·(2X² + (2d+p)XY + (7p-2)dY²).
```

The first summand is nonnegative exactly on the active region.  The bracket is
nonnegative on the whole rooted region `0 ≤ a ≤ d ≤ 1`, by a split at `d = p/3`:

* `d ≥ p/3` — the form is positive semidefinite outright,
  `8·(bracket) = (4X + (2d+p)Y)² - q_p(d)·Y²` with
  `q_p(d) = 4d² + (16-52p)d + p² ≤ 0` there, by convexity from
  `q_p(p/3) = p(48-143p)/9 ≤ 0` and `q_p(1) = p² - 52p + 20 ≤ 0`;
* `d ≤ p/3` — then `|X| ≤ pd` (from `0 ≤ a ≤ d` and `p ≥ 1/2`) and `Y < 0`, so
  dropping `2X²` leaves `d(p-d)(6p² - 2p - (9p-2)d) ≥ 0`.

No cubic discriminant, no Bernstein matrix, and no root of `1-p` appears.  The
inactive case follows the note: `L_p` is increasing in `a`, and at the parabola
`a = d(1-d)` it equals `-p²Q_p(d)` with `8(5p-2)Q_p(d)` a sum of a square and
`(2p-1)²(5p-2)(11p+2) ≥ 0`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.AdjTail

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.BookTail Taeyoung.Methods.Broom

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The leaf-weighted rooted triangle

`E(x) = ∫∫ W(x,y)W(x,z)W(y,z)·d(y)`, the density of a triangle rooted at `x`
carrying one pendant leaf on the *other* endpoint of the rooted edge. -/

/-- `E(x)`, the rooted triangle with a leaf on the adjacent root. -/
noncomputable def leafTri (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ y, ∫ z, W x y * W x z * W y z * degree W y ∂μ ∂μ

section LeafTri

variable (W : Graphon Ω μ)

private lemma bdd_leafTri (x y z : Ω) :
    |W x y * W x z * W y z * degree W y| ≤ 1 := by
  have h0 : 0 ≤ W x y * W x z * W y z * degree W y :=
    mul_nonneg (mul_nonneg (mul_nonneg (W.nonneg x y) (W.nonneg x z))
      (W.nonneg y z)) (degree_nonneg W y)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (W.le_one x y) (W.nonneg x z)
    (W.le_one x z)) (W.nonneg y z) (W.le_one y z)) (degree_nonneg W y)
    (degree_le_one W y)

private lemma ker_leafTri (x : Ω) : Measurable
    (Function.uncurry fun y z ↦ W x y * W x z * W y z * degree W y) :=
  (((W.measurable.comp (measurable_const.prodMk measurable_fst)).mul
    (W.measurable.comp (measurable_const.prodMk measurable_snd))).mul
    W.measurable).mul ((measurable_degree W).comp measurable_fst)

lemma leafTri_nonneg (x : Ω) : 0 ≤ leafTri W x :=
  integral_nonneg fun y ↦ integral_nonneg fun _z ↦
    mul_nonneg (mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
      (W.nonneg _ _)) (degree_nonneg W y)

lemma measurable_leafTri : Measurable (leafTri W) := by
  have hg : StronglyMeasurable (fun q : (Ω × Ω) × Ω ↦
      W q.1.1 q.1.2 * W q.1.1 q.2 * W q.1.2 q.2 * degree W q.1.2) := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact (((W.measurable.comp measurable_fst).mul
      (W.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd))).mul
      (W.measurable.comp ((measurable_snd.comp measurable_fst).prodMk
        measurable_snd))).mul
      ((measurable_degree W).comp (measurable_snd.comp measurable_fst))
  have hinner : Measurable
      (Function.uncurry fun x y ↦ ∫ z, W x y * W x z * W y z * degree W y ∂μ) :=
    (hg.integral_prod_right' (ν := μ)).measurable
  exact (hinner.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma leafTri_le_one (x : Ω) : leafTri W x ≤ 1 := by
  have hb : ∀ y, |∫ z, W x y * W x z * W y z * degree W y ∂μ| ≤ 1 := fun y ↦
    abs_integral_le_of_bdd (measurable_row (ker_leafTri W x) y)
      (bdd_leafTri W x y)
  have hfin := abs_integral_le_of_bdd (μ := μ)
    (measurable_integral_right (ker_leafTri W x)) hb
  rw [abs_le] at hfin
  exact hfin.2

/-- **The two-edge inclusion–exclusion**, `E ≥ C - (1-d)A`. -/
theorem leafTri_ge (x : Ω) :
    sqOp W x - (1 - degree W x) * pathOp W x ≤ leafTri W x := by
  have hrow : ∀ y : Ω, Integrable (fun z ↦ W y z) μ := fun y ↦
    integrable_of_bdd (measurable_row W.measurable y) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (W.nonneg y z)]; exact W.le_one y z
  -- the linearised kernel
  have hlker : Measurable (Function.uncurry fun y z ↦
      W x y * degree W y * (W x z + W y z - 1)) :=
    (((W.measurable.comp (measurable_const.prodMk measurable_fst)).mul
      ((measurable_degree W).comp measurable_fst)).mul
      (((W.measurable.comp (measurable_const.prodMk measurable_snd)).add
        W.measurable).sub measurable_const))
  have hlbdd : ∀ y z, |W x y * degree W y * (W x z + W y z - 1)| ≤ 1 := by
    intro y z
    have h1 := W.nonneg x y; have h2 := W.le_one x y
    have h3 := W.nonneg x z; have h4 := W.le_one x z
    have h5 := W.nonneg y z; have h6 := W.le_one y z
    have h7 := degree_nonneg W y; have h8 := degree_le_one W y
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg h1 h7, mul_nonneg (mul_nonneg h1 h7) h3,
      mul_nonneg (mul_nonneg h1 h7) h5]
  have hpt : ∀ y z, W x y * degree W y * (W x z + W y z - 1) ≤
      W x y * W x z * W y z * degree W y := by
    intro y z
    have hab : W x z + W y z - 1 ≤ W x z * W y z := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (W.le_one x z))
        (sub_nonneg.mpr (W.le_one y z))]
    have hmul := mul_le_mul_of_nonneg_left hab
      (mul_nonneg (W.nonneg x y) (degree_nonneg W y))
    nlinarith [hmul]
  -- the inner integral of the linearisation
  have hz : ∀ y : Ω, (∫ z, W x y * degree W y * (W x z + W y z - 1) ∂μ) =
      W x y * degree W y * (degree W x + degree W y - 1) := by
    intro y
    rw [integral_const_mul]
    congr 1
    have e1 := integral_sub ((hrow x).add (hrow y)) (integrable_const (μ := μ) (1 : ℝ))
    have e2 := integral_add (hrow x) (hrow y)
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
    simp [degree]
  -- the outer integral of the linearisation
  have hWd : Integrable (fun y ↦ W x y * degree W y) μ :=
    integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_degree W))
      (C := 1) fun y ↦ by
        rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
        exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
  have houter : (∫ y, W x y * degree W y * (degree W x + degree W y - 1) ∂μ) =
      degree W x * pathOp W x + sqOp W x - pathOp W x := by
    have hfun : ∀ y : Ω, W x y * degree W y * (degree W x + degree W y - 1) =
        degree W x * (W x y * degree W y) + W x y * degree W y ^ 2 -
          W x y * degree W y := fun y ↦ by ring
    have j0 : Integrable (fun y ↦ degree W x * (W x y * degree W y)) μ :=
      hWd.const_mul _
    have j1 : Integrable (fun y ↦ W x y * degree W y ^ 2) μ :=
      integrable_sqOp_row W x
    have e1 := integral_sub (j0.add j1) hWd
    have e2 := integral_add j0 j1
    simp only [Pi.add_apply] at e1 e2
    rw [integral_congr_ae (ae_of_all _ hfun), e1, e2, integral_const_mul]
    rfl
  -- compare the two double integrals
  have hcmp : (∫ y, ∫ z, W x y * degree W y * (W x z + W y z - 1) ∂μ ∂μ) ≤
      leafTri W x := by
    refine integral_mono (integrable_integral_right hlker hlbdd)
      (integrable_integral_right (ker_leafTri W x) (bdd_leafTri W x)) fun y ↦ ?_
    exact integral_mono (integrable_of_bdd (measurable_row hlker y) (hlbdd y))
      (integrable_of_bdd (measurable_row (ker_leafTri W x) y)
        (bdd_leafTri W x y)) (hpt y)
  rw [integral_congr_ae (ae_of_all _ hz), houter] at hcmp
  nlinarith [hcmp]

end LeafTri

/-! ### The scalar supporting plane -/

/-- `L_p(d,a)`. -/
noncomputable def plane (p d a : ℝ) : ℝ :=
  p ^ 4 * (3 - 8 * p) + 2 * p ^ 3 * (5 * p - 2) * d +
    p ^ 2 * (5 * p - 2) * (a - d ^ 2)

/-- The quadratic form `2X² + (2d+p)XY + (7p-2)dY²` at `X = a - pd`, `Y = d - p`
is nonnegative on the whole rooted region. -/
theorem shape_nonneg {p d a : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (had : a ≤ d) (hd1 : d ≤ 1) :
    0 ≤ 2 * (a - p * d) ^ 2 + (2 * d + p) * (a - p * d) * (d - p) +
      (7 * p - 2) * d * (d - p) ^ 2 := by
  have hd0 : (0 : ℝ) ≤ d := le_trans ha0 had
  rcases le_total d (p / 3) with hsmall | hbig
  · -- `d ≤ p/3`: the cross term is dominated by `(7p-2)dY²`
    have hXlo : -(p * d) ≤ a - p * d := by linarith
    have hXhi : a - p * d ≤ p * d := by nlinarith [hd0, hp, hp1, had]
    have hpd : (0 : ℝ) ≤ p - d := by nlinarith [hp, hd0]
    have hcross : -((2 * d + p) * (p * d) * (p - d)) ≤
        (2 * d + p) * (a - p * d) * (d - p) := by
      have h2d : (0 : ℝ) ≤ 2 * d + p := by linarith
      nlinarith [mul_nonneg (mul_nonneg h2d hpd) (sub_nonneg.mpr hXhi)]
    have hlow : 0 ≤ d * (p - d) * (6 * p ^ 2 - 2 * p - (9 * p - 2) * d) := by
      refine mul_nonneg (mul_nonneg hd0 hpd) ?_
      nlinarith [hp, hp1, hsmall, hd0]
    have hid : (7 * p - 2) * d * (d - p) ^ 2 -
        (2 * d + p) * (p * d) * (p - d) =
        d * (p - d) * (6 * p ^ 2 - 2 * p - (9 * p - 2) * d) := by ring
    nlinarith [sq_nonneg (a - p * d), hcross, hlow, hid]
  · -- `p/3 ≤ d`: the quadratic form is itself positive semidefinite
    have hq : 4 * d ^ 2 + (16 - 52 * p) * d + p ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hbig), hp, hp1,
        hbig, hd0]
    have hid : 8 * (2 * (a - p * d) ^ 2 + (2 * d + p) * (a - p * d) * (d - p) +
        (7 * p - 2) * d * (d - p) ^ 2) =
        (4 * (a - p * d) + (2 * d + p) * (d - p)) ^ 2 -
          (4 * d ^ 2 + (16 - 52 * p) * d + p ^ 2) * (d - p) ^ 2 := by ring
    nlinarith [hid, sq_nonneg (4 * (a - p * d) + (2 * d + p) * (d - p)),
      mul_nonneg (neg_nonneg.mpr hq) (sq_nonneg (d - p))]

/-- The active case, after clearing `d`. -/
theorem plane_le_active {p d a : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (had : a ≤ d) (hd1 : d ≤ 1) (hact : 0 ≤ a + d ^ 2 - d) :
    d * plane p d a ≤ a ^ 2 * (a + d ^ 2 - d) := by
  have hS := shape_nonneg hp hp1 ha0 had hd1
  have hid : a ^ 2 * (a + d ^ 2 - d) - d * plane p d a =
      (a - p ^ 2) ^ 2 * (a + d ^ 2 - d) +
        p ^ 2 * (2 * (a - p * d) ^ 2 + (2 * d + p) * (a - p * d) * (d - p) +
          (7 * p - 2) * d * (d - p) ^ 2) := by
    simp only [plane]; ring
  have h1 : 0 ≤ (a - p ^ 2) ^ 2 * (a + d ^ 2 - d) :=
    mul_nonneg (sq_nonneg _) hact
  have h2 : 0 ≤ p ^ 2 * (2 * (a - p * d) ^ 2 +
      (2 * d + p) * (a - p * d) * (d - p) + (7 * p - 2) * d * (d - p) ^ 2) :=
    mul_nonneg (sq_nonneg p) hS
  linarith [hid, h1, h2]

/-- The inactive case: below the parabola `a = d(1-d)` the plane is nonpositive. -/
theorem plane_nonpos {p d a : ℝ} (hp : (1 : ℝ) / 2 ≤ p)
    (hin : a + d ^ 2 - d ≤ 0) :
    plane p d a ≤ 0 := by
  have hγ : (0 : ℝ) < p ^ 2 * (5 * p - 2) := by nlinarith [hp]
  have hstep : plane p d a ≤ plane p d (d - d ^ 2) := by
    simp only [plane]; nlinarith [hγ, hin]
  have hQ : 0 ≤ 2 * (5 * p - 2) * d ^ 2 + (-10 * p ^ 2 - p + 2) * d +
      (8 * p ^ 3 - 3 * p ^ 2) := by
    have hid : 8 * (5 * p - 2) * (2 * (5 * p - 2) * d ^ 2 +
        (-10 * p ^ 2 - p + 2) * d + (8 * p ^ 3 - 3 * p ^ 2)) =
        (4 * (5 * p - 2) * d + (-10 * p ^ 2 - p + 2)) ^ 2 +
          (2 * p - 1) ^ 2 * (5 * p - 2) * (11 * p + 2) := by ring
    have h1 : (0 : ℝ) ≤ (2 * p - 1) ^ 2 * (5 * p - 2) * (11 * p + 2) := by
      refine mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
    nlinarith [hid, sq_nonneg (4 * (5 * p - 2) * d + (-10 * p ^ 2 - p + 2)), h1, hp]
  have hval : plane p d (d - d ^ 2) =
      -(p ^ 2 * (2 * (5 * p - 2) * d ^ 2 + (-10 * p ^ 2 - p + 2) * d +
        (8 * p ^ 3 - 3 * p ^ 2))) := by
    simp only [plane]; ring
  nlinarith [hstep, hval, hQ, sq_nonneg p]

/-- **The pointwise supporting-plane bound**, cleared of the division by `d`. -/
theorem mul_plane_le {p d a c e : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (had : a ≤ d) (hd1 : d ≤ 1)
    (hc : a ^ 2 ≤ d * c) (he : c - (1 - d) * a ≤ e) (he0 : 0 ≤ e) :
    d * plane p d a ≤ d * (a * e) := by
  have hd0 : (0 : ℝ) ≤ d := le_trans ha0 had
  rcases le_total (a + d ^ 2 - d) 0 with hin | hact
  · have h := plane_nonpos hp hin
    have hrhs : 0 ≤ d * (a * e) := mul_nonneg hd0 (mul_nonneg ha0 he0)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hd0 h, hrhs]
  · have hstep := plane_le_active hp hp1 ha0 had hd1 hact
    have h1 : (d * a) * (c - (1 - d) * a) ≤ (d * a) * e :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hd0 ha0)
    have h2 : a ^ 2 * (a + d ^ 2 - d) ≤ (d * a) * (c - (1 - d) * a) := by
      nlinarith [mul_le_mul_of_nonneg_left hc ha0]
    nlinarith [hstep, h1, h2]

/-- **The supporting plane lies under `A·E` at every point.** -/
theorem plane_le_rooted (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) (x : Ω) :
    plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ≤
      pathOp W x * leafTri W x := by
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
    have hval : plane p 0 0 = p ^ 4 * (3 - 8 * p) := by simp only [plane]; ring
    rw [hdz, hAz, hval, zero_mul]
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ p) 4, hp]
  · have hchain := mul_plane_le (p := p) (d := degree W x) (a := pathOp W x)
      (c := sqOp W x) (e := leafTri W x) hp hp1 hA0 hAd hd1
      (sq_pathOp_le W x) (leafTri_ge W x) (leafTri_nonneg W x)
    exact le_of_mul_le_mul_left hchain hdpos

/-! ### The graph and its peeling -/

/-- Triangle `0,1,2`; the two-edge tail `0–3–4`; the leaf `5` on `1`. -/
def adjTail : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4), (1, 5)]

instance : DecidableRel adjTail.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_adjTail :
    adjTail.edgeFinset = {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(3, 4), s(1, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_adjTail (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight adjTail W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 3) (x 4) * W (x 1) (x 5) := by
  rw [graphWeight, edgeFinset_adjTail]
  simp
  ring

section Peel

variable (W : Graphon Ω μ)

private lemma meas_adjTail : Measurable fun y : Fin 6 → Ω ↦
    W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
      W (y 3) (y 4) * W (y 1) (y 5) :=
  (((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 3)).mul
    (measurable_coord_pair W 3 4)).mul (measurable_coord_pair W 1 5)

omit [IsProbabilityMeasure μ] in
private lemma bdd_adjTail (x : Fin 6 → Ω) :
    |W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 3) (x 4) * W (x 1) (x 5)| ≤ 1 := by
  have h0 : 0 ≤ W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
      W (x 3) (x 4) * W (x 1) (x 5) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _)

/-- **The density of Atlas 97 is `∫ A·E`.** -/
theorem homDensity_adjTail :
    homDensity adjTail W = ∫ x, pathOp W x * leafTri W x ∂μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_adjTail W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
        W a3 a4 * W a1 a5)
      (meas_adjTail W) (bdd_adjTail W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  have hinner : ∀ a1 a2 : Ω,
      (∫ a3, ∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
          W a3 a4 * W a1 a5 ∂μ ∂μ ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2 * degree W a1) * pathOp W a0 := by
    intro a1 a2
    have h5 : ∀ a3 a4 : Ω,
        (∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a3 a4 * W a1 a5 ∂μ) =
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * degree W a1 := by
      intro a3 a4
      have hre : ∀ a5 : Ω,
          W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a3 a4 * W a1 a5 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * W a1 a5 :=
        fun a5 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      rfl
    have h4 : ∀ a3 : Ω,
        (∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 *
            W a3 a4 * W a1 a5 ∂μ ∂μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * degree W a1) *
            (W a0 a3 * degree W a3) := by
      intro a3
      rw [integral_congr_ae (ae_of_all _ (h5 a3))]
      have hre : ∀ a4 : Ω,
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * W a3 a4) * degree W a1 =
            ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * degree W a1) *
              W a3 a4 := fun a4 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      show ((W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3) * degree W a1) *
          degree W a3 = _
      ring
    rw [integral_congr_ae (ae_of_all _ h4), integral_const_mul, ← pathOp]
  have h12 : (∫ a1, ∫ a2,
      (W a0 a1 * W a0 a2 * W a1 a2 * degree W a1) * pathOp W a0 ∂μ ∂μ) =
      pathOp W a0 * leafTri W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, (W a0 a1 * W a0 a2 * W a1 a2 * degree W a1) * pathOp W a0 ∂μ) =
          pathOp W a0 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a1 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 ↦ by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul, ← leafTri]
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
  have hfun : ∀ x : Ω,
      plane (cliqueDensity 2 W) (degree W x) (pathOp W x) =
        cliqueDensity 2 W ^ 4 * (3 - 8 * cliqueDensity 2 W) +
          2 * cliqueDensity 2 W ^ 3 * (5 * cliqueDensity 2 W - 2) * degree W x +
          cliqueDensity 2 W ^ 2 * (5 * cliqueDensity 2 W - 2) * pathOp W x -
          cliqueDensity 2 W ^ 2 * (5 * cliqueDensity 2 W - 2) *
            degree W x ^ 2 := by
    intro x
    simp only [plane]
    ring
  have j0 : Integrable (fun _ : Ω ↦
      cliqueDensity 2 W ^ 4 * (3 - 8 * cliqueDensity 2 W)) μ :=
    integrable_const _
  have j1 : Integrable (fun x : Ω ↦
      2 * cliqueDensity 2 W ^ 3 * (5 * cliqueDensity 2 W - 2) * degree W x) μ :=
    hd.const_mul _
  have j2 : Integrable (fun x : Ω ↦
      cliqueDensity 2 W ^ 2 * (5 * cliqueDensity 2 W - 2) * pathOp W x) μ :=
    hA.const_mul _
  have j3 : Integrable (fun x : Ω ↦
      cliqueDensity 2 W ^ 2 * (5 * cliqueDensity 2 W - 2) *
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

/-- **Atlas 97 dominates its target.** -/
theorem adjTail_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1) ≤
      homDensity adjTail W := by
  have hint1 : Integrable
      (fun x ↦ plane (cliqueDensity 2 W) (degree W x) (pathOp W x)) μ := by
    have hfun : ∀ x : Ω,
        plane (cliqueDensity 2 W) (degree W x) (pathOp W x) =
          cliqueDensity 2 W ^ 4 * (3 - 8 * cliqueDensity 2 W) +
            2 * cliqueDensity 2 W ^ 3 * (5 * cliqueDensity 2 W - 2) * degree W x +
            cliqueDensity 2 W ^ 2 * (5 * cliqueDensity 2 W - 2) * pathOp W x -
            cliqueDensity 2 W ^ 2 * (5 * cliqueDensity 2 W - 2) *
              degree W x ^ 2 := by
      intro x; simp only [plane]; ring
    refine Integrable.congr ?_ (ae_of_all _ fun x ↦ (hfun x).symm)
    exact (((integrable_const _).add ((integrable_degree W).const_mul _)).add
      ((integrable_pathOp W).const_mul _)).sub
      ((integrable_degree_pow W 2).const_mul _)
  have hint2 : Integrable (fun x ↦ pathOp W x * leafTri W x) μ :=
    integrable_of_bdd ((measurable_pathOp W).mul (measurable_leafTri W))
      (C := 1) fun x ↦ by
        have h0 : 0 ≤ pathOp W x * leafTri W x :=
          mul_nonneg (pathOp_nonneg W x) (leafTri_nonneg W x)
        rw [abs_of_nonneg h0]
        exact mul_le_one₀ (pathOp_le_one W x) (leafTri_nonneg W x)
          (leafTri_le_one W x)
  have hmono := integral_mono hint1 hint2 (plane_le_rooted W hp)
  rw [integral_plane W] at hmono
  rw [homDensity_adjTail W]
  exact hmono

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_97 (z : ℝ) :
    affineProd [0, 1, 1, 1, 1, 2] z = z ^ 4 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃`, then `3` on the root `0`, then `4` on `3`, then `5` on the adjacent
root `1`. -/
def iso97 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {none}) {some (some 1)} ≃g
      adjTail where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom97 : IsChromaticPolynomial adjTail
    ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := adjTail) iso97
    (isClique_singleton _ (some (some 1)))
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

theorem count97 (k : ℕ) :
    properAssignmentCount adjTail k =
      (k - 1) * ((k - 1) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := adjTail) iso97
      (isClique_singleton _ (some (some 1))) k,
    properAssignmentCount_attachVertex (isClique_singleton _ none),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 3)).card) = 1 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num97 : IsChromaticNumber adjTail 3 where
  positive := by rw [count97]; decide
  zero_below k hk := by
    rw [count97, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 97 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_97 : Taeyoung.SatisfiesLowerBound adjTail := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := adjTail) hP chrom97
  have hreq : r = 3 := IsChromaticNumber.unique (H := adjTail) hr num97
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := adjTail_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 1, 2] (by norm_num) hone,
      affineProd_97]
    exact hkey

end Taeyoung.Methods.AdjTail
