import Taeyoung.Methods.Atlas160.Scalar
import Taeyoung.Methods.K4Tail.Link
import Taeyoung.Methods.K4Tail.Rows

/-!
# Atlas 160: the link reduction

The scalar plane of `Atlas160/Scalar.lean`, transported to a point of the
graphon.  The quantity being bounded is the *signed* weight
`(2A(x) - p)·κ₄(x)`, where `κ₄` is the rooted `K₄` density; it is what the page
reduction `t(H,W) ≥ 2J - p·t(K₄,W)` leaves behind after conditioning at a clique
vertex.

Three pointwise facts feed the three regions of the plane.

* `s = 2A(x) - p ≤ 0` — the sign is wrong, so the bound must come from an
  *upper* estimate on `κ₄`.  `rootedK4_le_cube` supplies `κ₄ ≤ d³`, the star
  weight alone; this is what the note's `d³s` branch needs, and it is sharp at
  the balanced multipartite graphon.
* `s ≥ 0` and `2s ≤ d²` — nonnegativity of `s·κ₄` suffices.
* `s ≥ 0` and `2s ≥ d²` — Goodman inside the link, in the truncated form
  `K4Tail.mul_rootedK4_ge`, which is shared verbatim with Atlas 142.

The feasibility `A(x) ≥ d(x) + p - 1` is proved here as well: it is what pins
the lower face of the negative region, and it is one application of
`(1-r)(1-s) ≥ 0`.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas160

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.K4Tail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The lower feasibility bound `A ≥ d + p - 1` -/

lemma integrable_row (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun y ↦ W x y) μ :=
  integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
    rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y

lemma integrable_row_mul_degree (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun y ↦ W x y * degree W y) μ :=
  integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_degree W))
    (C := 1) fun y ↦ by
      rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
      exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)

/-- `A(x) ≥ d(x) + p - 1`, from `(1 - W(x,y))(1 - d(y)) ≥ 0`. -/
theorem degree_add_sub_le_pathOp (W : Graphon Ω μ) (x : Ω) :
    degree W x + cliqueDensity 2 W - 1 ≤ pathOp W x := by
  have hI1 := integrable_row W x
  have hI2 := integrable_degree W
  have hI3 := integrable_row_mul_degree W x
  have e1 : Integrable (fun y ↦ (1 : ℝ) - W x y) μ :=
    ((integrable_const (1 : ℝ)).sub hI1).congr (ae_of_all _ fun _ ↦ rfl)
  have e2 : Integrable (fun y ↦ (1 : ℝ) - W x y - degree W y) μ :=
    (e1.sub hI2).congr (ae_of_all _ fun _ ↦ rfl)
  have hval : (∫ y, ((1 : ℝ) - W x y - degree W y + W x y * degree W y) ∂μ) =
      1 - degree W x - cliqueDensity 2 W + pathOp W x := by
    rw [integral_add e2 hI3, integral_sub e1 hI2,
      integral_sub (integrable_const (1 : ℝ)) hI1, integral_const,
      integral_degree W]
    simp [degree, pathOp]
  have hnn : 0 ≤ ∫ y, ((1 : ℝ) - W x y - degree W y + W x y * degree W y) ∂μ := by
    refine integral_nonneg fun y ↦ ?_
    show (0 : ℝ) ≤ 1 - W x y - degree W y + W x y * degree W y
    nlinarith [W.nonneg x y, W.le_one x y, degree_nonneg W y, degree_le_one W y]
  rw [hval] at hnn
  linarith

/-! ### The rooted `K₄` never exceeds the star weight -/

/-- `κ₄(x) ≤ d(x)³`: drop the three link edges.  Above the degenerate set this
is `homDensity ≤ 1` inside the link; on it, `W(x,·)` vanishes almost everywhere
and both sides are zero. -/
theorem rootedK4_le_cube (W : Graphon Ω μ) (x : Ω) :
    rootedK4 W x ≤ degree W x ^ 3 := by
  rcases eq_or_lt_of_le (degree_nonneg W x) with hd | hd
  · -- the degenerate fibre
    have hdz : degree W x = 0 := hd.symm
    have hae : ∀ᵐ y ∂μ, W x y = 0 := by
      have h0 : (∫ y, W x y ∂μ) = 0 := hdz
      have := (integral_eq_zero_iff_of_nonneg (fun y ↦ W.nonneg x y)
        (integrable_row W x)).mp h0
      filter_upwards [this] with y hy using hy
    have hzero : rootedK4 W x = 0 := by
      rw [rootedK4_eq]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae] with y0 hy0
      have hinner : ∀ y1 y2 : Ω, W x y0 * W x y1 * W x y2 *
          (W y0 y1 * W y0 y2 * W y1 y2) = 0 := by
        intro y1 y2; rw [hy0]; ring
      simp only [hinner, integral_zero]
      rfl
    rw [hzero, hdz]
    norm_num
  · haveI := isProbabilityMeasure_linkMeasure W hd
    rw [rootedK4, rootedDensity_eq _ W hd]
    have h1 : homDensity (⊤ : SimpleGraph (Fin 3)) (linkGraphon W x) ≤ 1 :=
      homDensity_le_one _ _
    have h0 : (0 : ℝ) < degree W x ^ 3 := by positivity
    nlinarith [h1, h0]

/-! ### The pointwise supporting-plane bound -/

/-- **The scalar plane, transported.**  `L_p(d(x), A(x))` lies under the signed
rooted weight at every point of the graphon, degenerate fibres included. -/
theorem plane_le_signed (W : Graphon Ω μ)
    (hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W) (x : Ω) :
    plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ≤
      (2 * pathOp W x - cliqueDensity 2 W) * rootedK4 W x := by
  have hp1 : cliqueDensity 2 W ≤ 1 := cliqueDensity_le_one 2 W
  have hd0 : 0 ≤ degree W x := degree_nonneg W x
  have hd1 : degree W x ≤ 1 := degree_le_one W x
  have ha0 : 0 ≤ pathOp W x := pathOp_nonneg W x
  have had : pathOp W x ≤ degree W x := pathOp_le_degree W x
  have hlo : degree W x + cliqueDensity 2 W - 1 ≤ pathOp W x :=
    degree_add_sub_le_pathOp W x
  have hk0 : 0 ≤ rootedK4 W x := rootedK4_nonneg W x
  have hkc : rootedK4 W x ≤ degree W x ^ 3 := rootedK4_le_cube W x
  rcases le_total (2 * pathOp W x - cliqueDensity 2 W) 0 with hs | hs
  · -- negative region: the cube bound reverses correctly
    have hplane := plane_le_neg hp hp1 hd0 hd1 hlo hs
    nlinarith [hplane, hkc, hs, hk0]
  · rcases le_total (2 * (2 * pathOp W x - cliqueDensity 2 W) -
      degree W x ^ 2) 0 with hv | hv
    · -- inactive region: the plane is already nonpositive
      have hplane := plane_nonpos (p := cliqueDensity 2 W) (d := degree W x)
        (a := pathOp W x) hp (by linarith)
      nlinarith [hplane, hk0, hs]
    · -- active region
      have hdpos : 0 < degree W x := by
        rcases eq_or_lt_of_le hd0 with hd | hd
        · exfalso
          have haz : pathOp W x = 0 := le_antisymm (by rw [hd]; exact had) ha0
          rw [haz] at hs
          have : (0 : ℝ) < cliqueDensity 2 W := by linarith
          linarith
        · exact hd
      have hlink := mul_rootedK4_ge W x
      rw [max_eq_left hs, max_eq_left hv] at hlink
      have hmul : (2 * pathOp W x - cliqueDensity 2 W) *
          ((2 * pathOp W x - cliqueDensity 2 W) *
            (2 * (2 * pathOp W x - cliqueDensity 2 W) - degree W x ^ 2)) ≤
          (2 * pathOp W x - cliqueDensity 2 W) *
            (degree W x * rootedK4 W x) :=
        mul_le_mul_of_nonneg_left hlink hs
      have hact := plane_le_active hp hp1 hd0 hd1 had (by linarith)
      have hchain : degree W x *
          plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ≤
          degree W x * ((2 * pathOp W x - cliqueDensity 2 W) * rootedK4 W x) := by
        nlinarith [hact, hmul]
      exact le_of_mul_le_mul_left hchain hdpos

end Taeyoung.Methods.Atlas160
