import Taeyoung.Methods.Atlas126.Link
import Taeyoung.Methods.Atlas160.Link
import Taeyoung.Methods.K4Tail.Link
import Taeyoung.Methods.Atlas178.Link
import Taeyoung.Methods.Atlas126.Coloring
import Taeyoung.Methods.TriangleDensity

/-!
# Atlas 126: the rooted factorization and the integrated bound

`notes/atlas126_triangle_c4_vertex_supporting_plane.tex` §2 and §7.  Rooting at
the cut vertex gives the exact identity

```
t(H₁₂₆,W) = ∫ τ(x)·r₄(x) dμ(x),
```

which is the six-fold peel below: the two `C₄` neighbours of the root collapse
to `b_x`, the opposite `C₄` vertex integrates `b_x²` to `r₄`, and the two
triangle vertices collapse to `τ`.

Everything after that is scalar.  `Atlas126.Link.projection` bounds `r₄` below,
and the note's supporting plane

```
F_p(d,a,t) = t³/d + t(a-t)²/(1-d) ≥ C(p) + β(d-p) + γ(a-d²) + λ(t-g)
```

is carried here as the explicit hypothesis `ScalarPlane`, stated multiplied
through by `d(1-d)` so that it is a polynomial statement with no side
conditions on `d`.  Given it, `graph126_bound` proves the graphon inequality:
the two mean-zero corrections integrate away, `λ(T-g) ≥ 0` is the triangle
input, and the two degenerate fibres `d = 0` and `d = 1` are settled by the
note's scalar gaps `G₀` and `G₁`.

The `d = 1` fibre does not need the note's endpoint convention.  Feasibility
alone gives `a ≥ p` and `τ ≥ p`, and one more Cauchy--Schwarz gives `r₄ ≥ a²`,
so `τ·r₄ ≥ p³` follows from the same three inequalities that bound the interior.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.Atlas126

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.K4Tail
  Taeyoung.Methods.Negative Taeyoung.Methods.TriangleDensity
  Taeyoung.Methods.BookTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma edgeFinset_graph126 :
    graph126.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 4), s(0, 5), s(3, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_graph126 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight graph126 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 4) *
        W (x 0) (x 5) * W (x 3) (x 4) * W (x 3) (x 5) := by
  rw [graphWeight, edgeFinset_graph126]
  simp
  ring

/-! ### The rooted factorization -/

set_option maxHeartbeats 1000000 in
/-- **The density of Atlas 126 is `∫ τ·r₄`.** -/
theorem homDensity_graph126 (W : Graphon Ω μ) :
    homDensity graph126 W =
      ∫ x, rootedTriangle W x * rootedC4 W x ∂μ := by
  have hm : Measurable (graphWeight graph126 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight graph126 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  have hm' : Measurable fun y : Fin 6 → Ω ↦
      W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 4) *
        W (y 0) (y 5) * W (y 3) (y 4) * W (y 3) (y 5) :=
    (((((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
      (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 0 4)).mul
      (measurable_coord_pair W 0 5)).mul (measurable_coord_pair W 3 4)).mul
      (measurable_coord_pair W 3 5))
  have hb' : ∀ y : Fin 6 → Ω,
      |W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 4) *
        W (y 0) (y 5) * W (y 3) (y 4) * W (y 3) (y 5)| ≤ 1 := by
    intro y
    rw [← graphWeight_graph126 W y]
    exact hb y
  rw [homDensity,
    integral_congr_ae (ae_of_all _ fun y ↦ graphWeight_graph126 W y),
    integral_assignment_fin_six (g := fun a0 a1 a2 a3 a4 a5 : Ω ↦
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a4 * W a0 a5 * W a3 a4 * W a3 a5)
      hm' hb']
  -- collapse `a5`, `a4`, `a3` to `r₄` and then `a2`, `a1` to `τ`
  have h5 : ∀ a0 a1 a2 a3 a4 : Ω,
      (∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a4 * W a0 a5 * W a3 a4 *
          W a3 a5 ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a4 * W a3 a4) * pairOp W a3 a0 := by
    intro a0 a1 a2 a3 a4
    rw [pairOp, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a5 ↦ ?_)
    simp only []
    rw [W.symm a0 a5]
    ring
  have h4 : ∀ a0 a1 a2 a3 : Ω,
      (∫ a4, (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a4 * W a3 a4) *
          pairOp W a3 a0 ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * pairOp W a3 a0 ^ 2 := by
    intro a0 a1 a2 a3
    have hcong : ∀ a4 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a4 * W a3 a4) * pairOp W a3 a0
          = (W a0 a1 * W a0 a2 * W a1 a2 * pairOp W a3 a0) *
            (W a3 a4 * W a4 a0) := by
      intro a4; rw [W.symm a0 a4]; ring
    rw [integral_congr_ae (ae_of_all _ hcong), integral_const_mul]
    show (W a0 a1 * W a0 a2 * W a1 a2 * pairOp W a3 a0) * pairOp W a3 a0
      = W a0 a1 * W a0 a2 * W a1 a2 * pairOp W a3 a0 ^ 2
    ring
  have h3 : ∀ a0 a1 a2 : Ω,
      (∫ a3, (W a0 a1 * W a0 a2 * W a1 a2) * pairOp W a3 a0 ^ 2 ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2) * rootedC4 W a0 := by
    intro a0 a1 a2
    rw [integral_const_mul, rootedC4]
    refine congrArg _ (integral_congr_ae (ae_of_all _ fun a3 ↦ ?_))
    simp only []
    rw [pairOp_symm W a3 a0]
  have h2 : ∀ a0 a1 : Ω,
      (∫ a2, (W a0 a1 * W a0 a2 * W a1 a2) * rootedC4 W a0 ∂μ) =
        (W a0 a1 * rootedC4 W a0) * pairOp W a1 a0 := by
    intro a0 a1
    have hcong : ∀ a2 : Ω, (W a0 a1 * W a0 a2 * W a1 a2) * rootedC4 W a0
        = (W a0 a1 * rootedC4 W a0) * (W a1 a2 * W a2 a0) := by
      intro a2; rw [W.symm a0 a2]; ring
    rw [integral_congr_ae (ae_of_all _ hcong), integral_const_mul, pairOp]
  have h1 : ∀ a0 : Ω,
      (∫ a1, (W a0 a1 * rootedC4 W a0) * pairOp W a1 a0 ∂μ) =
        rootedTriangle W a0 * rootedC4 W a0 := by
    intro a0
    have hcong : ∀ a1 : Ω, (W a0 a1 * rootedC4 W a0) * pairOp W a1 a0
        = rootedC4 W a0 * (W a0 a1 * pairOp W a0 a1) := by
      intro a1; rw [pairOp_symm W a1 a0]; ring
    rw [integral_congr_ae (ae_of_all _ hcong), integral_const_mul,
      integral_row_mul_pairOp W a0]
    ring
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_congr_ae (ae_of_all _ fun a1 ↦
    integral_congr_ae (ae_of_all _ fun a2 ↦
      integral_congr_ae (ae_of_all _ fun a3 ↦
        integral_congr_ae (ae_of_all _ fun a4 ↦ h5 a0 a1 a2 a3 a4))))]
  rw [integral_congr_ae (ae_of_all _ fun a1 ↦
    integral_congr_ae (ae_of_all _ fun a2 ↦
      integral_congr_ae (ae_of_all _ fun a3 ↦ h4 a0 a1 a2 a3)))]
  rw [integral_congr_ae (ae_of_all _ fun a1 ↦
    integral_congr_ae (ae_of_all _ fun a2 ↦ h3 a0 a1 a2))]
  rw [integral_congr_ae (ae_of_all _ fun a1 ↦ h2 a0 a1), h1 a0]

/-! ### The scalar supporting plane, as a hypothesis -/

/-- The note's Lemma 5.1, multiplied through by `d(1-d)`.  In this form it is a
polynomial statement over the exact feasible region and needs no convention at
`d ∈ {0,1}`. -/
def ScalarPlane (p C beta gamma lam g : ℝ) : Prop :=
  ∀ d a t : ℝ, 0 ≤ d → d ≤ 1 → 0 ≤ a → d + p - 1 ≤ a → a ≤ d →
    0 ≤ t → 2 * a - p ≤ t → t ≤ a → t ≤ d ^ 2 →
    d * (1 - d) * (C + beta * (d - p) + gamma * (a - d ^ 2) + lam * (t - g)) ≤
      (1 - d) * t ^ 3 + d * t * (a - t) ^ 2

/-- **The plane, transported to a point of the graphon.** -/
theorem plane_le_rooted (W : Graphon Ω μ) {C beta gamma lam g : ℝ}
    (hG0 : C ≤ beta * cliqueDensity 2 W + lam * g)
    (hG1 : C + beta * (1 - cliqueDensity 2 W)
      + gamma * (cliqueDensity 2 W - 1)
      + lam * (cliqueDensity 2 W - g) ≤ cliqueDensity 2 W ^ 3)
    (hplane : ScalarPlane (cliqueDensity 2 W) C beta gamma lam g) (x : Ω) :
    C + beta * (degree W x - cliqueDensity 2 W)
        + gamma * (pathOp W x - degree W x ^ 2)
        + lam * (rootedTriangle W x - g) ≤
      rootedTriangle W x * rootedC4 W x := by
  set p := cliqueDensity 2 W with hpdef
  have hd0 : 0 ≤ degree W x := degree_nonneg W x
  have hd1 : degree W x ≤ 1 := degree_le_one W x
  have ha0 : 0 ≤ pathOp W x := pathOp_nonneg W x
  have haD : pathOp W x ≤ degree W x := pathOp_le_degree W x
  have haL : degree W x + p - 1 ≤ pathOp W x := Atlas160.degree_add_sub_le_pathOp W x
  have ht0 : 0 ≤ rootedTriangle W x := rootedTriangle_nonneg W x
  have htL : 2 * pathOp W x - p ≤ rootedTriangle W x := rootedTriangle_ge W x
  have htA : rootedTriangle W x ≤ pathOp W x := rootedTriangle_le_pathOp W x
  have htD : rootedTriangle W x ≤ degree W x ^ 2 :=
    Atlas178.rootedTriangle_le_sq_degree W x
  have hr0 : 0 ≤ rootedC4 W x := rootedC4_nonneg W x
  rcases eq_or_lt_of_le hd0 with hdz | hdpos
  · -- `d = 0`: feasibility collapses `a` and `τ` to zero
    have hd : degree W x = 0 := hdz.symm
    have ha : pathOp W x = 0 := le_antisymm (by rw [← hd]; exact haD) ha0
    have ht : rootedTriangle W x = 0 :=
      le_antisymm (by rw [← ha]; exact htA) ht0
    rw [hd, ha, ht]
    simp only [zero_mul]
    nlinarith [hG0]
  · rcases eq_or_lt_of_le hd1 with hdo | hdlt
    · -- `d = 1`: `a ≥ p`, `τ ≥ p`, and `r₄ ≥ a²`
      have hd : degree W x = 1 := hdo
      have hap : p ≤ pathOp W x := by rw [hd] at haL; linarith
      -- `τ ≤ a` and `τ ≥ 2a - p` force `a ≤ p`, hence `a = τ = p`
      have hpa : pathOp W x = p := le_antisymm (by linarith [htL, htA]) hap
      have hpt : rootedTriangle W x = p := by
        refine le_antisymm ?_ (by linarith [htL, hpa])
        rw [← hpa]; exact htA
      have hp0 : 0 ≤ p := cliqueDensity_nonneg 2 W
      have hrsq : pathOp W x ^ 2 ≤ rootedC4 W x := sq_pathOp_le_rootedC4 W x
      have hrp : p ^ 2 ≤ rootedC4 W x := by rw [hpa] at hrsq; exact hrsq
      have hmain : p * p ^ 2 ≤ rootedTriangle W x * rootedC4 W x := by
        rw [hpt]
        exact mul_le_mul_of_nonneg_left hrp hp0
      rw [hd, hpa, hpt]
      nlinarith [hmain, hG1, hp0]
    · -- the interior: divide the cleared plane by `d(1-d) > 0`
      have hpos : 0 < degree W x * (1 - degree W x) := by
        apply mul_pos hdpos; linarith
      have hproj := projection W x
      have hstep : degree W x * (1 - degree W x) *
          (C + beta * (degree W x - p) + gamma * (pathOp W x - degree W x ^ 2)
            + lam * (rootedTriangle W x - g)) ≤
          degree W x * (1 - degree W x) *
            (rootedTriangle W x * rootedC4 W x) := by
        have hA := hplane (degree W x) (pathOp W x) (rootedTriangle W x)
          hd0 hd1 ha0 haL haD ht0 htL htA htD
        nlinarith [hA, hproj, ht0, hd0, hd1]
      exact le_of_mul_le_mul_left hstep hpos

/-! ### The integrated bound -/

/-- **Atlas 126 dominates its target, given the scalar plane.** -/
theorem graph126_bound (W : Graphon Ω μ) {C beta gamma lam g : ℝ}
    (hlam : 0 ≤ lam)
    (hg : g ≤ cliqueDensity 3 W)
    (hG0 : C ≤ beta * cliqueDensity 2 W + lam * g)
    (hG1 : C + beta * (1 - cliqueDensity 2 W)
      + gamma * (cliqueDensity 2 W - 1)
      + lam * (cliqueDensity 2 W - g) ≤ cliqueDensity 2 W ^ 3)
    (hplane : ScalarPlane (cliqueDensity 2 W) C beta gamma lam g) :
    C ≤ homDensity graph126 W := by
  set p := cliqueDensity 2 W with hpdef
  have hd := integrable_degree W
  have hA := integrable_pathOp W
  have hd2 := integrable_degree_pow W 2
  have hτ : Integrable (rootedTriangle W) μ :=
    integrable_of_bdd (measurable_rootedTriangle W) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (rootedTriangle_nonneg W x)]
      exact rootedTriangle_le_one W x
  have i0 : Integrable (fun _ : Ω ↦ C - beta * p - gamma * 0 - lam * g) μ :=
    integrable_const _
  have i1 : Integrable (fun x : Ω ↦ beta * degree W x) μ := hd.const_mul _
  have i2 : Integrable (fun x : Ω ↦ gamma * pathOp W x) μ := hA.const_mul _
  have i3 : Integrable (fun x : Ω ↦ gamma * degree W x ^ 2) μ := hd2.const_mul _
  have i4 : Integrable (fun x : Ω ↦ lam * rootedTriangle W x) μ := hτ.const_mul _
  set G : Ω → ℝ := fun x ↦ C + beta * (degree W x - p)
    + gamma * (pathOp W x - degree W x ^ 2)
    + lam * (rootedTriangle W x - g) with hGdef
  have hGsplit : ∀ x : Ω, G x =
      (C - beta * p - gamma * 0 - lam * g) + beta * degree W x
        + gamma * pathOp W x - gamma * degree W x ^ 2
        + lam * rootedTriangle W x := by
    intro x; simp only [hGdef]; ring
  have hGint : Integrable G μ := by
    refine Integrable.congr ?_ (ae_of_all _ fun x ↦ (hGsplit x).symm)
    exact ((((i0.add i1).add i2).sub i3).add i4)
  have hGval : (∫ x, G x ∂μ) = C + lam * (cliqueDensity 3 W - g) := by
    have e1 := integral_add (((i0.add i1).add i2).sub i3) i4
    have e2 := integral_sub ((i0.add i1).add i2) i3
    have e3 := integral_add (i0.add i1) i2
    have e4 := integral_add i0 i1
    simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 e3 e4
    rw [integral_congr_ae (ae_of_all _ hGsplit), e1, e2, e3, e4, integral_const,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_degree, integral_pathOp, moment,
      ← cliqueDensity_three_eq_integral_rootedTriangle]
    simp
    ring
  have hprodint : Integrable (fun x ↦ rootedTriangle W x * rootedC4 W x) μ :=
    integrable_of_bdd ((measurable_rootedTriangle W).mul (measurable_rootedC4 W))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (rootedTriangle_nonneg W x)
          (rootedC4_nonneg W x))]
        exact mul_le_one₀ (rootedTriangle_le_one W x) (rootedC4_nonneg W x)
          (rootedC4_le_one W x)
  have hmono : (∫ x, G x ∂μ) ≤ ∫ x, rootedTriangle W x * rootedC4 W x ∂μ :=
    integral_mono hGint hprodint fun x ↦
      plane_le_rooted W hG0 hG1 hplane x
  rw [hGval, ← homDensity_graph126 W] at hmono
  nlinarith [hmono, hlam, hg]

end Taeyoung.Methods.Atlas126
