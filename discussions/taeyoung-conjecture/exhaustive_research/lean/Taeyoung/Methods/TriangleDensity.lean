import Taeyoung.Fisher
import Taeyoung.Methods.Peeling
import Taeyoung.Methods.Link.WeightedGoodmanRpow

/-!
# Triangle density: the sharp lower bound, in this project's vocabulary

`Taeyoung/Fisher/` vendors the proof of Fisher's 1989 triangle-density theorem
on the band `1/2 < p ≤ 2/3`.  It is stated there in the graphon vocabulary of
the odd-cycle development — an unbundled kernel `W : Ω → Ω → ℝ` with a
predicate `IsGraphon`, an `edgeDensity`, and the triangle density written as
`trace μ (compPow μ W 2)`.  This file restates it for the bundled `Graphon Ω μ`
of `Foundation/`, so the catalogue never has to mention the vendored names.

Three things are proved.

* `cliqueDensity_three_eq` — the triangle density peels to the triple
  integral, hence equals `∫ τ`.  The two vocabularies then agree by Fubini:
  `edgeDensity_bridge` and `trace_compPow_bridge`.
* `fisher_triangle_bound` — the sharp bound `t(K₃,W) ≥ (3/2)y(1-y)²` at
  `y = fisherParam p`, for `1/2 < p ≤ 2/3`.
* `goodman_triangle_bound` — the crude bound `t(K₃,W) ≥ p(2p-1)`, valid at
  every density.  Above `p = 2/3` this is all the catalogue needs, so the two
  together cover the whole interval.

The parameter `y = fisherParam p = (1 - √(4-6p))/3` is the mass of the small
part of the extremal three-part graphon; `fisherParam_quadratic` is the
identity `p = (1 + 2y - 3y²)/2` that inverts it, and `fisherParam_mem` places
`y` in `[0, 1/3]`.  Arguments that need the extremal profile are cleanest in
the `y` coordinate, where it is the polynomial `(3/2)y(1-y)²`.
-/

open MeasureTheory

namespace Taeyoung.Methods.TriangleDensity

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The triangle density as a triple integral -/

lemma edgeFinset_top3 :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_top3 (W : Graphon Ω μ) (x : Fin 3 → Ω) :
    graphWeight (⊤ : SimpleGraph (Fin 3)) W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) := by
  rw [graphWeight, edgeFinset_top3]
  simp
  ring

/-- **The triangle density, peeled.** -/
theorem cliqueDensity_three_eq (W : Graphon Ω μ) :
    cliqueDensity 3 W =
      ∫ a0, ∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ ∂μ ∂μ := by
  have hm : Measurable fun y : Fin 3 → Ω ↦
      W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) :=
    ((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
      (measurable_coord_pair W 1 2)
  have hb : ∀ y : Fin 3 → Ω, |W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2)| ≤ 1 := by
    intro y
    have h0 : 0 ≤ W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) :=
      mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
      (W.nonneg _ _) (W.le_one _ _)
  rw [cliqueDensity, homDensity,
    integral_congr_ae (ae_of_all _ fun y ↦ graphWeight_top3 W y)]
  exact integral_assignment_fin_three
    (g := fun a0 a1 a2 ↦ W a0 a1 * W a0 a2 * W a1 a2) hm hb

/-- The triangle density is the mean of the rooted triangle density. -/
theorem cliqueDensity_three_eq_integral_rootedTriangle (W : Graphon Ω μ) :
    cliqueDensity 3 W = ∫ x, rootedTriangle W x ∂μ := by
  rw [cliqueDensity_three_eq]
  rfl

/-! ### Agreement with the vendored vocabulary -/

/-- A bundled graphon is an unbundled one. -/
theorem isGraphon_toFun (W : Graphon Ω μ) :
    OddCycleBound.IsGraphon (fun x y ↦ W x y) μ :=
  ⟨W.measurable, W.nonneg, W.le_one, W.symm⟩

theorem edgeDensity_bridge (W : Graphon Ω μ) :
    OddCycleBound.edgeDensity (fun x y ↦ W x y) μ = cliqueDensity 2 W := by
  rw [← integral_degree W]
  rfl

theorem trace_compPow_bridge (W : Graphon Ω μ) :
    OddCycleBound.trace μ (OddCycleBound.compPow μ (fun x y ↦ W x y) 2) =
      cliqueDensity 3 W := by
  rw [cliqueDensity_three_eq]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  show (∫ a1, W a0 a1 * (∫ a2, W a1 a2 * W a2 a0 ∂μ) ∂μ)
      = ∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ ∂μ
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  show W a0 a1 * (∫ a2, W a1 a2 * W a2 a0 ∂μ)
      = ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  show W a0 a1 * (W a1 a2 * W a2 a0) = W a0 a1 * W a0 a2 * W a1 a2
  rw [W.symm a2 a0]
  ring

/-! ### The extremal parameter -/

/-- `y = (1 - √(4-6p))/3`: the small part's mass in the extremal three-part
graphon of edge density `p`. -/
noncomputable def fisherParam (p : ℝ) : ℝ := (1 - Real.sqrt (4 - 6 * p)) / 3

/-- The extremal triangle density, in the parameter `y`. -/
noncomputable def fisherProfile (p : ℝ) : ℝ :=
  3 / 2 * fisherParam p * (1 - fisherParam p) ^ 2

/-- `y` lies in `[0, 1/3]` for `1/2 ≤ p ≤ 2/3`. -/
theorem fisherParam_mem {p : ℝ} (hlo : 1 / 2 ≤ p) :
    0 ≤ fisherParam p ∧ fisherParam p ≤ 1 / 3 := by
  constructor
  · rw [fisherParam, le_div_iff₀ (by norm_num : (0:ℝ) < 3), zero_mul, sub_nonneg]
    rcases le_or_gt (4 - 6 * p) 0 with h | h
    · simpa [Real.sqrt_eq_zero_of_nonpos h] using (by norm_num : (0:ℝ) ≤ 1)
    · rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
  · rw [fisherParam, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
    have := Real.sqrt_nonneg (4 - 6 * p)
    linarith

/-- The inverse relation `p = (1 + 2y - 3y²)/2`, valid where `4 - 6p ≥ 0`. -/
theorem fisherParam_quadratic {p : ℝ} (hhi : p ≤ 2 / 3) :
    (1 + 2 * fisherParam p - 3 * fisherParam p ^ 2) / 2 = p := by
  have hnn : (0 : ℝ) ≤ 4 - 6 * p := by linarith
  have hsq : Real.sqrt (4 - 6 * p) ^ 2 = 4 - 6 * p := Real.sq_sqrt hnn
  rw [fisherParam]
  field_simp
  nlinarith [hsq]

/-! ### The two lower bounds -/

/-- **Fisher's sharp triangle bound**, `1/2 < p ≤ 2/3`, restated for a bundled
graphon.  The proof is vendored in `Taeyoung/Fisher/`. -/
theorem fisher_triangle_bound (W : Graphon Ω μ)
    (hlo : 1 / 2 < cliqueDensity 2 W) (hhi : cliqueDensity 2 W ≤ 2 / 3) :
    fisherProfile (cliqueDensity 2 W) ≤ cliqueDensity 3 W := by
  have hE := edgeDensity_bridge W
  have h := OddCycleBound.triangleDensityLowerBound_twoThirds
    (isGraphon_toFun W) (by rw [hE]; exact hlo) (by rw [hE]; exact hhi)
  simp only [hE, trace_compPow_bridge W] at h
  exact h

/-- **Goodman's triangle bound**, `t(K₃,W) ≥ p(2p-1)`, at every density.  This
is the weighted rooted-triangle inequality at exponent `0`, divided by `p`. -/
theorem goodman_triangle_bound (W : Graphon Ω μ) (hp : 0 < cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ≤ cliqueDensity 3 W := by
  set p := cliqueDensity 2 W with hpdef
  have hjen : p ^ ((0 : ℝ) + 2) ≤ momentR W ((0 : ℝ) + 2) :=
    rpow_le_momentR W (by norm_num)
  have hwt := weighted_rootedTriangle_rpow W (s := (0 : ℝ)) le_rfl
  have hzero : (∫ x, degree W x ^ (0 : ℝ) * rootedTriangle W x ∂μ)
      = cliqueDensity 3 W := by
    rw [cliqueDensity_three_eq_integral_rootedTriangle]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show degree W x ^ (0 : ℝ) * rootedTriangle W x = rootedTriangle W x
    rw [Real.rpow_zero, one_mul]
  rw [hzero] at hwt
  rcases le_or_gt (2 * p - 1) 0 with h2p | h2p
  · have h3 : 0 ≤ cliqueDensity 3 W := by
      rw [cliqueDensity_three_eq_integral_rootedTriangle]
      exact integral_nonneg fun x ↦ rootedTriangle_nonneg W x
    nlinarith
  · have hstep : (2 * p - 1) * p ^ ((0 : ℝ) + 2) ≤ p * cliqueDensity 3 W :=
      le_trans (mul_le_mul_of_nonneg_left hjen h2p.le) hwt
    have hsq : p ^ ((0 : ℝ) + 2) = p ^ 2 := by
      rw [show (0 : ℝ) + 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hsq] at hstep
    have : p * (p * (2 * p - 1)) ≤ p * cliqueDensity 3 W := by nlinarith [hstep]
    exact le_of_mul_le_mul_left this hp

end Taeyoung.Methods.TriangleDensity
