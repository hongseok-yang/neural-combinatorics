import Taeyoung.Methods.OddLeaf.Holder
import Taeyoung.Methods.OddCycleC5.Chromatic

/-!
# Atlas 104: the five-cycle with one pendant leaf

`notes/odd_cycle_one_leaf.tex` at `m = 5`.  Peeling the leaf gives

```
t(C₅⁺,W) = ∫ F(y)·d(y₀),      F = graphWeight c5 W,
```

and `F` is invariant under the cyclic rotation of the five coordinates, so the
same integral results with the degree at any coordinate.  Averaging the five and
applying the arithmetic–geometric mean inequality gives

```
t(C₅⁺,W) ≥ ∫ F(y)·∏ᵢ d(yᵢ)^{1/5} = M⁵·t(C₅,W;ν),   dν = (d^{1/5}/M)dμ.
```

The already-verified analytic `C₅` theorem applies verbatim on `(Ω,ν)`, and the
row closes with three scalar facts about `K = M⁵` and the biased edge density
`s`: `K ≤ p` (Jensen), `p⁷ ≤ K²s⁵` (the fractional Hölder of `Holder.lean`,
because `N = M²s`), and the rescaling below.

**The scalar rescaling is proved differently from the note.**  The note deduces
it from the strict monotonicity of `ψ₅(s) = φ₅(s)/s^{5/2}`, differentiating a
function with two half-integer powers.  Here no derivative and no half-integer
power appears.  Writing `φ₅(u) = u·h(u)` with `h(u) = (2u-1)(2u²-2u+1)`, the
whole content is the polynomial inequality

```
s³·h(p)² ≤ p³·h(s)²      (1/2 ≤ p ≤ s),
```

and after `p = 1/2 + a²`, `s = 1/2 + a² + b²` its cleared form
`8(p³h(s)² - s³h(p)²)` is a polynomial in `a, b` all of whose coefficients are
nonnegative and all of whose exponents are even — one `ring` identity and
`positivity`.
-/

open MeasureTheory Finset Polynomial

open scoped ENNReal

namespace Taeyoung.Methods.OddLeaf

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.OddCycleC5

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The scalar rescaling -/

/-- `φ₅(u) = u⁵ - u(1-u)⁴ = u·(2u-1)(2u²-2u+1)`. -/
lemma phi_eq (u : ℝ) :
    u ^ 5 - u * (1 - u) ^ 4 = u * ((2 * u - 1) * (2 * u ^ 2 - 2 * u + 1)) := by
  ring

/-- **`h(s)²/s³` is increasing on `[1/2,1]`**, in cleared form. -/
theorem scalar_mono {p s : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hps : p ≤ s) :
    s ^ 3 * ((2 * p - 1) * (2 * p ^ 2 - 2 * p + 1)) ^ 2 ≤
      p ^ 3 * ((2 * s - 1) * (2 * s ^ 2 - 2 * s + 1)) ^ 2 := by
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, p = 1 / 2 + a ^ 2 :=
    ⟨Real.sqrt (p - 1 / 2), by
      rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ p - 1 / 2)]; ring⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ, s = 1 / 2 + a ^ 2 + b ^ 2 :=
    ⟨Real.sqrt (s - (1 / 2 + a ^ 2)), by
      rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ s - (1 / 2 + a ^ 2))]; ring⟩
  have hid : 8 * ((1 / 2 + a ^ 2) ^ 3 *
        ((2 * (1 / 2 + a ^ 2 + b ^ 2) - 1) *
          (2 * (1 / 2 + a ^ 2 + b ^ 2) ^ 2 - 2 * (1 / 2 + a ^ 2 + b ^ 2) + 1)) ^ 2 -
      (1 / 2 + a ^ 2 + b ^ 2) ^ 3 *
        ((2 * (1 / 2 + a ^ 2) - 1) *
          (2 * (1 / 2 + a ^ 2) ^ 2 - 2 * (1 / 2 + a ^ 2) + 1)) ^ 2) =
      b ^ 2 * (384 * a ^ 16 +
        1536 * a ^ 14 * b ^ 2 + 768 * a ^ 14 +
        2432 * a ^ 12 * b ^ 4 + 2688 * a ^ 12 * b ^ 2 + 544 * a ^ 12 +
        1920 * a ^ 10 * b ^ 6 + 3840 * a ^ 10 * b ^ 4 +
        1632 * a ^ 10 * b ^ 2 + 288 * a ^ 10 +
        768 * a ^ 8 * b ^ 8 + 2880 * a ^ 8 * b ^ 6 + 2112 * a ^ 8 * b ^ 4 +
        720 * a ^ 8 * b ^ 2 + 136 * a ^ 8 +
        128 * a ^ 6 * b ^ 10 + 1152 * a ^ 6 * b ^ 8 + 1504 * a ^ 6 * b ^ 6 +
        704 * a ^ 6 * b ^ 4 + 272 * a ^ 6 * b ^ 2 + 32 * a ^ 6 +
        192 * a ^ 4 * b ^ 10 + 576 * a ^ 4 * b ^ 8 + 336 * a ^ 4 * b ^ 6 +
        184 * a ^ 4 * b ^ 4 + 48 * a ^ 4 * b ^ 2 + 6 * a ^ 4 +
        96 * a ^ 2 * b ^ 10 + 96 * a ^ 2 * b ^ 8 + 48 * a ^ 2 * b ^ 6 +
        32 * a ^ 2 * b ^ 4 + 6 * a ^ 2 * b ^ 2 + 2 * a ^ 2 +
        16 * b ^ 10 + 8 * b ^ 6 + b ^ 2) := by ring
  have hnn : (0 : ℝ) ≤ b ^ 2 * (384 * a ^ 16 +
        1536 * a ^ 14 * b ^ 2 + 768 * a ^ 14 +
        2432 * a ^ 12 * b ^ 4 + 2688 * a ^ 12 * b ^ 2 + 544 * a ^ 12 +
        1920 * a ^ 10 * b ^ 6 + 3840 * a ^ 10 * b ^ 4 +
        1632 * a ^ 10 * b ^ 2 + 288 * a ^ 10 +
        768 * a ^ 8 * b ^ 8 + 2880 * a ^ 8 * b ^ 6 + 2112 * a ^ 8 * b ^ 4 +
        720 * a ^ 8 * b ^ 2 + 136 * a ^ 8 +
        128 * a ^ 6 * b ^ 10 + 1152 * a ^ 6 * b ^ 8 + 1504 * a ^ 6 * b ^ 6 +
        704 * a ^ 6 * b ^ 4 + 272 * a ^ 6 * b ^ 2 + 32 * a ^ 6 +
        192 * a ^ 4 * b ^ 10 + 576 * a ^ 4 * b ^ 8 + 336 * a ^ 4 * b ^ 6 +
        184 * a ^ 4 * b ^ 4 + 48 * a ^ 4 * b ^ 2 + 6 * a ^ 4 +
        96 * a ^ 2 * b ^ 10 + 96 * a ^ 2 * b ^ 8 + 48 * a ^ 2 * b ^ 6 +
        32 * a ^ 2 * b ^ 4 + 6 * a ^ 2 * b ^ 2 + 2 * a ^ 2 +
        16 * b ^ 10 + 8 * b ^ 6 + b ^ 2) := by positivity
  linarith [hid, hnn]

/-- **The odd-cycle rescaling**, in the form the graphon proof needs. -/
theorem transfer {p s K : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hs0 : 0 ≤ s)
    (hK0 : 0 < K) (hKp : K ≤ p) (hKs : p ^ 7 ≤ K ^ 2 * s ^ 5) :
    p * (p ^ 5 - p * (1 - p) ^ 4) ≤ K * (s ^ 5 - s * (1 - s) ^ 4) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hps : p ≤ s := by
    refine le_of_pow_le_pow_left₀ (n := 5) (by norm_num) hs0 ?_
    have hK2 : K ^ 2 ≤ p ^ 2 := by nlinarith [hK0, hKp]
    have h1 : K ^ 2 * s ^ 5 ≤ p ^ 2 * s ^ 5 :=
      mul_le_mul_of_nonneg_right hK2 (pow_nonneg hs0 5)
    have h3 : p ^ 2 * p ^ 5 ≤ p ^ 2 * s ^ 5 := by
      rw [show p ^ 2 * p ^ 5 = p ^ 7 by ring]
      exact le_trans hKs h1
    exact le_of_mul_le_mul_left h3 (by positivity)
  have hs2 : (1 : ℝ) / 2 ≤ s := le_trans hp hps
  have hq : ∀ t : ℝ, (0 : ℝ) ≤ 2 * t ^ 2 - 2 * t + 1 := fun t ↦ by
    nlinarith [sq_nonneg (2 * t - 1)]
  have hφs : 0 ≤ s * ((2 * s - 1) * (2 * s ^ 2 - 2 * s + 1)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (hq s))
  rw [phi_eq p, phi_eq s]
  have hmono := scalar_mono hp hps
  have hkey : (p * (p * ((2 * p - 1) * (2 * p ^ 2 - 2 * p + 1)))) ^ 2 ≤
      (K * (s * ((2 * s - 1) * (2 * s ^ 2 - 2 * s + 1)))) ^ 2 := by
    have hpos : (0 : ℝ) < s ^ 3 * p ^ 3 := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    have hA : p ^ 7 * (s ^ 3 * ((2 * p - 1) * (2 * p ^ 2 - 2 * p + 1)) ^ 2) ≤
        (K ^ 2 * s ^ 5) *
          (p ^ 3 * ((2 * s - 1) * (2 * s ^ 2 - 2 * s + 1)) ^ 2) :=
      mul_le_mul hKs hmono (by positivity) (by positivity)
    nlinarith [hA]
  exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num)
    (mul_nonneg hK0.le hφs) hkey

/-! ### The graph and its peeling -/

/-- The five-cycle `0–1–2–3–4–0` with a pendant leaf `5` on the vertex `0`. -/
def c5plus : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4), (0, 5)]

instance : DecidableRel c5plus.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_c5plus :
    c5plus.edgeFinset =
      {s(0, 1), s(0, 4), s(1, 2), s(2, 3), s(3, 4), s(0, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_c5plus (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight c5plus W x =
      W (x 0) (x 1) * W (x 0) (x 4) * W (x 1) (x 2) * W (x 2) (x 3) *
        W (x 3) (x 4) * W (x 0) (x 5) := by
  rw [graphWeight, edgeFinset_c5plus]
  simp
  ring

section Peel

variable (W : Graphon Ω μ)

/-- The five-cycle weight of an assignment, as a function of five coordinates. -/
private lemma cycle_of (y : Fin 5 → Ω) :
    graphWeight c5 W y =
      W (y 0) (y 1) * W (y 0) (y 4) * W (y 1) (y 2) * W (y 2) (y 3) *
        W (y 3) (y 4) := graphWeight_c5 W y

private lemma meas_cycle : Measurable fun y : Fin 5 → Ω ↦
    (W (y 0) (y 1) * W (y 0) (y 4) * W (y 1) (y 2) * W (y 2) (y 3) *
      W (y 3) (y 4)) * degree W (y 0) :=
  ((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 4)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 2 3)).mul
    (measurable_coord_pair W 3 4) |>.mul
    ((measurable_degree W).comp (measurable_pi_apply 0))

private lemma bdd_cycle (y : Fin 5 → Ω) :
    |(W (y 0) (y 1) * W (y 0) (y 4) * W (y 1) (y 2) * W (y 2) (y 3) *
      W (y 3) (y 4)) * degree W (y 0)| ≤ 1 := by
  have h0 : 0 ≤ (W (y 0) (y 1) * W (y 0) (y 4) * W (y 1) (y 2) * W (y 2) (y 3) *
      W (y 3) (y 4)) * degree W (y 0) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_)
      (degree_nonneg W _) <;> exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  refine mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (degree_nonneg W _) (degree_le_one W _)

private lemma meas_c5plus : Measurable fun y : Fin 6 → Ω ↦
    W (y 0) (y 1) * W (y 0) (y 4) * W (y 1) (y 2) * W (y 2) (y 3) *
      W (y 3) (y 4) * W (y 0) (y 5) :=
  (((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 4)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 2 3)).mul
    (measurable_coord_pair W 3 4)).mul (measurable_coord_pair W 0 5)

omit [IsProbabilityMeasure μ] in
private lemma bdd_c5plus (x : Fin 6 → Ω) :
    |W (x 0) (x 1) * W (x 0) (x 4) * W (x 1) (x 2) * W (x 2) (x 3) *
      W (x 3) (x 4) * W (x 0) (x 5)| ≤ 1 := by
  have h0 : 0 ≤ W (x 0) (x 1) * W (x 0) (x 4) * W (x 1) (x 2) * W (x 2) (x 3) *
      W (x 3) (x 4) * W (x 0) (x 5) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _)

/-- **The density of Atlas 104 is the cycle weight against the root degree.** -/
theorem homDensity_c5plus :
    homDensity c5plus W =
      ∫ y, graphWeight c5 W y * degree W (y 0)
        ∂assignmentMeasure (Fin 5) μ := by
  have hright : (∫ y, graphWeight c5 W y * degree W (y 0)
      ∂assignmentMeasure (Fin 5) μ) =
      ∫ a0, ∫ a1, ∫ a2, ∫ a3, ∫ a4,
        (W a0 a1 * W a0 a4 * W a1 a2 * W a2 a3 * W a3 a4) * degree W a0
        ∂μ ∂μ ∂μ ∂μ ∂μ := by
    rw [integral_congr_ae (ae_of_all _ fun y ↦ by rw [cycle_of W y]),
      integral_assignment_fin_five
        (g := fun a0 a1 a2 a3 a4 ↦
          (W a0 a1 * W a0 a4 * W a1 a2 * W a2 a3 * W a3 a4) * degree W a0)
        (meas_cycle W) (bdd_cycle W)]
  rw [hright, homDensity,
    integral_congr_ae (ae_of_all _ (graphWeight_c5plus W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ W a0 a1 * W a0 a4 * W a1 a2 * W a2 a3 *
        W a3 a4 * W a0 a5)
      (meas_c5plus W) (bdd_c5plus W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
  simp only []
  have hre : ∀ a5 : Ω,
      W a0 a1 * W a0 a4 * W a1 a2 * W a2 a3 * W a3 a4 * W a0 a5 =
        (W a0 a1 * W a0 a4 * W a1 a2 * W a2 a3 * W a3 a4) * W a0 a5 :=
    fun a5 ↦ by ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
  rfl

end Peel

/-! ### Cyclic symmetrisation -/

lemma c5_rot_adj (i a b : Fin 5) : c5.Adj (a + i) (b + i) ↔ c5.Adj a b := by
  revert i a b
  decide

/-- Rotating the five coordinates is an automorphism of `C₅`. -/
def rotIso (i : Fin 5) : c5 ≃g c5 where
  toEquiv := Equiv.addRight i
  map_rel_iff' := by intro a b; exact c5_rot_adj i a b

/-- **The degree may sit at any cycle coordinate.** -/
theorem integral_cycle_degree (W : Graphon Ω μ) (i : Fin 5) :
    (∫ y, graphWeight c5 W y * degree W (y 0) ∂assignmentMeasure (Fin 5) μ) =
      ∫ y, graphWeight c5 W y * degree W (y i)
        ∂assignmentMeasure (Fin 5) μ := by
  rw [integral_assignment_perm (Equiv.addRight i)
    (fun y ↦ graphWeight c5 W y * degree W (y 0))]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  have hw : graphWeight c5 W (fun v ↦ y ((Equiv.addRight i) v)) =
      graphWeight c5 W y := graphWeight_iso W (rotIso i) y
  rw [hw]
  congr 2
  show y ((0 : Fin 5) + i) = y i
  rw [zero_add]

/-! ### The arithmetic–geometric mean step -/

/-- `∏ d(yᵢ)^{1/5} ≤ (1/5)∑ d(yᵢ)`. -/
theorem prod_rootDegree_le (W : Graphon Ω μ) (y : Fin 5 → Ω) :
    (∏ i, rootDegree W 5 (y i)) ≤
      ∑ i, ((5 : ℝ))⁻¹ * degree W (y i) := by
  have h := Real.geom_mean_le_arith_mean_weighted (univ : Finset (Fin 5))
    (fun _ ↦ ((5 : ℝ))⁻¹) (fun i ↦ degree W (y i))
    (fun i _ ↦ by norm_num)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num)
    (fun i _ ↦ degree_nonneg W (y i))
  refine le_trans (le_of_eq ?_) h
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [rootDegree]
  norm_num

/-! ### The chain -/

section Chain

variable (W : Graphon Ω μ)

private lemma meas_cycle_deg (i : Fin 5) : Measurable fun y : Fin 5 → Ω ↦
    graphWeight c5 W y * degree W (y i) :=
  (measurable_graphWeight c5 W).mul
    ((measurable_degree W).comp (measurable_pi_apply i))

private lemma bdd_cycle_deg (i : Fin 5) (y : Fin 5 → Ω) :
    |graphWeight c5 W y * degree W (y i)| ≤ 1 := by
  have h0 : 0 ≤ graphWeight c5 W y * degree W (y i) :=
    mul_nonneg (graphWeight_nonneg c5 W y) (degree_nonneg W _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (graphWeight_le_one c5 W y) (degree_nonneg W _)
    (degree_le_one W _)

private lemma int_cycle_deg (i : Fin 5) : Integrable
    (fun y : Fin 5 → Ω ↦ graphWeight c5 W y * degree W (y i))
    (assignmentMeasure (Fin 5) μ) :=
  integrable_of_bounded (meas_cycle_deg W i) (bdd_cycle_deg W i)

/-- **The arithmetic–geometric mean step**, after cyclic symmetrisation. -/
theorem integral_prod_rootDegree_le :
    (∫ y, (∏ i, rootDegree W 5 (y i)) * graphWeight c5 W y
        ∂assignmentMeasure (Fin 5) μ) ≤
      ∫ y, graphWeight c5 W y * degree W (y 0)
        ∂assignmentMeasure (Fin 5) μ := by
  set ν := assignmentMeasure (Fin 5) μ with hν
  have hleft : Integrable
      (fun y : Fin 5 → Ω ↦ (∏ i, rootDegree W 5 (y i)) * graphWeight c5 W y) ν := by
    refine integrable_of_bounded (C := 1) ?_ ?_
    · exact (Finset.measurable_prod _ fun i _ ↦
        (measurable_rootDegree W).comp (measurable_pi_apply i)).mul
        (measurable_graphWeight c5 W)
    · intro y
      have hp0 : 0 ≤ ∏ i, rootDegree W 5 (y i) :=
        Finset.prod_nonneg fun i _ ↦ rootDegree_nonneg W _
      have hp1 : (∏ i, rootDegree W 5 (y i)) ≤ 1 :=
        Finset.prod_le_one (fun i _ ↦ rootDegree_nonneg W _)
          (fun i _ ↦ rootDegree_le_one W _)
      rw [abs_of_nonneg (mul_nonneg hp0 (graphWeight_nonneg c5 W y))]
      exact mul_le_one₀ hp1 (graphWeight_nonneg c5 W y) (graphWeight_le_one c5 W y)
  have hright : Integrable
      (fun y : Fin 5 → Ω ↦ ∑ i, ((5 : ℝ))⁻¹ * (graphWeight c5 W y * degree W (y i)))
      ν :=
    integrable_finsetSum _ fun i _ ↦ ((int_cycle_deg W i).const_mul _)
  have hstep : (∫ y, (∏ i, rootDegree W 5 (y i)) * graphWeight c5 W y ∂ν) ≤
      ∫ y, ∑ i, ((5 : ℝ))⁻¹ * (graphWeight c5 W y * degree W (y i)) ∂ν := by
    refine integral_mono hleft hright fun y ↦ ?_
    have hpt := prod_rootDegree_le W y
    have hexp : ∑ i, ((5 : ℝ))⁻¹ * (graphWeight c5 W y * degree W (y i)) =
        graphWeight c5 W y * ∑ i, ((5 : ℝ))⁻¹ * degree W (y i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_left hpt (graphWeight_nonneg c5 W y) |>.trans_eq
      (by ring) |>.trans_eq' (by ring)
  refine le_trans hstep (le_of_eq ?_)
  rw [integral_finsetSum _ fun i _ ↦ ((int_cycle_deg W i).const_mul _)]
  have hterm : ∀ i : Fin 5,
      (∫ y, ((5 : ℝ))⁻¹ * (graphWeight c5 W y * degree W (y i)) ∂ν) =
        ((5 : ℝ))⁻¹ *
          ∫ y, graphWeight c5 W y * degree W (y 0) ∂ν := by
    intro i
    rw [integral_const_mul, ← integral_cycle_degree W i]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  ring

end Chain

/-! ### The bound -/

/-- **Atlas 104 dominates its target.** -/
theorem c5plus_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 6 - cliqueDensity 2 W ^ 2 *
        (1 - cliqueDensity 2 W) ^ 4 ≤ homDensity c5plus W := by
  set p := cliqueDensity 2 W with hpdef
  have hp0 : (0 : ℝ) < p := by linarith
  have hM : 0 < rootMean W 5 := rootMean_pos W (by norm_num) hp0
  haveI : IsProbabilityMeasure (rootMeasure W 5) :=
    isProbabilityMeasure_rootMeasure W hM
  set s := cliqueDensity 2 (rootGraphon W 5) with hsdef
  set K := rootMean W 5 ^ 5 with hKdef
  have hK0 : 0 < K := by positivity
  have hKp : K ≤ p := pow_rootMean_le W (by norm_num)
  have hs0 : 0 ≤ s := cliqueDensity_nonneg 2 _
  -- the fractional Hölder bound, rewritten through `N = M²s`
  have hKs : p ^ 7 ≤ K ^ 2 * s ^ 5 := by
    have h := pow_seven_le_pow_rootEdge W
    rw [rootEdge_eq W hM] at h
    calc p ^ 7 ≤ (rootMean W 5 ^ 2 * s) ^ 5 := h
      _ = K ^ 2 * s ^ 5 := by rw [hKdef]; ring
  -- the analytic `C₅` theorem on the biased space
  have hcycle : s ^ 5 - s * (1 - s) ^ 4 ≤ homDensity c5 (rootGraphon W 5) :=
    c5_homDensity_bound (rootGraphon W 5)
  -- assemble
  have hbias := integral_rootDegree_prod 5 5 c5 W hM
  have hmid : K * (s ^ 5 - s * (1 - s) ^ 4) ≤
      ∫ y, (∏ i, rootDegree W 5 (y i)) * graphWeight c5 W y
        ∂assignmentMeasure (Fin 5) μ := by
    rw [hbias, hKdef]
    exact mul_le_mul_of_nonneg_left hcycle (by positivity)
  have hchain := le_trans hmid (integral_prod_rootDegree_le W)
  have hscalar := transfer (p := p) (s := s) (K := K) hp hs0 hK0 hKp hKs
  rw [homDensity_c5plus W]
  have hfinal : p * (p ^ 5 - p * (1 - p) ^ 4) =
      p ^ 6 - p ^ 2 * (1 - p) ^ 4 := by ring
  linarith [hscalar, hchain, hfinal]

/-! ### Chromatic data and the catalogue proposition -/

/-- The attachment of the leaf, read on `Fin 6`. -/
def leafEquiv : Option (Fin 5) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some i => ![0, 1, 2, 3, 4] i
  invFun j := ![some 0, some 1, some 2, some 3, some 4, none] j
  left_inv := by decide
  right_inv := by decide

/-- A singleton is a clique. -/
lemma isClique_c5_singleton :
    c5.IsClique ((({0} : Finset (Fin 5)) : Finset (Fin 5)) : Set (Fin 5)) := by
  intro u hu v hv huv
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  exact absurd (hu.trans hv.symm) huv

def iso104 : attachVertex c5 {0} ≃g c5plus where
  toEquiv := leafEquiv
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom104 :
    IsChromaticPolynomial c5plus (((X : ℝ[X]) - 1) ^ 6 - ((X : ℝ[X]) - 1) ^ 2) := by
  have h := isChromaticPolynomial_of_attachIso (H' := c5plus) iso104
    isClique_c5_singleton isChromaticPolynomial_c5
  rw [show (({0} : Finset (Fin 5)).card) = 1 from by decide] at h
  have hpoly : ((X : ℝ[X]) - C ((1 : ℕ) : ℝ)) * (((X : ℝ[X]) - 1) ^ 5 - (X - 1)) =
      ((X : ℝ[X]) - 1) ^ 6 - ((X : ℝ[X]) - 1) ^ 2 := by
    simp only [Nat.cast_one, map_one]
    ring
  rw [← hpoly]
  exact h

theorem count104 (k : ℕ) :
    properAssignmentCount c5plus k = (k - 1) * properAssignmentCount c5 k := by
  rw [properAssignmentCount_of_attachIso (H' := c5plus) iso104
      isClique_c5_singleton k, Finset.card_singleton]

theorem num104 : IsChromaticNumber c5plus 3 where
  positive := by
    rw [count104, properAssignmentCount_c5 (by norm_num)]
    norm_num
  zero_below k hk := by
    rw [count104]
    interval_cases k
    · rw [properAssignmentCount_c5_small (by norm_num)]
    · rw [properAssignmentCount_c5_small (by norm_num)]
    · rw [properAssignmentCount_c5 (by norm_num)]
      norm_num

/-- **Atlas 104 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_104 : Taeyoung.SatisfiesLowerBound c5plus := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ((X : ℝ[X]) - 1) ^ 6 - ((X : ℝ[X]) - 1) ^ 2 :=
    IsChromaticPolynomial.unique (H := c5plus) hP chrom104
  have hreq : r = 3 := IsChromaticNumber.unique (H := c5plus) hr num104
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hbound := c5plus_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hbound
    norm_num at hbound
    exact hbound
  · rw [chromaticTarget_of_ne_one _ hone]
    have hq : (1 : ℝ) - cliqueDensity 2 W ≠ 0 := fun h ↦ hone (by linarith)
    have hcalc :
        (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 6) *
            Polynomial.eval (1 / (1 - cliqueDensity 2 W))
              (((X : ℝ[X]) - 1) ^ 6 - ((X : ℝ[X]) - 1) ^ 2) =
          cliqueDensity 2 W ^ 6 -
            cliqueDensity 2 W ^ 2 * (1 - cliqueDensity 2 W) ^ 4 := by
      simp only [Fintype.card_fin, eval_sub, eval_pow, eval_X, eval_one]
      field_simp
      ring
    rw [hcalc]
    exact hbound

end Taeyoung.Methods.OddLeaf
