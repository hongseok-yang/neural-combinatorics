import Taeyoung.Methods.Atlas148.Linear

/-!
# Atlas 148: the two-dimensional projection

For a fixed spine image `x`, the note's density identity presents the Atlas 148
density as a squared norm,

```
t = ∫ ‖T_W F_x‖² dμ(x),      F_x(a) = K(x,a) = W(x,a)S(x,a),
```

and projects `T_W F_x` onto the two orthogonal functions `1` and
`W(x,·) - d(x)`, whose squared norms are `1` and `v(x) = ∫W(x,·)² - d(x)²`.
Bessel's inequality then gives

```
‖T_W F_x‖² ≥ g(x)² + (h(x) - d(x)g(x))²/v(x),
```

with the quotient set to zero where `v(x) = 0`.

Two changes make this painless in Lean, and both come from keeping the
multiplier free instead of optimizing it fibrewise.

* **No division.**  Bessel is used in its *linearized* form: for every real
  `λ`, `‖T_W F_x‖² ≥ g(x)² + 2λ(h(x) - d(x)g(x)) - λ²v(x)`.  Optimizing over
  `λ` would give the quotient back, but the quotient is never needed — and the
  degenerate fibres `v(x) = 0` need no separate treatment.
* **No Hilbert space.**  In that form Bessel is one line: put
  `w = T_W F_x - λ(W(x,·) - d(x))`.  Because the centred function has mean
  zero, `∫w = g(x)`, and Jensen `(∫w)² ≤ ∫w²` is the whole content.

The same free `λ` collapses the note's final two-dimensional Cauchy--Schwarz.
Taking `λ = -cq` and feeding in the linear estimate `p²G - qΔ ≥ pcf` turns the
target into

```
t - pc²f ≥ (G - cp²)² ≥ 0,
```

using `f = p³ + q³`.  So no `(G₀, Δ₀)` vector, no weighted inner product, and
no division by `V` anywhere: `V ≤ pq` enters only as a coefficient bound.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Jensen and linearized Bessel on a probability space -/

/-- Jensen for squares: `(∫u)² ≤ ∫u²`. -/
lemma sq_integral_le (u : Ω → ℝ) (hu : Integrable u μ)
    (hu2 : Integrable (fun z ↦ u z ^ 2) μ) :
    (∫ z, u z ∂μ) ^ 2 ≤ ∫ z, u z ^ 2 ∂μ := by
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (A := fun _ : Ω ↦ (1:ℝ)) (η := u) (integrable_const 1)
    (hu.congr (ae_of_all _ fun z ↦ (one_mul (u z)).symm))
    (hu2.congr (ae_of_all _ fun z ↦ (one_mul (u z ^ 2)).symm))
    fun _ ↦ zero_le_one
  simpa using hcs

/-- **Linearized two-term Bessel.**  If `e` has mean zero then for every `λ`

```
(∫u)² + 2λ∫u·e - λ²∫e² ≤ ∫u².
```

Optimizing over `λ` recovers the usual quotient form; leaving `λ` free avoids
both the division and the degenerate case `∫e² = 0`. -/
lemma two_term_bessel {u e : Ω → ℝ} (hu : Integrable u μ)
    (hu2 : Integrable (fun z ↦ u z ^ 2) μ) (he : Integrable e μ)
    (he2 : Integrable (fun z ↦ e z ^ 2) μ) (hue : Integrable (fun z ↦ u z * e z) μ)
    (hmean : (∫ z, e z ∂μ) = 0) (lam : ℝ) :
    (∫ z, u z ∂μ) ^ 2 + 2 * lam * (∫ z, u z * e z ∂μ)
        - lam ^ 2 * (∫ z, e z ^ 2 ∂μ)
      ≤ ∫ z, u z ^ 2 ∂μ := by
  have hle : Integrable (fun z ↦ lam * e z) μ := he.const_mul lam
  have hw : Integrable (fun z ↦ u z - lam * e z) μ := hu.sub hle
  -- the expanded square
  have hpt : ∀ z, (u z - lam * e z) ^ 2
      = u z ^ 2 - 2 * lam * (u z * e z) + lam ^ 2 * e z ^ 2 := by
    intro z; ring
  have hA : Integrable (fun z ↦ 2 * lam * (u z * e z)) μ := hue.const_mul _
  have hB : Integrable (fun z ↦ lam ^ 2 * e z ^ 2) μ := he2.const_mul _
  have hAB : Integrable (fun z ↦ u z ^ 2 - 2 * lam * (u z * e z)) μ :=
    (hu2.sub hA).congr (ae_of_all _ fun z ↦ rfl)
  have hw2 : Integrable (fun z ↦ (u z - lam * e z) ^ 2) μ :=
    ((hAB.add hB).congr (ae_of_all _ fun z ↦ rfl)).congr
      (ae_of_all _ fun z ↦ (hpt z).symm)
  have hsq : (∫ z, (u z - lam * e z) ^ 2 ∂μ)
      = (∫ z, u z ^ 2 ∂μ) - 2 * lam * (∫ z, u z * e z ∂μ)
        + lam ^ 2 * ∫ z, e z ^ 2 ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add hAB hB,
      integral_sub hu2 hA, integral_const_mul, integral_const_mul]
  have hmeanw : (∫ z, (u z - lam * e z) ∂μ) = ∫ z, u z ∂μ := by
    rw [integral_sub hu hle, integral_const_mul, hmean]
    ring
  have hjen := sq_integral_le (fun z ↦ u z - lam * e z) hw hw2
  rw [hmeanw, hsq] at hjen
  linarith

/-! ### The fibre data -/

/-- `K(x,a) = W(x,a)S(x,a)`. -/
noncomputable def edgeK (W : Graphon Ω μ) (x a : Ω) : ℝ := W x a * pageOp W 0 x a

lemma edgeK_nonneg (W : Graphon Ω μ) (x a : Ω) : 0 ≤ edgeK W x a :=
  mul_nonneg (W.nonneg _ _) (pageOp_nonneg W le_rfl _ _)

lemma edgeK_le_one (W : Graphon Ω μ) (x a : Ω) : edgeK W x a ≤ 1 :=
  mul_le_one₀ (W.le_one _ _) (pageOp_nonneg W le_rfl _ _) (pageOp_le_one W le_rfl _ _)

lemma measurable_edgeK (W : Graphon Ω μ) :
    Measurable fun q : Ω × Ω ↦ edgeK W q.1 q.2 :=
  W.measurable.mul (measurable_pageOp W le_rfl)

lemma integrable_edgeK_row (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun a ↦ edgeK W x a) μ :=
  integrable_of_bdd (measurable_row (measurable_edgeK W) x) (C := 1) fun a ↦ by
    rw [abs_of_nonneg (edgeK_nonneg W x a)]; exact edgeK_le_one W x a

/-- `(T_W F_x)(z) = ∫ W(z,a)K(x,a) dμ(a)`. -/
noncomputable def fibOp (W : Graphon Ω μ) (x z : Ω) : ℝ :=
  ∫ a, W z a * edgeK W x a ∂μ

lemma fibOp_integrand_nonneg (W : Graphon Ω μ) (x z a : Ω) :
    0 ≤ W z a * edgeK W x a :=
  mul_nonneg (W.nonneg _ _) (edgeK_nonneg W x a)

lemma fibOp_integrand_le_one (W : Graphon Ω μ) (x z a : Ω) :
    W z a * edgeK W x a ≤ 1 :=
  mul_le_one₀ (W.le_one _ _) (edgeK_nonneg W x a) (edgeK_le_one W x a)

lemma integrable_fibOp_integrand (W : Graphon Ω μ) (x z : Ω) :
    Integrable (fun a ↦ W z a * edgeK W x a) μ :=
  integrable_of_bdd ((measurable_row W.measurable z).mul
    (measurable_row (measurable_edgeK W) x)) (C := 1) fun a ↦ by
      rw [abs_of_nonneg (fibOp_integrand_nonneg W x z a)]
      exact fibOp_integrand_le_one W x z a

lemma fibOp_nonneg (W : Graphon Ω μ) (x z : Ω) : 0 ≤ fibOp W x z :=
  integral_nonneg fun a ↦ fibOp_integrand_nonneg W x z a

lemma fibOp_le_one (W : Graphon Ω μ) (x z : Ω) : fibOp W x z ≤ 1 := by
  refine le_of_abs_le (abs_integral_le_of_bdd ((measurable_row W.measurable z).mul
    (measurable_row (measurable_edgeK W) x)) fun a ↦ ?_)
  rw [abs_of_nonneg (fibOp_integrand_nonneg W x z a)]
  exact fibOp_integrand_le_one W x z a

lemma measurable_fibOp (W : Graphon Ω μ) :
    Measurable fun q : Ω × Ω ↦ fibOp W q.1 q.2 := by
  have hg : StronglyMeasurable fun p : (Ω × Ω) × Ω ↦
      W p.1.2 p.2 * edgeK W p.1.1 p.2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    exact (W.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
      ((measurable_edgeK W).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact (hg.integral_prod_right' (ν := μ)).measurable

lemma integrable_fibOp_row (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun z ↦ fibOp W x z) μ :=
  integrable_of_bdd (measurable_row (measurable_fibOp W) x) (C := 1) fun z ↦ by
    rw [abs_of_nonneg (fibOp_nonneg W x z)]; exact fibOp_le_one W x z

/-- `g(x) = ∫ d(a)K(x,a)`. -/
noncomputable def gFib (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ a, degree W a * edgeK W x a ∂μ

/-- `h(x) = ∫ K(x,a)S(x,a)`. -/
noncomputable def hFib (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ a, edgeK W x a * pageOp W 0 x a ∂μ

/-- `v(x) = ∫ W(x,·)² - d(x)²`, the squared norm of the centred row. -/
noncomputable def vFib (W : Graphon Ω μ) (x : Ω) : ℝ :=
  (∫ z, W x z ^ 2 ∂μ) - degree W x ^ 2

/-! ### The three fibre identities -/

/-- `∫ T_W F_x = g(x)`. -/
theorem integral_fibOp (W : Graphon Ω μ) (x : Ω) :
    (∫ z, fibOp W x z ∂μ) = gFib W x := by
  have hi : Integrable (Function.uncurry fun z a ↦ W z a * edgeK W x a) (μ.prod μ) :=
    integrable_prod_of_bdd (W.measurable.mul
      ((measurable_edgeK W).comp (measurable_const.prodMk measurable_snd)))
      (C := 1) fun q ↦ by
        show |W q.1 q.2 * edgeK W x q.2| ≤ 1
        rw [abs_of_nonneg (fibOp_integrand_nonneg W x q.1 q.2)]
        exact fibOp_integrand_le_one W x q.1 q.2
  simp only [fibOp, gFib]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  show (∫ z, W z a * edgeK W x a ∂μ) = degree W a * edgeK W x a
  rw [integral_mul_const]
  congr 1
  rw [← integral_edge_right W a]
  exact integral_congr_ae (ae_of_all _ fun z ↦ W.symm z a)

/-- `∫ (T_W F_x)·W(x,·) = h(x)`. -/
theorem integral_fibOp_mul_row (W : Graphon Ω μ) (x : Ω) :
    (∫ z, fibOp W x z * W x z ∂μ) = hFib W x := by
  have hi : Integrable
      (Function.uncurry fun z a ↦ W x z * (W z a * edgeK W x a)) (μ.prod μ) := by
    refine integrable_prod_of_bdd ((W.measurable.comp
      (measurable_const.prodMk measurable_fst)).mul (W.measurable.mul
        ((measurable_edgeK W).comp (measurable_const.prodMk measurable_snd))))
      (C := 1) fun q ↦ ?_
    have h0 : 0 ≤ W x q.1 * (W q.1 q.2 * edgeK W x q.2) :=
      mul_nonneg (W.nonneg _ _) (fibOp_integrand_nonneg W x q.1 q.2)
    show |W x q.1 * (W q.1 q.2 * edgeK W x q.2)| ≤ 1
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _) (fibOp_integrand_nonneg W x q.1 q.2)
      (fibOp_integrand_le_one W x q.1 q.2)
  have hstep : (∫ z, fibOp W x z * W x z ∂μ)
      = ∫ z, ∫ a, W x z * (W z a * edgeK W x a) ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    show fibOp W x z * W x z = ∫ a, W x z * (W z a * edgeK W x a) ∂μ
    rw [fibOp, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
    ring
  rw [hstep, integral_integral_swap hi, hFib]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  show (∫ z, W x z * (W z a * edgeK W x a) ∂μ) = edgeK W x a * pageOp W 0 x a
  have hre : ∀ z, W x z * (W z a * edgeK W x a)
      = edgeK W x a * (W x z * W a z) := by
    intro z
    rw [W.symm z a]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp_zero_eq]

/-- The centred row has mean zero, and squared norm `v(x)`. -/
theorem integral_row_centered (W : Graphon Ω μ) (x : Ω) :
    (∫ z, (W x z - degree W x) ∂μ) = 0 := by
  have hrow : Integrable (fun z ↦ W x z) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (W.nonneg x z)]; exact W.le_one x z
  rw [integral_sub hrow (integrable_const _), integral_edge_right, integral_const]
  simp

theorem integral_row_centered_sq (W : Graphon Ω μ) (x : Ω) :
    (∫ z, (W x z - degree W x) ^ 2 ∂μ) = vFib W x := by
  have hrow : Integrable (fun z ↦ W x z) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (W.nonneg x z)]; exact W.le_one x z
  have hrow2 : Integrable (fun z ↦ W x z ^ 2) μ :=
    integrable_of_bdd ((measurable_row W.measurable x).pow_const 2) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (W.nonneg x z) (W.le_one x z)
  have hpt : ∀ z, (W x z - degree W x) ^ 2
      = W x z ^ 2 - 2 * degree W x * W x z + degree W x ^ 2 := by
    intro z; ring
  have hA : Integrable (fun z ↦ 2 * degree W x * W x z) μ := hrow.const_mul _
  have hAB : Integrable (fun z ↦ W x z ^ 2 - 2 * degree W x * W x z) μ :=
    (hrow2.sub hA).congr (ae_of_all _ fun z ↦ rfl)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add hAB (integrable_const _),
    integral_sub hrow2 hA, integral_const_mul, integral_edge_right, integral_const,
    vFib]
  simp
  ring

/-! ### The fibrewise bound -/

/-- **Linearized Bessel on one fibre.** -/
theorem fibOp_sq_lower (W : Graphon Ω μ) (x : Ω) (lam : ℝ) :
    gFib W x ^ 2 + 2 * lam * (hFib W x - degree W x * gFib W x)
        - lam ^ 2 * vFib W x
      ≤ ∫ z, fibOp W x z ^ 2 ∂μ := by
  set u := fun z ↦ fibOp W x z with hu_def
  set e := fun z ↦ W x z - degree W x with he_def
  have hmu : Measurable u := measurable_row (measurable_fibOp W) x
  have hme : Measurable e := (measurable_row W.measurable x).sub measurable_const
  have hu : Integrable u μ := integrable_fibOp_row W x
  have hu2 : Integrable (fun z ↦ u z ^ 2) μ :=
    integrable_of_bdd (hmu.pow_const 2) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (fibOp_nonneg W x z) (fibOp_le_one W x z)
  have hebd : ∀ z, |e z| ≤ 1 := fun z ↦ by
    rw [abs_le]
    constructor
    · have := W.nonneg x z; have := degree_le_one W x; simp only [he_def]; linarith
    · have := W.le_one x z; have := degree_nonneg W x; simp only [he_def]; linarith
  have he : Integrable e μ := integrable_of_bdd hme hebd
  have he2 : Integrable (fun z ↦ e z ^ 2) μ :=
    integrable_of_bdd (hme.pow_const 2) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc e z ^ 2 = |e z| ^ 2 := (sq_abs _).symm
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hebd z) 2
        _ = 1 := one_pow 2
  have hue : Integrable (fun z ↦ u z * e z) μ :=
    integrable_of_bdd (hmu.mul hme) (C := 1) fun z ↦ by
      rw [abs_mul, abs_of_nonneg (fibOp_nonneg W x z)]
      calc u z * |e z| ≤ 1 * 1 :=
            mul_le_mul (fibOp_le_one W x z) (hebd z) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have hmean : (∫ z, e z ∂μ) = 0 := integral_row_centered W x
  have hbes := two_term_bessel hu hu2 he he2 hue hmean lam
  -- identify the three integrals
  have h1 : (∫ z, u z ∂μ) = gFib W x := integral_fibOp W x
  have h2 : (∫ z, u z * e z ∂μ) = hFib W x - degree W x * gFib W x := by
    have hpt : ∀ z, u z * e z = u z * W x z - degree W x * u z := by
      intro z; simp only [he_def]; ring
    have hA : Integrable (fun z ↦ u z * W x z) μ :=
      integrable_of_bdd (hmu.mul (measurable_row W.measurable x)) (C := 1) fun z ↦ by
        rw [abs_of_nonneg (mul_nonneg (fibOp_nonneg W x z) (W.nonneg x z))]
        exact mul_le_one₀ (fibOp_le_one W x z) (W.nonneg x z) (W.le_one x z)
    have hB : Integrable (fun z ↦ degree W x * u z) μ := hu.const_mul _
    rw [integral_congr_ae (ae_of_all _ hpt), integral_sub hA hB, integral_const_mul,
      integral_fibOp_mul_row W x, h1]
  have h3 : (∫ z, e z ^ 2 ∂μ) = vFib W x := integral_row_centered_sq W x
  rw [h1, h2, h3] at hbes
  exact hbes

end Taeyoung.Methods.Atlas148
