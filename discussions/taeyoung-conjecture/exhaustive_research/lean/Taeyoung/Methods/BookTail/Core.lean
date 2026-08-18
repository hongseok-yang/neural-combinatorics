import Taeyoung.Methods.PathSidorenko
import Taeyoung.Methods.Link.PageOp
import Taeyoung.Methods.RootedTriangleTree.Paw

/-!
# Triangle books with a two-edge tail: the analytic core

`notes/triangle_book_two_edge_tail.tex`.  Let `R_m` be a book of `m` triangles
on a spine `ab`, with one two-edge tail `a–u–v`.  Peeling the pages and the tail
turns its density into

```
t(R_m,W) = ∫∫ W(x,y)·A(x)·S(x,y)^m,      A = T_W d,   S(x,y) = ∫W(x,z)W(y,z)dz,
```

and the target is `Φ = p³(2p-1)^m`.  Writing

```
B = ∫ A·d = t(P₄,W),        F = ∫ A·τ = t(R₁,W),
```

the note's two inputs are `F ≥ (2p-1)B` and `F ≥ p³(2p-1)`; Jensen for
`s ↦ s^m` under `dν = W(x,y)A(x)dμ²` then gives every `m` at once.

Both inputs start from the pointwise Goodman bound `τ ≥ 2A - p`, which
`Link.rootedTriangle_ge` already has, and reduce to scalar facts about

```
M = ∫A = ∫d²,        N = ∫A²,        B = ∫A·d.
```

**The route here differs from the note's.**  The note proves `F ≥ (2p-1)B` for
every `p ≥ 1/6`, by an exact operator square `E = 2‖h + ((2p+1)/4)g‖² +
((2p+1)(6p-1)/8)‖g‖²` after `d = p·1 + g`, `h = Tg`.  On the interval the
catalogue actually requires, `p ≥ 1/2`, plain Cauchy–Schwarz suffices and is far
cheaper: `B² ≤ N·M`, `N ≥ M²` and `M ≥ p²` give

```
(2N - pM)² - (2p-1)²·N·M = (4N - M)(N - p²M) ≥ 0,
```

both factors being nonnegative because `M ≥ p² ≥ 1/4`.  So the operator
identity is not formalized; what is formalized is the same inequality on
`[1/2,1]`, which is all `SatisfiesLowerBound` ever asks for at `χ = 3`.
-/

open MeasureTheory

namespace Taeyoung.Methods.BookTail

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.RootedTriangleTree

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Cauchy–Schwarz for two integrals

`Methods/PureChordal/WeightedCauchySchwarz.lean` has the weighted form
`(∫Aη)² ≤ (∫A)(∫Aη²)`, which is not the shape needed here.  The unweighted
form is the same one-line argument: integrate `(f - (∫fg/∫g²)·g)²`. -/

theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f g : α → ℝ} (hf2 : Integrable (fun x ↦ f x ^ 2) ν)
    (hg2 : Integrable (fun x ↦ g x ^ 2) ν)
    (hfg : Integrable (fun x ↦ f x * g x) ν) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν := by
  set a := ∫ x, f x ^ 2 ∂ν with hadef
  set b := ∫ x, f x * g x ∂ν with hbdef
  set c := ∫ x, g x ^ 2 ∂ν with hcdef
  have hc0 : 0 ≤ c := integral_nonneg fun x ↦ sq_nonneg _
  rcases eq_or_lt_of_le hc0 with hc | hc
  · -- `∫g² = 0` forces `g = 0` a.e., hence `∫fg = 0`
    have hgae : (fun x ↦ g x ^ 2) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg _) hg2).mp hc.symm
    have hb : b = 0 := by
      rw [hbdef]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hgae] with x hx
      have : g x = 0 := by
        have := hx
        simp only [Pi.zero_apply, pow_eq_zero_iff (n := 2) (by norm_num)] at this
        exact this
      simp [this]
    rw [hb, ← hc]
    simp
  · -- otherwise complete the square at `λ = b/c`
    set lam := b / c with hlamdef
    have hquad : 0 ≤ ∫ x, (f x - lam * g x) ^ 2 ∂ν :=
      integral_nonneg fun x ↦ sq_nonneg _
    have hexp : (∫ x, (f x - lam * g x) ^ 2 ∂ν) = a - 2 * lam * b + lam ^ 2 * c := by
      have hpt : ∀ x, (f x - lam * g x) ^ 2 =
          f x ^ 2 - (2 * lam) * (f x * g x) + lam ^ 2 * g x ^ 2 := by
        intro x; ring
      have e1 : (∫ x, (f x ^ 2 - (2 * lam) * (f x * g x) + lam ^ 2 * g x ^ 2) ∂ν) =
          (∫ x, (f x ^ 2 - (2 * lam) * (f x * g x)) ∂ν) +
            ∫ x, lam ^ 2 * g x ^ 2 ∂ν :=
        integral_add (hf2.sub (hfg.const_mul (2 * lam))) (hg2.const_mul (lam ^ 2))
      have e2 : (∫ x, (f x ^ 2 - (2 * lam) * (f x * g x)) ∂ν) =
          (∫ x, f x ^ 2 ∂ν) - ∫ x, (2 * lam) * (f x * g x) ∂ν :=
        integral_sub hf2 (hfg.const_mul (2 * lam))
      rw [integral_congr_ae (ae_of_all _ hpt), e1, e2, integral_const_mul,
        integral_const_mul]
    rw [hexp, hlamdef] at hquad
    have hcne : c ≠ 0 := ne_of_gt hc
    field_simp at hquad
    nlinarith [hquad, hc]

/-! ### `∫A = ∫d²` -/

section Basic

variable (W : Graphon Ω μ)

lemma integrable_pathOp : Integrable (pathOp W) μ :=
  integrable_of_bdd (measurable_pathOp W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (pathOp_nonneg W x)]
    exact pathOp_le_one W x

lemma integrable_pathOp_sq : Integrable (fun x ↦ pathOp W x ^ 2) μ :=
  integrable_of_bdd ((measurable_pathOp W).pow_const 2) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (pow_nonneg (pathOp_nonneg W x) 2)]
    exact pow_le_one₀ (pathOp_nonneg W x) (pathOp_le_one W x)

lemma integrable_pathOp_mul_degree :
    Integrable (fun x ↦ pathOp W x * degree W x) μ :=
  integrable_of_bdd ((measurable_pathOp W).mul (measurable_degree W)) (C := 1)
    fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg (pathOp_nonneg W x) (degree_nonneg W x))]
      exact mul_le_one₀ (pathOp_le_one W x) (degree_nonneg W x) (degree_le_one W x)

lemma integrable_pathOp_mul_rootedTriangle :
    Integrable (fun x ↦ pathOp W x * rootedTriangle W x) μ :=
  integrable_of_bdd ((measurable_pathOp W).mul (measurable_rootedTriangle W))
    (C := 1) fun x ↦ by
      rw [abs_of_nonneg (mul_nonneg (pathOp_nonneg W x) (rootedTriangle_nonneg W x))]
      exact mul_le_one₀ (pathOp_le_one W x) (rootedTriangle_nonneg W x)
        (rootedTriangle_le_one W x)

/-- **`T_W` is self-adjoint**, applied once: `∫ A = ∫ d²`. -/
theorem integral_pathOp : (∫ x, pathOp W x ∂μ) = moment W 2 := by
  have hint : Integrable
      (Function.uncurry fun x y ↦ W x y * degree W y) (μ.prod μ) := by
    refine integrable_prod_of_bdd
      (W.measurable.mul ((measurable_degree W).comp measurable_snd))
      (C := 1) fun q ↦ ?_
    show |W q.1 q.2 * degree W q.2| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) (degree_nonneg W _))]
    exact mul_le_one₀ (W.le_one _ _) (degree_nonneg W _) (degree_le_one W _)
  calc (∫ x, pathOp W x ∂μ) = ∫ x, ∫ y, W x y * degree W y ∂μ ∂μ := rfl
    _ = ∫ y, ∫ x, W x y * degree W y ∂μ ∂μ := integral_integral_swap hint
    _ = moment W 2 := by
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        simp only []
        rw [integral_mul_const]
        have hsym : (∫ x, W x y ∂μ) = degree W y :=
          integral_congr_ae (ae_of_all _ fun x ↦ W.symm x y)
        rw [hsym, sq]

/-- `M ≥ p²`, restated for `∫A`. -/
lemma sq_le_integral_pathOp (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 2 ≤ ∫ x, pathOp W x ∂μ := by
  rw [integral_pathOp]
  exact pow_le_moment W 2

/-- `N ≥ M²`, Cauchy–Schwarz against the constant `1`. -/
lemma sq_integral_pathOp_le (W : Graphon Ω μ) :
    (∫ x, pathOp W x ∂μ) ^ 2 ≤ ∫ x, pathOp W x ^ 2 ∂μ := by
  have h := sq_integral_mul_le (ν := μ) (f := pathOp W) (g := fun _ ↦ (1 : ℝ))
    (integrable_pathOp_sq W) (by simpa using (integrable_const (1 : ℝ)))
    (by simpa using integrable_pathOp W)
  simpa using h

/-- `B² ≤ N·M`, Cauchy–Schwarz between `A` and `d`. -/
lemma sq_integral_pathOp_mul_degree_le (W : Graphon Ω μ) :
    (∫ x, pathOp W x * degree W x ∂μ) ^ 2 ≤
      (∫ x, pathOp W x ^ 2 ∂μ) * ∫ x, pathOp W x ∂μ := by
  have h := sq_integral_mul_le (ν := μ) (f := pathOp W) (g := degree W)
    (integrable_pathOp_sq W) (integrable_degree_pow W 2)
    (integrable_pathOp_mul_degree W)
  rw [integral_pathOp]
  exact h

end Basic

/-! ### The pointwise Goodman bound, integrated against `A` -/

/-- `F ≥ 2N - pM`, from `τ ≥ 2A - p` weighted by `A ≥ 0`. -/
theorem two_mul_sq_sub_le_integral_pathOp_mul_rootedTriangle (W : Graphon Ω μ) :
    2 * (∫ x, pathOp W x ^ 2 ∂μ) -
        cliqueDensity 2 W * ∫ x, pathOp W x ∂μ ≤
      ∫ x, pathOp W x * rootedTriangle W x ∂μ := by
  have hlin : Integrable (fun x ↦ pathOp W x *
      (2 * pathOp W x - cliqueDensity 2 W)) μ := by
    have h := ((integrable_pathOp_sq W).const_mul 2).sub
      ((integrable_pathOp W).const_mul (cliqueDensity 2 W))
    refine h.congr (ae_of_all _ fun x ↦ ?_)
    show 2 * pathOp W x ^ 2 - cliqueDensity 2 W * pathOp W x =
      pathOp W x * (2 * pathOp W x - cliqueDensity 2 W)
    ring
  have hmono : (∫ x, pathOp W x * (2 * pathOp W x - cliqueDensity 2 W) ∂μ) ≤
      ∫ x, pathOp W x * rootedTriangle W x ∂μ :=
    integral_mono hlin (integrable_pathOp_mul_rootedTriangle W) fun x ↦
      mul_le_mul_of_nonneg_left (rootedTriangle_ge W x) (pathOp_nonneg W x)
  refine le_trans (le_of_eq ?_) hmono
  have hpt : ∀ x, pathOp W x * (2 * pathOp W x - cliqueDensity 2 W) =
      2 * pathOp W x ^ 2 - cliqueDensity 2 W * pathOp W x := by
    intro x; ring
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_sub ((integrable_pathOp_sq W).const_mul 2)
      ((integrable_pathOp W).const_mul (cliqueDensity 2 W)),
    integral_const_mul, integral_const_mul]

/-! ### The two scalar inputs -/

/-- **The `A`-weighted rooted-triangle inequality**, `F ≥ (2p-1)B`, on the
required interval `p ≥ 1/2`. -/
theorem weighted_le_integral_pathOp_mul_rootedTriangle (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    (2 * cliqueDensity 2 W - 1) * (∫ x, pathOp W x * degree W x ∂μ) ≤
      ∫ x, pathOp W x * rootedTriangle W x ∂μ := by
  set p := cliqueDensity 2 W with hpdef
  set M := ∫ x, pathOp W x ∂μ with hMdef
  set N := ∫ x, pathOp W x ^ 2 ∂μ with hNdef
  set B := ∫ x, pathOp W x * degree W x ∂μ with hBdef
  have hMp : p ^ 2 ≤ M := sq_le_integral_pathOp W
  have hNM : M ^ 2 ≤ N := sq_integral_pathOp_le W
  have hBNM : B ^ 2 ≤ N * M := sq_integral_pathOp_mul_degree_le W
  have hB0 : 0 ≤ B :=
    integral_nonneg fun x ↦ mul_nonneg (pathOp_nonneg W x) (degree_nonneg W x)
  have hM0 : 0 ≤ M := le_trans (sq_nonneg p) hMp
  have hMquarter : (1 : ℝ) / 4 ≤ M := by nlinarith [hMp, hp, sq_nonneg (p - 1 / 2)]
  -- the two nonnegative factors of `(2N - pM)² - (2p-1)²NM`
  have hf1 : 0 ≤ 4 * N - M := by nlinarith [hNM, hMquarter, hM0]
  have hf2 : 0 ≤ N - p ^ 2 * M := by nlinarith [hNM, hMp, hM0]
  have hLHS : 0 ≤ 2 * N - p * M := by nlinarith [hNM, hMp, hM0, hp]
  have hRHS : 0 ≤ (2 * p - 1) * B := mul_nonneg (by linarith) hB0
  have hprod : 0 ≤ (4 * N - M) * (N - p ^ 2 * M) := mul_nonneg hf1 hf2
  have hid : (2 * N - p * M) ^ 2 - (2 * p - 1) ^ 2 * (N * M) =
      (4 * N - M) * (N - p ^ 2 * M) := by ring
  have hscale : (2 * p - 1) ^ 2 * B ^ 2 ≤ (2 * p - 1) ^ 2 * (N * M) :=
    mul_le_mul_of_nonneg_left hBNM (sq_nonneg _)
  have hsq : ((2 * p - 1) * B) ^ 2 ≤ (2 * N - p * M) ^ 2 := by
    nlinarith [hscale, hprod, hid]
  have hkey : (2 * p - 1) * B ≤ 2 * N - p * M := by
    nlinarith [hsq, hLHS, hRHS]
  exact le_trans hkey
    (two_mul_sq_sub_le_integral_pathOp_mul_rootedTriangle W)

/-- **The sharp first-page bound**, `F ≥ p³(2p-1)`.  This is the density of the
triangle with a two-edge tail, `t(R₁,W)`. -/
theorem firstPage_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ≤
      ∫ x, pathOp W x * rootedTriangle W x ∂μ := by
  set p := cliqueDensity 2 W with hpdef
  set M := ∫ x, pathOp W x ∂μ with hMdef
  set N := ∫ x, pathOp W x ^ 2 ∂μ with hNdef
  have hMp : p ^ 2 ≤ M := sq_le_integral_pathOp W
  have hNM : M ^ 2 ≤ N := sq_integral_pathOp_le W
  have hM0 : 0 ≤ M := le_trans (sq_nonneg p) hMp
  have hid : 2 * M ^ 2 - p * M - p ^ 3 * (2 * p - 1) =
      (M - p ^ 2) * (2 * (M + p ^ 2) - p) := by ring
  have hpos : 0 ≤ (M - p ^ 2) * (2 * (M + p ^ 2) - p) :=
    mul_nonneg (by linarith) (by nlinarith [hMp, hp])
  have hstep : p ^ 3 * (2 * p - 1) ≤ 2 * N - p * M := by linarith
  exact le_trans hstep
    (two_mul_sq_sub_le_integral_pathOp_mul_rootedTriangle W)

end Taeyoung.Methods.BookTail
