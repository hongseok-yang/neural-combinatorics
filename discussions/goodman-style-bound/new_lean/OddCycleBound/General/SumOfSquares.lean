import OddCycleBound.PathDensity

/-!
# The moment sum-of-squares engine (general degree)

`Graphon.lean` / `Certificate.lean` provide the fixed-degree Hankel SOS lemmas `sos1`, `sos2`.
Here we prove the **general** one, once:

  `0 ≤ Σ_{i,j<N} cᵢ cⱼ s_{i+j}` for every coefficient vector `c : ℕ → ℝ` and every `N`,

as `0 ≤ ∫ (Σ_{i<N} cᵢ hᵢ)²`, expanded by `Finset.sum_mul_sum` and the moment identity
`∫ hᵢ hⱼ = s_{i+j}`.  This is the Hankel-form-PSD statement and the single engine all the
path-certificate positivity proofs reduce to.  The fixed-degree `sos3` (the degree-3 form,
needed for the `C₉` linear part) is derived from it.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- **Bilinear moment expansion**: `∫ (Σ uᵢ hᵢ)(Σ vⱼ hⱼ) = Σ_{i,j} uᵢ vⱼ s_{i+j}`. -/
lemma mombilin_expand (hU : IsGraphon U μ) (u v : ℕ → ℝ) (N : ℕ) :
    ∫ x, (∑ i ∈ Finset.range N, u i * compressIter U μ i x) * (∑ j ∈ Finset.range N, v j * compressIter U μ j x) ∂μ
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, u i * v j * specMoment U μ (i + j) := by
  have hint : ∀ i j, Integrable (fun x => u i * v j * (compressIter U μ i x * compressIter U μ j x)) μ :=
    fun i j => (((good_compressIter hU i).mul (good_compressIter hU j)).integrable).const_mul _
  have e1 : ∀ x, (∑ i ∈ Finset.range N, u i * compressIter U μ i x)
        * (∑ j ∈ Finset.range N, v j * compressIter U μ j x)
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          u i * v j * (compressIter U μ i x * compressIter U μ j x) := by
    intro x
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [integral_congr_ae (ae_of_all _ e1),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, moment hU j i]

/-- **Moment expansion of a square**: `∫ (Σ cᵢ hᵢ)² = Σ_{i,j} cᵢ cⱼ s_{i+j}`. -/
lemma momsq_expand (hU : IsGraphon U μ) (c : ℕ → ℝ) (N : ℕ) :
    ∫ x, (∑ i ∈ Finset.range N, c i * compressIter U μ i x) ^ 2 ∂μ
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i * c j * specMoment U μ (i + j) := by
  rw [show (fun x => (∑ i ∈ Finset.range N, c i * compressIter U μ i x) ^ 2)
      = (fun x => (∑ i ∈ Finset.range N, c i * compressIter U μ i x)
          * (∑ j ∈ Finset.range N, c j * compressIter U μ j x)) from by funext x; rw [sq]]
  exact mombilin_expand hU c c N

/-- **The general Hankel SOS form is PSD.**  For every `c : ℕ → ℝ` and `N`,
`0 ≤ Σ_{i,j<N} cᵢ cⱼ s_{i+j}`. -/
lemma sos_sq_expand (hU : IsGraphon U μ) (c : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i * c j * specMoment U μ (i + j) := by
  rw [← momsq_expand hU c N]; exact integral_nonneg fun x => sq_nonneg _

/-- The zero function is `Good`. -/
lemma good_zero : Good (fun _ : Ω => (0 : ℝ)) :=
  ⟨stronglyMeasurable_const, ⟨0, le_refl 0, fun _ => by simp⟩⟩

/-- A finite moment combination `x ↦ Σ_{a<N} cₐ hₐ(x)` is `Good`. -/
lemma good_momcombo (hU : IsGraphon U μ) (c : ℕ → ℝ) :
    ∀ N, Good (fun x => ∑ a ∈ Finset.range N, c a * compressIter U μ a x)
  | 0 => by simpa using good_zero
  | (N + 1) => by
      have he : (fun x => ∑ a ∈ Finset.range (N + 1), c a * compressIter U μ a x)
          = (fun x => (∑ a ∈ Finset.range N, c a * compressIter U μ a x) + c N * compressIter U μ N x) := by
        funext x; rw [Finset.sum_range_succ]
      rw [he]
      exact good_add (good_momcombo hU c N) (good_smul (c N) (good_compressIter hU N))

/-- **The general two-variable product-measure SOS is PSD.**  For every `C : ℕ → ℕ → ℝ` and `N`,
`0 ≤ Σ_{a,b,c,d<N} C(a,b)·C(c,d)·s_{a+c}·s_{b+d}`, proved as
`0 ≤ ∫∫ (Σ_{a,b} C(a,b)·hₐ(x)·hᵦ(y))²`.  This is the engine for the multivariate (kernel)
positivity parts of the path certificates (`C₉` quadratic part, `C₁₁`/`C₁₃` Bernstein kernels). -/
lemma sos_sq_expand_2var (hU : IsGraphon U μ) (C : ℕ → ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N, ∑ a ∈ Finset.range N, ∑ c ∈ Finset.range N,
          C a b * C c d * (specMoment U μ (a + c) * specMoment U μ (b + d)) := by
  have hg : ∀ b, Good (fun x => ∑ a ∈ Finset.range N, C a b * compressIter U μ a x) :=
    fun b => good_momcombo hU (fun a => C a b) N
  set F : Ω → ℝ := fun x => ∫ y, (∑ b ∈ Finset.range N,
      (∑ a ∈ Finset.range N, C a b * compressIter U μ a x) * compressIter U μ b y) ^ 2 ∂μ with hF
  have hFnn : ∀ x, 0 ≤ F x := fun x => integral_nonneg fun y => sq_nonneg _
  have hFeq : ∀ x, F x = ∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N,
      (∑ a ∈ Finset.range N, C a b * compressIter U μ a x)
        * (∑ c ∈ Finset.range N, C c d * compressIter U μ c x) * specMoment U μ (b + d) := by
    intro x
    show (∫ y, (∑ b ∈ Finset.range N,
        (∑ a ∈ Finset.range N, C a b * compressIter U μ a x) * compressIter U μ b y) ^ 2 ∂μ) = _
    rw [momsq_expand hU (fun b => ∑ a ∈ Finset.range N, C a b * compressIter U μ a x) N]
  have hInt : ∀ b d, Integrable (fun x => (∑ a ∈ Finset.range N, C a b * compressIter U μ a x)
      * (∑ c ∈ Finset.range N, C c d * compressIter U μ c x) * specMoment U μ (b + d)) μ :=
    fun b d => (((hg b).mul (hg d)).integrable).mul_const _
  have key : ∫ x, F x ∂μ = ∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N,
      ∑ a ∈ Finset.range N, ∑ c ∈ Finset.range N,
        C a b * C c d * (specMoment U μ (a + c) * specMoment U μ (b + d)) := by
    rw [integral_congr_ae (ae_of_all _ hFeq),
      integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ => hInt b d))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ (fun d _ => hInt b d)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show (fun x => (∑ a ∈ Finset.range N, C a b * compressIter U μ a x)
          * (∑ c ∈ Finset.range N, C c d * compressIter U μ c x) * specMoment U μ (b + d))
        = (fun x => specMoment U μ (b + d) * ((∑ a ∈ Finset.range N, C a b * compressIter U μ a x)
          * (∑ c ∈ Finset.range N, C c d * compressIter U μ c x))) from by funext x; ring,
      integral_const_mul, mombilin_expand hU (fun a => C a b) (fun c => C c d) N,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [← key]; exact integral_nonneg hFnn

/-- **The general three-variable product-measure SOS is PSD.**  For every `C : ℕ → ℕ → ℕ → ℝ`
and `N`, `0 ≤ Σ C(a,b,c)·C(d,e,f)·s_{a+d}·s_{b+e}·s_{c+f}`, proved as
`0 ≤ ∫∫∫ (Σ C(a,b,c)·hₐ(x)·hᵦ(y)·h_c(z))²`.  The engine for the cubic (`C₁₁`/`C₁₃`) kernel parts. -/
lemma sos_sq_expand_3var (hU : IsGraphon U μ) (C : ℕ → ℕ → ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ c ∈ Finset.range N, ∑ f ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ e ∈ Finset.range N,
          ∑ a ∈ Finset.range N, ∑ d ∈ Finset.range N,
          C a b c * C d e f * (specMoment U μ (a + d) * specMoment U μ (b + e) * specMoment U μ (c + f)) := by
  -- coefficient combos that are `Good`
  have hgx : ∀ b c, Good (fun x => ∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) :=
    fun b c => good_momcombo hU (fun a => C a b c) N
  -- G x = ∫∫_{y,z} (Σ_{a,b,c} C a b c · hₐ(x) hᵦ(y) h_c(z))²
  set G : Ω → ℝ := fun x => ∫ y, ∫ z, (∑ c ∈ Finset.range N,
      (∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x)
        * compressIter U μ b y) * compressIter U μ c z) ^ 2 ∂μ ∂μ with hG
  have hGnn : ∀ x, 0 ≤ G x := fun x => integral_nonneg fun y => integral_nonneg fun z => sq_nonneg _
  -- inner z-integral by momsq_expand, then y-integral by mombilin_expand
  have hGeq : ∀ x, G x = ∑ c ∈ Finset.range N, ∑ f ∈ Finset.range N, ∑ b ∈ Finset.range N,
      ∑ e ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x)
        * (∑ d ∈ Finset.range N, C d e f * compressIter U μ d x)
        * (specMoment U μ (b + e) * specMoment U μ (c + f)) := by
    intro x
    have hz : ∀ y, (∫ z, (∑ c ∈ Finset.range N, (∑ b ∈ Finset.range N,
          (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) * compressIter U μ b y)
          * compressIter U μ c z) ^ 2 ∂μ)
        = ∑ c ∈ Finset.range N, ∑ f ∈ Finset.range N,
          (∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) * compressIter U μ b y)
          * (∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b f * compressIter U μ a x) * compressIter U μ b y)
          * specMoment U μ (c + f) := fun y =>
      momsq_expand hU (fun c => ∑ b ∈ Finset.range N,
        (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) * compressIter U μ b y) N
    show (∫ y, (∫ z, _ ∂μ) ∂μ) = _
    rw [integral_congr_ae (ae_of_all _ hz)]
    -- now integrate the (c,f) sum over y
    have hgy : ∀ c, Good (fun y => ∑ b ∈ Finset.range N,
        (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) * compressIter U μ b y) :=
      fun c => good_momcombo hU (fun b => (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x)) N
    have hInty : ∀ c f, Integrable (fun y => (∑ b ∈ Finset.range N,
        (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) * compressIter U μ b y)
        * (∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b f * compressIter U μ a x) * compressIter U μ b y)
        * specMoment U μ (c + f)) μ :=
      fun c f => (((hgy c).mul (hgy f)).integrable).mul_const _
    rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun f _ => hInty c f))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ (fun f _ => hInty c f)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [show (fun y => (∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) * compressIter U μ b y)
          * (∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b f * compressIter U μ a x) * compressIter U μ b y)
          * specMoment U μ (c + f))
        = (fun y => specMoment U μ (c + f) * ((∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x) * compressIter U μ b y)
          * (∑ b ∈ Finset.range N, (∑ a ∈ Finset.range N, C a b f * compressIter U μ a x) * compressIter U μ b y))) from by funext y; ring,
      integral_const_mul,
      mombilin_expand hU (fun b => ∑ a ∈ Finset.range N, C a b c * compressIter U μ a x)
        (fun b => ∑ a ∈ Finset.range N, C a b f * compressIter U μ a x) N, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  -- outer x-integral by mombilin_expand
  have hIntx : ∀ c f b e, Integrable (fun x => (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x)
      * (∑ d ∈ Finset.range N, C d e f * compressIter U μ d x) * (specMoment U μ (b + e) * specMoment U μ (c + f))) μ :=
    fun c f b e => (((hgx b c).mul (hgx e f)).integrable).mul_const _
  have key : ∫ x, G x ∂μ = ∑ c ∈ Finset.range N, ∑ f ∈ Finset.range N, ∑ b ∈ Finset.range N,
      ∑ e ∈ Finset.range N, ∑ a ∈ Finset.range N, ∑ d ∈ Finset.range N,
        C a b c * C d e f * (specMoment U μ (a + d) * specMoment U μ (b + e) * specMoment U μ (c + f)) := by
    rw [integral_congr_ae (ae_of_all _ hGeq)]
    rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun f _ =>
      integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun e _ => hIntx c f b e))))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ (fun f _ => integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun e _ => hIntx c f b e)))]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun e _ => hIntx c f b e))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ (fun e _ => hIntx c f b e)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show (fun x => (∑ a ∈ Finset.range N, C a b c * compressIter U μ a x)
          * (∑ d ∈ Finset.range N, C d e f * compressIter U μ d x) * (specMoment U μ (b + e) * specMoment U μ (c + f)))
        = (fun x => (specMoment U μ (b + e) * specMoment U μ (c + f)) * ((∑ a ∈ Finset.range N, C a b c * compressIter U μ a x)
          * (∑ d ∈ Finset.range N, C d e f * compressIter U μ d x))) from by funext x; ring,
      integral_const_mul, mombilin_expand hU (fun a => C a b c) (fun d => C d e f) N, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [← key]; exact integral_nonneg hGnn

/-- **Degree-`(2,2)` bivariate SOS** (`s₀ … s₄`): for a bivariate polynomial
`ψ(λ,μ) = Σ_{a,b≤2} c_{ab} λᵃμᵇ`, the moment value `∫∫ψ² ≥ 0`.  The engine for the `C₉`
quadratic part.  Derived from `sos_sq_expand_2var` with the 3×3 coefficient matrix. -/
lemma sos2var3 (hU : IsGraphon U μ) (c00 c01 c02 c10 c11 c12 c20 c21 c22 : ℝ) :
    0 ≤ c00^2*specMoment U μ 0^2 + 2*c00*c01*specMoment U μ 0*specMoment U μ 1 + 2*c00*c02*specMoment U μ 0*specMoment U μ 2
      + 2*c00*c10*specMoment U μ 0*specMoment U μ 1 + 2*c00*c11*specMoment U μ 1^2 + 2*c00*c12*specMoment U μ 1*specMoment U μ 2
      + 2*c00*c20*specMoment U μ 0*specMoment U μ 2 + 2*c00*c21*specMoment U μ 1*specMoment U μ 2 + 2*c00*c22*specMoment U μ 2^2
      + c01^2*specMoment U μ 0*specMoment U μ 2 + 2*c01*c02*specMoment U μ 0*specMoment U μ 3 + 2*c01*c10*specMoment U μ 1^2
      + 2*c01*c11*specMoment U μ 1*specMoment U μ 2 + 2*c01*c12*specMoment U μ 1*specMoment U μ 3 + 2*c01*c20*specMoment U μ 1*specMoment U μ 2
      + 2*c01*c21*specMoment U μ 2^2 + 2*c01*c22*specMoment U μ 2*specMoment U μ 3 + c02^2*specMoment U μ 0*specMoment U μ 4
      + 2*c02*c10*specMoment U μ 1*specMoment U μ 2 + 2*c02*c11*specMoment U μ 1*specMoment U μ 3 + 2*c02*c12*specMoment U μ 1*specMoment U μ 4
      + 2*c02*c20*specMoment U μ 2^2 + 2*c02*c21*specMoment U μ 2*specMoment U μ 3 + 2*c02*c22*specMoment U μ 2*specMoment U μ 4
      + c10^2*specMoment U μ 0*specMoment U μ 2 + 2*c10*c11*specMoment U μ 1*specMoment U μ 2 + 2*c10*c12*specMoment U μ 2^2
      + 2*c10*c20*specMoment U μ 0*specMoment U μ 3 + 2*c10*c21*specMoment U μ 1*specMoment U μ 3 + 2*c10*c22*specMoment U μ 2*specMoment U μ 3
      + c11^2*specMoment U μ 2^2 + 2*c11*c12*specMoment U μ 2*specMoment U μ 3 + 2*c11*c20*specMoment U μ 1*specMoment U μ 3
      + 2*c11*c21*specMoment U μ 2*specMoment U μ 3 + 2*c11*c22*specMoment U μ 3^2 + c12^2*specMoment U μ 2*specMoment U μ 4
      + 2*c12*c20*specMoment U μ 2*specMoment U μ 3 + 2*c12*c21*specMoment U μ 3^2 + 2*c12*c22*specMoment U μ 3*specMoment U μ 4
      + c20^2*specMoment U μ 0*specMoment U μ 4 + 2*c20*c21*specMoment U μ 1*specMoment U μ 4 + 2*c20*c22*specMoment U μ 2*specMoment U μ 4
      + c21^2*specMoment U μ 2*specMoment U μ 4 + 2*c21*c22*specMoment U μ 3*specMoment U μ 4 + c22^2*specMoment U μ 4^2 := by
  have h := sos_sq_expand_2var hU
    (fun a b => if a = 0 then (if b = 0 then c00 else if b = 1 then c01 else c02)
      else if a = 1 then (if b = 0 then c10 else if b = 1 then c11 else c12)
      else (if b = 0 then c20 else if b = 1 then c21 else c22)) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  nlinarith [h]

/-- The shifted degree-1 square `0 ≤ ∫(t·hᵢ + hⱼ)²` expanded: `0 ≤ s_{2i}·t² + 2s_{i+j}·t + s_{2j}`. -/
lemma momquad (hU : IsGraphon U μ) (i j : ℕ) (t : ℝ) :
    0 ≤ specMoment U μ (i + i) * t ^ 2 + 2 * specMoment U μ (i + j) * t + specMoment U μ (j + j) := by
  have hnn : 0 ≤ ∫ x, (t * compressIter U μ i x + compressIter U μ j x) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have hii : Integrable (fun x => t ^ 2 * (compressIter U μ i x * compressIter U μ i x)) μ :=
    (((good_compressIter hU i).mul (good_compressIter hU i)).integrable).const_mul _
  have hij : Integrable (fun x => 2 * t * (compressIter U μ i x * compressIter U μ j x)) μ :=
    (((good_compressIter hU i).mul (good_compressIter hU j)).integrable).const_mul _
  have hjj : Integrable (fun x => compressIter U μ j x * compressIter U μ j x) μ :=
    ((good_compressIter hU j).mul (good_compressIter hU j)).integrable
  have hrest : Integrable (fun x => 2 * t * (compressIter U μ i x * compressIter U μ j x)
      + compressIter U μ j x * compressIter U μ j x) μ := hij.add hjj
  have hexp : ∫ x, (t * compressIter U μ i x + compressIter U μ j x) ^ 2 ∂μ
      = specMoment U μ (i + i) * t ^ 2 + 2 * specMoment U μ (i + j) * t + specMoment U μ (j + j) := by
    rw [show (fun x => (t * compressIter U μ i x + compressIter U μ j x) ^ 2)
        = (fun x => t ^ 2 * (compressIter U μ i x * compressIter U μ i x)
            + (2 * t * (compressIter U μ i x * compressIter U μ j x) + compressIter U μ j x * compressIter U μ j x)) from by
          funext x; ring,
      integral_add hii hrest, integral_add hij hjj,
      integral_const_mul, integral_const_mul, moment hU i i, moment hU j i, moment hU j j]
    ring
  rw [hexp] at hnn; exact hnn

/-- **The `2×2` Hankel / Cauchy–Schwarz minor**: `s_{i+j}² ≤ s_{2i}·s_{2j}`. -/
lemma momcs (hU : IsGraphon U μ) (i j : ℕ) :
    specMoment U μ (i + j) ^ 2 ≤ specMoment U μ (i + i) * specMoment U μ (j + j) := by
  have h : ∀ x : ℝ, 0 ≤ specMoment U μ (i + i) * (x * x) + 2 * specMoment U μ (i + j) * x + specMoment U μ (j + j) :=
    fun x => by have := momquad hU i j x; nlinarith [this]
  have hd := discrim_le_zero h
  simp only [discrim] at hd
  nlinarith [hd]

/-- **Degree-3 Hankel SOS** (`s₀ … s₆`): the engine for the `C₉` linear part.  Derived from
`sos_sq_expand` with the four-term coefficient vector `(c₀,c₁,c₂,c₃)`. -/
lemma sos3 (hU : IsGraphon U μ) (c3 c2 c1 c0 : ℝ) :
    0 ≤ c3 ^ 2 * specMoment U μ 6 + 2 * c3 * c2 * specMoment U μ 5 + (2 * c3 * c1 + c2 ^ 2) * specMoment U μ 4
      + (2 * c3 * c0 + 2 * c2 * c1) * specMoment U μ 3 + (2 * c2 * c0 + c1 ^ 2) * specMoment U μ 2
      + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
  have h := sos_sq_expand hU
    (fun k => if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else c3) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  nlinarith [h]

/-- **Degree-4 Hankel SOS** (`s₀ … s₈`): the engine for the `C₁₁` linear part.  Derived from
`sos_sq_expand` with the five-term coefficient vector `(c₀,c₁,c₂,c₃,c₄)`. -/
lemma sos4 (hU : IsGraphon U μ) (c4 c3 c2 c1 c0 : ℝ) :
    0 ≤ c4 ^ 2 * specMoment U μ 8 + 2 * c4 * c3 * specMoment U μ 7
      + (2 * c4 * c2 + c3 ^ 2) * specMoment U μ 6 + (2 * c4 * c1 + 2 * c3 * c2) * specMoment U μ 5
      + (2 * c4 * c0 + 2 * c3 * c1 + c2 ^ 2) * specMoment U μ 4
      + (2 * c3 * c0 + 2 * c2 * c1) * specMoment U μ 3 + (2 * c2 * c0 + c1 ^ 2) * specMoment U μ 2
      + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
  have h := sos_sq_expand hU
    (fun k => if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else if k = 3 then c3 else c4) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  nlinarith [h]

/-- **Degree-5 Hankel SOS** (`s₀ … s₁₀`): the engine for the `C₁₃` linear part.  Derived from
`sos_sq_expand` with the six-term coefficient vector `(c₀,…,c₅)`. -/
lemma sos5 (hU : IsGraphon U μ) (c5 c4 c3 c2 c1 c0 : ℝ) :
    0 ≤ c5 ^ 2 * specMoment U μ 10 + 2 * c5 * c4 * specMoment U μ 9
      + (2 * c5 * c3 + c4 ^ 2) * specMoment U μ 8 + (2 * c5 * c2 + 2 * c4 * c3) * specMoment U μ 7
      + (2 * c5 * c1 + 2 * c4 * c2 + c3 ^ 2) * specMoment U μ 6
      + (2 * c5 * c0 + 2 * c4 * c1 + 2 * c3 * c2) * specMoment U μ 5
      + (2 * c4 * c0 + 2 * c3 * c1 + c2 ^ 2) * specMoment U μ 4
      + (2 * c3 * c0 + 2 * c2 * c1) * specMoment U μ 3 + (2 * c2 * c0 + c1 ^ 2) * specMoment U μ 2
      + 2 * c1 * c0 * specMoment U μ 1 + c0 ^ 2 * specMoment U μ 0 := by
  have h := sos_sq_expand hU
    (fun k => if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else if k = 3 then c3
      else if k = 4 then c4 else c5) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  nlinarith [h]


-- Degree-(3,3) bivariate Hankel SOS (basis monomials of degree < 4).
set_option maxHeartbeats 2000000 in
lemma sos2var4 (hU : IsGraphon U μ) (c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 c30 c31 c32 c33 : ℝ) :
    0 ≤ (c00^2) * (specMoment U μ 0 ^ 2) + (2*c00*c01 + 2*c00*c10) * (specMoment U μ 0 * specMoment U μ 1) + (2*c00*c02 + 2*c00*c20 + c01^2 + c10^2) * (specMoment U μ 0 * specMoment U μ 2) + (2*c00*c03 + 2*c00*c30 + 2*c01*c02 + 2*c10*c20) * (specMoment U μ 0 * specMoment U μ 3) + (2*c01*c03 + c02^2 + 2*c10*c30 + c20^2) * (specMoment U μ 0 * specMoment U μ 4) + (2*c02*c03 + 2*c20*c30) * (specMoment U μ 0 * specMoment U μ 5) + (c03^2 + c30^2) * (specMoment U μ 0 * specMoment U μ 6) + (2*c00*c11 + 2*c01*c10) * (specMoment U μ 1 ^ 2) + (2*c00*c12 + 2*c00*c21 + 2*c01*c11 + 2*c01*c20 + 2*c02*c10 + 2*c10*c11) * (specMoment U μ 1 * specMoment U μ 2) + (2*c00*c13 + 2*c00*c31 + 2*c01*c12 + 2*c01*c30 + 2*c02*c11 + 2*c03*c10 + 2*c10*c21 + 2*c11*c20) * (specMoment U μ 1 * specMoment U μ 3) + (2*c01*c13 + 2*c02*c12 + 2*c03*c11 + 2*c10*c31 + 2*c11*c30 + 2*c20*c21) * (specMoment U μ 1 * specMoment U μ 4) + (2*c02*c13 + 2*c03*c12 + 2*c20*c31 + 2*c21*c30) * (specMoment U μ 1 * specMoment U μ 5) + (2*c03*c13 + 2*c30*c31) * (specMoment U μ 1 * specMoment U μ 6) + (2*c00*c22 + 2*c01*c21 + 2*c02*c20 + 2*c10*c12 + c11^2) * (specMoment U μ 2 ^ 2) + (2*c00*c23 + 2*c00*c32 + 2*c01*c22 + 2*c01*c31 + 2*c02*c21 + 2*c02*c30 + 2*c03*c20 + 2*c10*c13 + 2*c10*c22 + 2*c11*c12 + 2*c11*c21 + 2*c12*c20) * (specMoment U μ 2 * specMoment U μ 3) + (2*c01*c23 + 2*c02*c22 + 2*c03*c21 + 2*c10*c32 + 2*c11*c13 + 2*c11*c31 + c12^2 + 2*c12*c30 + 2*c20*c22 + c21^2) * (specMoment U μ 2 * specMoment U μ 4) + (2*c02*c23 + 2*c03*c22 + 2*c12*c13 + 2*c20*c32 + 2*c21*c31 + 2*c22*c30) * (specMoment U μ 2 * specMoment U μ 5) + (2*c03*c23 + c13^2 + 2*c30*c32 + c31^2) * (specMoment U μ 2 * specMoment U μ 6) + (2*c00*c33 + 2*c01*c32 + 2*c02*c31 + 2*c03*c30 + 2*c10*c23 + 2*c11*c22 + 2*c12*c21 + 2*c13*c20) * (specMoment U μ 3 ^ 2) + (2*c01*c33 + 2*c02*c32 + 2*c03*c31 + 2*c10*c33 + 2*c11*c23 + 2*c11*c32 + 2*c12*c22 + 2*c12*c31 + 2*c13*c21 + 2*c13*c30 + 2*c20*c23 + 2*c21*c22) * (specMoment U μ 3 * specMoment U μ 4) + (2*c02*c33 + 2*c03*c32 + 2*c12*c23 + 2*c13*c22 + 2*c20*c33 + 2*c21*c32 + 2*c22*c31 + 2*c23*c30) * (specMoment U μ 3 * specMoment U μ 5) + (2*c03*c33 + 2*c13*c23 + 2*c30*c33 + 2*c31*c32) * (specMoment U μ 3 * specMoment U μ 6) + (2*c11*c33 + 2*c12*c32 + 2*c13*c31 + 2*c21*c23 + c22^2) * (specMoment U μ 4 ^ 2) + (2*c12*c33 + 2*c13*c32 + 2*c21*c33 + 2*c22*c23 + 2*c22*c32 + 2*c23*c31) * (specMoment U μ 4 * specMoment U μ 5) + (2*c13*c33 + c23^2 + 2*c31*c33 + c32^2) * (specMoment U μ 4 * specMoment U μ 6) + (2*c22*c33 + 2*c23*c32) * (specMoment U μ 5 ^ 2) + (2*c23*c33 + 2*c32*c33) * (specMoment U μ 5 * specMoment U μ 6) + (c33^2) * (specMoment U μ 6 ^ 2) := by
  have h := sos_sq_expand_2var hU (fun a b => if a = 0 then (if b = 0 then c00 else if b = 1 then c01 else if b = 2 then c02 else if b = 3 then c03 else 0) else  if a = 1 then (if b = 0 then c10 else if b = 1 then c11 else if b = 2 then c12 else if b = 3 then c13 else 0) else  if a = 2 then (if b = 0 then c20 else if b = 1 then c21 else if b = 2 then c22 else if b = 3 then c23 else 0) else  if a = 3 then (if b = 0 then c30 else if b = 1 then c31 else if b = 2 then c32 else if b = 3 then c33 else 0) else 0) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  nlinarith [h]

-- Trivariate Hankel SOS over the Newton basis (total degree <= 2 in lam,mu,nu).
set_option maxHeartbeats 4000000 in
lemma sos3var3 (hU : IsGraphon U μ) (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : ℝ) :
    0 ≤ (d0^2) * (specMoment U μ 0 ^ 3) + (2*d0*d1 + 2*d0*d2 + 2*d0*d3) * (specMoment U μ 0 ^ 2 * specMoment U μ 1) + (2*d0*d4 + 2*d0*d5 + 2*d0*d6 + d1^2 + d2^2 + d3^2) * (specMoment U μ 0 ^ 2 * specMoment U μ 2) + (2*d1*d4 + 2*d2*d5 + 2*d3*d6) * (specMoment U μ 0 ^ 2 * specMoment U μ 3) + (d4^2 + d5^2 + d6^2) * (specMoment U μ 0 ^ 2 * specMoment U μ 4) + (2*d0*d7 + 2*d0*d8 + 2*d0*d9 + 2*d1*d2 + 2*d1*d3 + 2*d2*d3) * (specMoment U μ 0 * specMoment U μ 1 ^ 2) + (2*d1*d5 + 2*d1*d6 + 2*d1*d7 + 2*d1*d8 + 2*d2*d4 + 2*d2*d6 + 2*d2*d7 + 2*d2*d9 + 2*d3*d4 + 2*d3*d5 + 2*d3*d8 + 2*d3*d9) * (specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 2) + (2*d4*d7 + 2*d4*d8 + 2*d5*d7 + 2*d5*d9 + 2*d6*d8 + 2*d6*d9) * (specMoment U μ 0 * specMoment U μ 1 * specMoment U μ 3) + (2*d4*d5 + 2*d4*d6 + 2*d5*d6 + d7^2 + d8^2 + d9^2) * (specMoment U μ 0 * specMoment U μ 2 ^ 2) + (2*d1*d9 + 2*d2*d8 + 2*d3*d7) * (specMoment U μ 1 ^ 3) + (2*d4*d9 + 2*d5*d8 + 2*d6*d7 + 2*d7*d8 + 2*d7*d9 + 2*d8*d9) * (specMoment U μ 1 ^ 2 * specMoment U μ 2) := by
  have h := sos_sq_expand_3var hU (fun a b c => if a = 0 then (if b = 0 then (if c = 0 then d0 else if c = 1 then d3 else if c = 2 then d6 else 0) else if b = 1 then (if c = 0 then d2 else if c = 1 then d9 else if c = 2 then 0 else 0) else if b = 2 then (if c = 0 then d5 else if c = 1 then 0 else if c = 2 then 0 else 0) else 0) else  if a = 1 then (if b = 0 then (if c = 0 then d1 else if c = 1 then d8 else if c = 2 then 0 else 0) else if b = 1 then (if c = 0 then d7 else if c = 1 then 0 else if c = 2 then 0 else 0) else if b = 2 then (if c = 0 then 0 else if c = 1 then 0 else if c = 2 then 0 else 0) else 0) else  if a = 2 then (if b = 0 then (if c = 0 then d4 else if c = 1 then 0 else if c = 2 then 0 else 0) else if b = 1 then (if c = 0 then 0 else if c = 1 then 0 else if c = 2 then 0 else 0) else if b = 2 then (if c = 0 then 0 else if c = 1 then 0 else if c = 2 then 0 else 0) else 0) else 0) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  nlinarith [h]

end OddCycleBound
