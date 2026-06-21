import OddCycleBound.PathDensity

/-!
# The moment sum-of-squares engine (general degree)

`Graphon.lean` / `IntegralCert.lean` provide the fixed-degree Hankel SOS lemmas `sos1`, `sos2`.
Here we prove the **general** one, once:

  `0 ≤ Σ_{i,j<N} cᵢ cⱼ s_{i+j}` for every coefficient vector `c : ℕ → ℝ` and every `N`,

as `0 ≤ ∫ (Σ_{i<N} cᵢ hᵢ)²`, expanded by `Finset.sum_mul_sum` and the moment identity
`∫ hᵢ hⱼ = s_{i+j}`.  This is the Hankel-form-PSD statement and the single engine all the
path-certificate positivity proofs reduce to.  The fixed-degree `sos3` (the degree-3 form,
needed for the `C₉` linear part) is derived from it.
-/

open MeasureTheory

namespace OddCycleBound.Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- **Bilinear moment expansion**: `∫ (Σ uᵢ hᵢ)(Σ vⱼ hⱼ) = Σ_{i,j} uᵢ vⱼ s_{i+j}`. -/
lemma mombilin_expand (hU : IsGraphon U μ) (u v : ℕ → ℝ) (N : ℕ) :
    ∫ x, (∑ i ∈ Finset.range N, u i * hseq U μ i x) * (∑ j ∈ Finset.range N, v j * hseq U μ j x) ∂μ
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, u i * v j * smom U μ (i + j) := by
  have hint : ∀ i j, Integrable (fun x => u i * v j * (hseq U μ i x * hseq U μ j x)) μ :=
    fun i j => (((good_h hU i).mul (good_h hU j)).integrable).const_mul _
  have e1 : ∀ x, (∑ i ∈ Finset.range N, u i * hseq U μ i x)
        * (∑ j ∈ Finset.range N, v j * hseq U μ j x)
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          u i * v j * (hseq U μ i x * hseq U μ j x) := by
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
    ∫ x, (∑ i ∈ Finset.range N, c i * hseq U μ i x) ^ 2 ∂μ
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i * c j * smom U μ (i + j) := by
  rw [show (fun x => (∑ i ∈ Finset.range N, c i * hseq U μ i x) ^ 2)
      = (fun x => (∑ i ∈ Finset.range N, c i * hseq U μ i x)
          * (∑ j ∈ Finset.range N, c j * hseq U μ j x)) from by funext x; rw [sq]]
  exact mombilin_expand hU c c N

/-- **The general Hankel SOS form is PSD.**  For every `c : ℕ → ℝ` and `N`,
`0 ≤ Σ_{i,j<N} cᵢ cⱼ s_{i+j}`. -/
lemma sos_sq_expand (hU : IsGraphon U μ) (c : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i * c j * smom U μ (i + j) := by
  rw [← momsq_expand hU c N]; exact integral_nonneg fun x => sq_nonneg _

/-- The zero function is `Good`. -/
lemma good_zero : Good (fun _ : Ω => (0 : ℝ)) :=
  ⟨stronglyMeasurable_const, ⟨0, le_refl 0, fun _ => by simp⟩⟩

/-- A finite moment combination `x ↦ Σ_{a<N} cₐ hₐ(x)` is `Good`. -/
lemma good_momcombo (hU : IsGraphon U μ) (c : ℕ → ℝ) :
    ∀ N, Good (fun x => ∑ a ∈ Finset.range N, c a * hseq U μ a x)
  | 0 => by simpa using good_zero
  | (N + 1) => by
      have he : (fun x => ∑ a ∈ Finset.range (N + 1), c a * hseq U μ a x)
          = (fun x => (∑ a ∈ Finset.range N, c a * hseq U μ a x) + c N * hseq U μ N x) := by
        funext x; rw [Finset.sum_range_succ]
      rw [he]
      exact good_add (good_momcombo hU c N) (good_smul (c N) (good_h hU N))

/-- **The general two-variable product-measure SOS is PSD.**  For every `C : ℕ → ℕ → ℝ` and `N`,
`0 ≤ Σ_{a,b,c,d<N} C(a,b)·C(c,d)·s_{a+c}·s_{b+d}`, proved as
`0 ≤ ∫∫ (Σ_{a,b} C(a,b)·hₐ(x)·hᵦ(y))²`.  This is the engine for the multivariate (kernel)
positivity parts of the path certificates (`C₉` quadratic part, `C₁₁`/`C₁₃` Bernstein kernels). -/
lemma sos_sq_expand_2var (hU : IsGraphon U μ) (C : ℕ → ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N, ∑ a ∈ Finset.range N, ∑ c ∈ Finset.range N,
          C a b * C c d * (smom U μ (a + c) * smom U μ (b + d)) := by
  have hg : ∀ b, Good (fun x => ∑ a ∈ Finset.range N, C a b * hseq U μ a x) :=
    fun b => good_momcombo hU (fun a => C a b) N
  set F : Ω → ℝ := fun x => ∫ y, (∑ b ∈ Finset.range N,
      (∑ a ∈ Finset.range N, C a b * hseq U μ a x) * hseq U μ b y) ^ 2 ∂μ with hF
  have hFnn : ∀ x, 0 ≤ F x := fun x => integral_nonneg fun y => sq_nonneg _
  have hFeq : ∀ x, F x = ∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N,
      (∑ a ∈ Finset.range N, C a b * hseq U μ a x)
        * (∑ c ∈ Finset.range N, C c d * hseq U μ c x) * smom U μ (b + d) := by
    intro x
    show (∫ y, (∑ b ∈ Finset.range N,
        (∑ a ∈ Finset.range N, C a b * hseq U μ a x) * hseq U μ b y) ^ 2 ∂μ) = _
    rw [momsq_expand hU (fun b => ∑ a ∈ Finset.range N, C a b * hseq U μ a x) N]
  have hInt : ∀ b d, Integrable (fun x => (∑ a ∈ Finset.range N, C a b * hseq U μ a x)
      * (∑ c ∈ Finset.range N, C c d * hseq U μ c x) * smom U μ (b + d)) μ :=
    fun b d => (((hg b).mul (hg d)).integrable).mul_const _
  have key : ∫ x, F x ∂μ = ∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N,
      ∑ a ∈ Finset.range N, ∑ c ∈ Finset.range N,
        C a b * C c d * (smom U μ (a + c) * smom U μ (b + d)) := by
    rw [integral_congr_ae (ae_of_all _ hFeq),
      integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ => hInt b d))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ (fun d _ => hInt b d)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show (fun x => (∑ a ∈ Finset.range N, C a b * hseq U μ a x)
          * (∑ c ∈ Finset.range N, C c d * hseq U μ c x) * smom U μ (b + d))
        = (fun x => smom U μ (b + d) * ((∑ a ∈ Finset.range N, C a b * hseq U μ a x)
          * (∑ c ∈ Finset.range N, C c d * hseq U μ c x))) from by funext x; ring,
      integral_const_mul, mombilin_expand hU (fun a => C a b) (fun c => C c d) N,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [← key]; exact integral_nonneg hFnn

/-- **Degree-`(2,2)` bivariate SOS** (`s₀ … s₄`): for a bivariate polynomial
`ψ(λ,μ) = Σ_{a,b≤2} c_{ab} λᵃμᵇ`, the moment value `∫∫ψ² ≥ 0`.  The engine for the `C₉`
quadratic part.  Derived from `sos_sq_expand_2var` with the 3×3 coefficient matrix. -/
lemma sos2var3 (hU : IsGraphon U μ) (c00 c01 c02 c10 c11 c12 c20 c21 c22 : ℝ) :
    0 ≤ c00^2*smom U μ 0^2 + 2*c00*c01*smom U μ 0*smom U μ 1 + 2*c00*c02*smom U μ 0*smom U μ 2
      + 2*c00*c10*smom U μ 0*smom U μ 1 + 2*c00*c11*smom U μ 1^2 + 2*c00*c12*smom U μ 1*smom U μ 2
      + 2*c00*c20*smom U μ 0*smom U μ 2 + 2*c00*c21*smom U μ 1*smom U μ 2 + 2*c00*c22*smom U μ 2^2
      + c01^2*smom U μ 0*smom U μ 2 + 2*c01*c02*smom U μ 0*smom U μ 3 + 2*c01*c10*smom U μ 1^2
      + 2*c01*c11*smom U μ 1*smom U μ 2 + 2*c01*c12*smom U μ 1*smom U μ 3 + 2*c01*c20*smom U μ 1*smom U μ 2
      + 2*c01*c21*smom U μ 2^2 + 2*c01*c22*smom U μ 2*smom U μ 3 + c02^2*smom U μ 0*smom U μ 4
      + 2*c02*c10*smom U μ 1*smom U μ 2 + 2*c02*c11*smom U μ 1*smom U μ 3 + 2*c02*c12*smom U μ 1*smom U μ 4
      + 2*c02*c20*smom U μ 2^2 + 2*c02*c21*smom U μ 2*smom U μ 3 + 2*c02*c22*smom U μ 2*smom U μ 4
      + c10^2*smom U μ 0*smom U μ 2 + 2*c10*c11*smom U μ 1*smom U μ 2 + 2*c10*c12*smom U μ 2^2
      + 2*c10*c20*smom U μ 0*smom U μ 3 + 2*c10*c21*smom U μ 1*smom U μ 3 + 2*c10*c22*smom U μ 2*smom U μ 3
      + c11^2*smom U μ 2^2 + 2*c11*c12*smom U μ 2*smom U μ 3 + 2*c11*c20*smom U μ 1*smom U μ 3
      + 2*c11*c21*smom U μ 2*smom U μ 3 + 2*c11*c22*smom U μ 3^2 + c12^2*smom U μ 2*smom U μ 4
      + 2*c12*c20*smom U μ 2*smom U μ 3 + 2*c12*c21*smom U μ 3^2 + 2*c12*c22*smom U μ 3*smom U μ 4
      + c20^2*smom U μ 0*smom U μ 4 + 2*c20*c21*smom U μ 1*smom U μ 4 + 2*c20*c22*smom U μ 2*smom U μ 4
      + c21^2*smom U μ 2*smom U μ 4 + 2*c21*c22*smom U μ 3*smom U μ 4 + c22^2*smom U μ 4^2 := by
  have h := sos_sq_expand_2var hU
    (fun a b => if a = 0 then (if b = 0 then c00 else if b = 1 then c01 else c02)
      else if a = 1 then (if b = 0 then c10 else if b = 1 then c11 else c12)
      else (if b = 0 then c20 else if b = 1 then c21 else c22)) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  nlinarith [h]

/-- The shifted degree-1 square `0 ≤ ∫(t·hᵢ + hⱼ)²` expanded: `0 ≤ s_{2i}·t² + 2s_{i+j}·t + s_{2j}`. -/
lemma momquad (hU : IsGraphon U μ) (i j : ℕ) (t : ℝ) :
    0 ≤ smom U μ (i + i) * t ^ 2 + 2 * smom U μ (i + j) * t + smom U μ (j + j) := by
  have hnn : 0 ≤ ∫ x, (t * hseq U μ i x + hseq U μ j x) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have hii : Integrable (fun x => t ^ 2 * (hseq U μ i x * hseq U μ i x)) μ :=
    (((good_h hU i).mul (good_h hU i)).integrable).const_mul _
  have hij : Integrable (fun x => 2 * t * (hseq U μ i x * hseq U μ j x)) μ :=
    (((good_h hU i).mul (good_h hU j)).integrable).const_mul _
  have hjj : Integrable (fun x => hseq U μ j x * hseq U μ j x) μ :=
    ((good_h hU j).mul (good_h hU j)).integrable
  have hrest : Integrable (fun x => 2 * t * (hseq U μ i x * hseq U μ j x)
      + hseq U μ j x * hseq U μ j x) μ := hij.add hjj
  have hexp : ∫ x, (t * hseq U μ i x + hseq U μ j x) ^ 2 ∂μ
      = smom U μ (i + i) * t ^ 2 + 2 * smom U μ (i + j) * t + smom U μ (j + j) := by
    rw [show (fun x => (t * hseq U μ i x + hseq U μ j x) ^ 2)
        = (fun x => t ^ 2 * (hseq U μ i x * hseq U μ i x)
            + (2 * t * (hseq U μ i x * hseq U μ j x) + hseq U μ j x * hseq U μ j x)) from by
          funext x; ring,
      integral_add hii hrest, integral_add hij hjj,
      integral_const_mul, integral_const_mul, moment hU i i, moment hU j i, moment hU j j]
    ring
  rw [hexp] at hnn; exact hnn

/-- **The `2×2` Hankel / Cauchy–Schwarz minor**: `s_{i+j}² ≤ s_{2i}·s_{2j}`. -/
lemma momcs (hU : IsGraphon U μ) (i j : ℕ) :
    smom U μ (i + j) ^ 2 ≤ smom U μ (i + i) * smom U μ (j + j) := by
  have h : ∀ x : ℝ, 0 ≤ smom U μ (i + i) * (x * x) + 2 * smom U μ (i + j) * x + smom U μ (j + j) :=
    fun x => by have := momquad hU i j x; nlinarith [this]
  have hd := discrim_le_zero h
  simp only [discrim] at hd
  nlinarith [hd]

/-- **Degree-3 Hankel SOS** (`s₀ … s₆`): the engine for the `C₉` linear part.  Derived from
`sos_sq_expand` with the four-term coefficient vector `(c₀,c₁,c₂,c₃)`. -/
lemma sos3 (hU : IsGraphon U μ) (c3 c2 c1 c0 : ℝ) :
    0 ≤ c3 ^ 2 * smom U μ 6 + 2 * c3 * c2 * smom U μ 5 + (2 * c3 * c1 + c2 ^ 2) * smom U μ 4
      + (2 * c3 * c0 + 2 * c2 * c1) * smom U μ 3 + (2 * c2 * c0 + c1 ^ 2) * smom U μ 2
      + 2 * c1 * c0 * smom U μ 1 + c0 ^ 2 * smom U μ 0 := by
  have h := sos_sq_expand hU
    (fun k => if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else c3) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  nlinarith [h]

end OddCycleBound.Graphon
