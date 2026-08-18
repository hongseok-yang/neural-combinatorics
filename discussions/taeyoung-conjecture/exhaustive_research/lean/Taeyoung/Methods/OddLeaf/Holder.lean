import Taeyoung.Methods.OddLeaf.Bias
import Taeyoung.Methods.PathSidorenko

/-!
# The fractionally degree-weighted edge

`notes/odd_cycle_one_leaf.tex` Lemma 2.1 and `notes/bowtie_outer_leaves.tex`
Lemma 2.1 are the same statement at `β = 1/m`.  For

```
N = ∫∫ W(x,y)·d(x)^{1/m}·d(y)^{1/m} dμ(x)dμ(y)
```

three-factor Hölder at exponents `(m/(m+2), 1/(m+2), 1/(m+2))` applied to the
almost-everywhere factorization

```
W = (W·d(x)^{1/m}d(y)^{1/m})^{m/(m+2)}·(W/d(x))^{1/(m+2)}·(W/d(y))^{1/(m+2)}
```

gives `p ≤ N^{m/(m+2)}`, i.e. `p^{m+2} ≤ N^m`.  The two quotient factors
integrate to `μ{d>0} ≤ 1`, exactly as in `Methods/PathSidorenko.lean`, whose
`ℝ≥0∞` scaffolding — `edgeE`, `degE`, the two quotient bounds, and the null set
where the factorization breaks — is reused verbatim.  Only the exponents and
the first factor are new.

The statement is kept in the polynomial form `p^{m+2} ≤ N^m` rather than
`p^{1+2/m} ≤ N` so that the consumer never has to handle a real power of `p`.
The two scoped instances are `m = 5` (Atlas 104) and `m = 6` (Atlas 119).

The generic step that makes `m` a parameter is that the leading factor
regroups as a single `(m+2)`-nd root: `g₀^{m/(m+2)} = (g₀^m)^{1/(m+2)}`, and
`g₀^m·g₁·g₂ = W^{m+2}` because `(d^{1/m})^m = d` — which is `pow_rootE`, an
`ℕ`-power, precisely because the exponent is a reciprocal integer.
-/

open MeasureTheory Finset

open scoped ENNReal

namespace Taeyoung.Methods.OddLeaf

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PathSidorenko

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `d^{1/m}` in `ℝ≥0∞` -/

/-- `d^{1/m}`, pushed into `ℝ≥0∞`. -/
noncomputable def rootE (W : Graphon Ω μ) (m : ℕ) (x : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (rootDegree W m x)

section RootE

variable (W : Graphon Ω μ) {m : ℕ}

lemma measurable_rootE : Measurable (rootE W m) :=
  (measurable_rootDegree W).ennreal_ofReal

lemma rootE_ne_top (x : Ω) : rootE W m x ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `(d^{1/m})^m = d`, in `ℝ≥0∞`. -/
lemma pow_rootE (hm : m ≠ 0) (x : Ω) : rootE W m x ^ m = degE W x := by
  rw [rootE, degE, ← ENNReal.ofReal_pow (rootDegree_nonneg W x),
    pow_rootDegree W hm x]

lemma rootE_ne_zero (hm : m ≠ 0) {x : Ω} (hx : degE W x ≠ 0) :
    rootE W m x ≠ 0 := by
  intro h
  exact hx (by rw [← pow_rootE W hm x, h, zero_pow hm])

end RootE

/-! ### The fractionally weighted edge integral -/

/-- `N = ∫∫ W(x,y)d(x)^{1/m}d(y)^{1/m}`. -/
noncomputable def rootEdge (W : Graphon Ω μ) (m : ℕ) : ℝ :=
  ∫ q, W q.1 q.2 * rootDegree W m q.1 * rootDegree W m q.2 ∂(μ.prod μ)

section RootEdge

variable (W : Graphon Ω μ) {m : ℕ}

lemma measurable_rootEdgeIntegrand : Measurable fun q : Ω × Ω ↦
    W q.1 q.2 * rootDegree W m q.1 * rootDegree W m q.2 :=
  (W.measurable.mul ((measurable_rootDegree W).comp measurable_fst)).mul
    ((measurable_rootDegree W).comp measurable_snd)

lemma rootEdgeIntegrand_nonneg (q : Ω × Ω) :
    0 ≤ W q.1 q.2 * rootDegree W m q.1 * rootDegree W m q.2 :=
  mul_nonneg (mul_nonneg (W.nonneg _ _) (rootDegree_nonneg W _))
    (rootDegree_nonneg W _)

lemma integrable_rootEdgeIntegrand : Integrable
    (fun q : Ω × Ω ↦ W q.1 q.2 * rootDegree W m q.1 * rootDegree W m q.2)
    (μ.prod μ) := by
  refine integrable_prod_of_bdd (measurable_rootEdgeIntegrand W) (C := 1)
    fun q ↦ ?_
  rw [abs_of_nonneg (rootEdgeIntegrand_nonneg W q)]
  exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (rootDegree_nonneg W _)
    (rootDegree_le_one W _)) (rootDegree_nonneg W _) (rootDegree_le_one W _)

lemma rootEdge_nonneg : 0 ≤ rootEdge W m :=
  integral_nonneg fun q ↦ rootEdgeIntegrand_nonneg W q

/-- The `ℝ≥0∞` form of `N`. -/
lemma lintegral_rootEdge :
    (∫⁻ q, edgeE W q * rootE W m q.1 * rootE W m q.2 ∂(μ.prod μ)) =
      ENNReal.ofReal (rootEdge W m) := by
  have hcongr : ∀ q : Ω × Ω, edgeE W q * rootE W m q.1 * rootE W m q.2 =
      ENNReal.ofReal (W q.1 q.2 * rootDegree W m q.1 * rootDegree W m q.2) := by
    intro q
    rw [edgeE, rootE, rootE, ← ENNReal.ofReal_mul (W.nonneg _ _),
      ← ENNReal.ofReal_mul
        (mul_nonneg (W.nonneg _ _) (rootDegree_nonneg W _))]
  rw [lintegral_congr hcongr, rootEdge]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_rootEdgeIntegrand W)
    (ae_of_all _ fun q ↦ rootEdgeIntegrand_nonneg W q)).symm

/-- **`N = M²·s`**: the fractionally weighted edge integral is the biased edge
density, rescaled. -/
theorem rootEdge_eq (hM : 0 < rootMean W m)
    [IsProbabilityMeasure (rootMeasure W m)] :
    rootEdge W m = rootMean W m ^ 2 * cliqueDensity 2 (rootGraphon W m) := by
  have hkey := integral_rootDegree_prod 2 m (⊤ : SimpleGraph (Fin 2)) W hM
  have htop : ∀ y : Fin 2 → Ω,
      (∏ i, rootDegree W m (y i)) * graphWeight (⊤ : SimpleGraph (Fin 2)) W y =
        W (y 0) (y 1) * rootDegree W m (y 0) * rootDegree W m (y 1) := by
    intro y
    rw [graphWeight_top_fin_two, Fin.prod_univ_two]
    ring
  rw [integral_congr_ae (ae_of_all _ htop)] at hkey
  have hprod : (∫ y : Fin 2 → Ω,
      W (y 0) (y 1) * rootDegree W m (y 0) * rootDegree W m (y 1)
        ∂assignmentMeasure (Fin 2) μ) = rootEdge W m := by
    have hm : Measurable fun y : Fin 2 → Ω ↦
        W (y 0) (y 1) * rootDegree W m (y 0) * rootDegree W m (y 1) :=
      ((measurable_coord_pair W 0 1).mul
        ((measurable_rootDegree W).comp (measurable_pi_apply 0))).mul
        ((measurable_rootDegree W).comp (measurable_pi_apply 1))
    have hbd : ∀ y : Fin 2 → Ω,
        |W (y 0) (y 1) * rootDegree W m (y 0) * rootDegree W m (y 1)| ≤ 1 := by
      intro y
      have h0 : 0 ≤ W (y 0) (y 1) * rootDegree W m (y 0) * rootDegree W m (y 1) :=
        mul_nonneg (mul_nonneg (W.nonneg _ _) (rootDegree_nonneg W _))
          (rootDegree_nonneg W _)
      rw [abs_of_nonneg h0]
      exact mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (rootDegree_nonneg W _)
        (rootDegree_le_one W _)) (rootDegree_nonneg W _) (rootDegree_le_one W _)
    rw [integral_assignment_fin_two
      (g := fun a0 a1 ↦ W a0 a1 * rootDegree W m a0 * rootDegree W m a1) hm hbd,
      rootEdge]
    have hint : Integrable
        (fun q : Ω × Ω ↦ W q.1 q.2 * rootDegree W m q.1 * rootDegree W m q.2)
        (μ.prod μ) := integrable_rootEdgeIntegrand W
    rw [← integral_integral
      (f := fun a b ↦ W a b * rootDegree W m a * rootDegree W m b) hint]
  rw [hprod] at hkey
  have hc : cliqueDensity 2 (rootGraphon W m) =
      homDensity (⊤ : SimpleGraph (Fin 2)) (rootGraphon W m) := rfl
  rw [hkey, hc]

end RootEdge

/-! ### Three-factor Hölder at `(5/7, 1/7, 1/7)` -/

/-- **The fractionally degree-weighted edge bound**, `p^{m+2} ≤ N^m`.

This is `notes/odd_cycle_one_leaf.tex` Lemma 2.1 and
`notes/bowtie_outer_leaves.tex` Lemma 2.1, both at `β = 1/m`.  The notes state
it as `N ≥ p^{1+2/m}`; the polynomial form below is equivalent and keeps every
real power out of the statement. -/
theorem pow_le_pow_rootEdge (W : Graphon Ω μ) {m : ℕ} (hm : m ≠ 0) :
    cliqueDensity 2 W ^ (m + 2) ≤ rootEdge W m ^ m := by
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  have hN0 : 0 ≤ rootEdge W m := rootEdge_nonneg W
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  set g₀ : (Ω × Ω) → ℝ≥0∞ :=
    fun q ↦ edgeE W q * rootE W m q.1 * rootE W m q.2 with hg₀
  set g₁ : (Ω × Ω) → ℝ≥0∞ := fun q ↦ edgeE W q / degE W q.1 with hg₁
  set g₂ : (Ω × Ω) → ℝ≥0∞ := fun q ↦ edgeE W q / degE W q.2 with hg₂
  set f : Fin 3 → (Ω × Ω) → ℝ≥0∞ :=
    fun i ↦ if i = 0 then g₀ else if i = 1 then g₁ else g₂ with hfdef
  set e : Fin 3 → ℝ :=
    fun i ↦ if i = 0 then (m : ℝ) / ((m : ℝ) + 2) else 1 / ((m : ℝ) + 2) with hedef
  have hf0 : f 0 = g₀ := rfl
  have hf1 : f 1 = g₁ := rfl
  have hf2 : f 2 = g₂ := rfl
  have he0 : e 0 = (m : ℝ) / ((m : ℝ) + 2) := rfl
  have he1 : e 1 = 1 / ((m : ℝ) + 2) := rfl
  have he2 : e 2 = 1 / ((m : ℝ) + 2) := rfl
  have hm₀ : AEMeasurable g₀ (μ.prod μ) :=
    (((measurable_edgeE W).mul ((measurable_rootE W).comp measurable_fst)).mul
      ((measurable_rootE W).comp measurable_snd)).aemeasurable
  have hm₁ : AEMeasurable g₁ (μ.prod μ) :=
    ((measurable_edgeE W).div
      ((measurable_degE W).comp measurable_fst)).aemeasurable
  have hm₂ : AEMeasurable g₂ (μ.prod μ) :=
    ((measurable_edgeE W).div
      ((measurable_degE W).comp measurable_snd)).aemeasurable
  have hmeas : ∀ i ∈ (univ : Finset (Fin 3)), AEMeasurable (f i) (μ.prod μ) := by
    intro i _
    rw [hfdef]
    dsimp only
    split_ifs <;> assumption
  have hsum : ∑ i ∈ (univ : Finset (Fin 3)), e i = 1 := by
    rw [Fin.sum_univ_three, he0, he1, he2]
    field_simp
    ring
  have hnn : ∀ i ∈ (univ : Finset (Fin 3)), 0 ≤ e i := by
    intro i _
    rw [hedef]
    dsimp only
    split_ifs
    · positivity
    · positivity
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := μ.prod μ)
    (univ : Finset (Fin 3)) hmeas (p := e) hsum hnn
  -- the left side is the edge density
  have hpt : ∀ᵐ q ∂(μ.prod μ), ∏ i : Fin 3, f i q ^ e i = edgeE W q := by
    filter_upwards [ae_degE_ne_zero W, ae_degE_ne_zero_snd W] with q h1 h2
    rw [Fin.prod_univ_three, hf0, hf1, hf2, he0, he1, he2]
    simp only [hg₀, hg₁, hg₂]
    rcases eq_or_ne (edgeE W q) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul, ENNReal.zero_div, ENNReal.zero_div,
        ENNReal.zero_rpow_of_pos
          (by positivity : (0 : ℝ) < (m : ℝ) / ((m : ℝ) + 2)),
        zero_mul, zero_mul]
    · have hb : degE W q.1 ≠ 0 := h1 h0
      have hc : degE W q.2 ≠ 0 := h2 h0
      have hbt : degE W q.1 ≠ ⊤ := ENNReal.ofReal_ne_top
      have hct : degE W q.2 ≠ ⊤ := ENNReal.ofReal_ne_top
      -- rewrite the leading factor as a seventh root of a fifth power
      have hsplit : (edgeE W q * rootE W m q.1 * rootE W m q.2) ^
            ((m : ℝ) / ((m : ℝ) + 2)) =
          ((edgeE W q * rootE W m q.1 * rootE W m q.2) ^ m) ^
            (1 / ((m : ℝ) + 2)) := by
        rw [← ENNReal.rpow_natCast (edgeE W q * rootE W m q.1 * rootE W m q.2) m,
          ← ENNReal.rpow_mul]
        congr 1
        field_simp
      rw [hsplit,
        ← ENNReal.mul_rpow_of_nonneg _ _
          (by positivity : (0 : ℝ) ≤ 1 / ((m : ℝ) + 2)),
        ← ENNReal.mul_rpow_of_nonneg _ _
          (by positivity : (0 : ℝ) ≤ 1 / ((m : ℝ) + 2))]
      have hfifth : (edgeE W q * rootE W m q.1 * rootE W m q.2) ^ m =
          edgeE W q ^ m * degE W q.1 * degE W q.2 := by
        rw [mul_pow, mul_pow, pow_rootE W hm, pow_rootE W hm]
      rw [hfifth]
      have hprod : edgeE W q ^ m * degE W q.1 * degE W q.2 *
          (edgeE W q / degE W q.1) * (edgeE W q / degE W q.2) =
            edgeE W q ^ (m + 2) := by
        simp only [div_eq_mul_inv]
        have hre : edgeE W q ^ m * degE W q.1 * degE W q.2 *
            (edgeE W q * (degE W q.1)⁻¹) * (edgeE W q * (degE W q.2)⁻¹) =
              edgeE W q ^ (m + 2) * (degE W q.1 * (degE W q.1)⁻¹) *
                (degE W q.2 * (degE W q.2)⁻¹) := by ring
        rw [hre, ENNReal.mul_inv_cancel hb hbt, ENNReal.mul_inv_cancel hc hct,
          mul_one, mul_one]
      rw [hprod, ← ENNReal.rpow_natCast (edgeE W q) (m + 2), ← ENNReal.rpow_mul]
      rw [show ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 by push_cast; ring]
      rw [mul_one_div, div_self (ne_of_gt hm2), ENNReal.rpow_one]
  have hLHS : (∫⁻ q, ∏ i : Fin 3, f i q ^ e i ∂(μ.prod μ)) =
      ENNReal.ofReal (cliqueDensity 2 W) := by
    rw [lintegral_congr_ae hpt, lintegral_edgeE]
  -- the two quotient factors are at most one
  have hone₁ : (∫⁻ q, f 1 q ∂(μ.prod μ)) ^ (1 / ((m : ℝ) + 2)) ≤ 1 := by
    rw [hf1, hg₁]
    calc (∫⁻ q, edgeE W q / degE W q.1 ∂(μ.prod μ)) ^ (1 / ((m : ℝ) + 2))
        ≤ (1 : ℝ≥0∞) ^ (1 / ((m : ℝ) + 2)) :=
          ENNReal.rpow_le_rpow (lintegral_edgeE_div_fst W) (by positivity)
      _ = 1 := ENNReal.one_rpow _
  have hone₂ : (∫⁻ q, f 2 q ∂(μ.prod μ)) ^ (1 / ((m : ℝ) + 2)) ≤ 1 := by
    rw [hf2, hg₂]
    calc (∫⁻ q, edgeE W q / degE W q.2 ∂(μ.prod μ)) ^ (1 / ((m : ℝ) + 2))
        ≤ (1 : ℝ≥0∞) ^ (1 / ((m : ℝ) + 2)) :=
          ENNReal.rpow_le_rpow (lintegral_edgeE_div_snd W) (by positivity)
      _ = 1 := ENNReal.one_rpow _
  have hRHS : (∏ i : Fin 3, (∫⁻ q, f i q ∂(μ.prod μ)) ^ e i) ≤
      (ENNReal.ofReal (rootEdge W m)) ^ ((m : ℝ) / ((m : ℝ) + 2)) := by
    rw [Fin.prod_univ_three, he0, he1, he2]
    calc (∫⁻ q, f 0 q ∂(μ.prod μ)) ^ ((m : ℝ) / ((m : ℝ) + 2)) *
          (∫⁻ q, f 1 q ∂(μ.prod μ)) ^ (1 / ((m : ℝ) + 2)) *
          (∫⁻ q, f 2 q ∂(μ.prod μ)) ^ (1 / ((m : ℝ) + 2))
        ≤ (∫⁻ q, f 0 q ∂(μ.prod μ)) ^ ((m : ℝ) / ((m : ℝ) + 2)) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl hone₁) hone₂
      _ = (∫⁻ q, f 0 q ∂(μ.prod μ)) ^ ((m : ℝ) / ((m : ℝ) + 2)) := by
          rw [mul_one, mul_one]
      _ = _ := by rw [hf0, hg₀, lintegral_rootEdge]
  have hkey : ENNReal.ofReal (cliqueDensity 2 W) ≤
      (ENNReal.ofReal (rootEdge W m)) ^ ((m : ℝ) / ((m : ℝ) + 2)) := by
    rw [← hLHS]
    exact le_trans hholder hRHS
  -- raise to the `(m+2)`-nd power
  have hbig : ENNReal.ofReal (cliqueDensity 2 W) ^ ((m : ℝ) + 2) ≤
      ENNReal.ofReal (rootEdge W m) ^ (m : ℝ) := by
    calc ENNReal.ofReal (cliqueDensity 2 W) ^ ((m : ℝ) + 2)
        ≤ ((ENNReal.ofReal (rootEdge W m)) ^ ((m : ℝ) / ((m : ℝ) + 2))) ^
            ((m : ℝ) + 2) := ENNReal.rpow_le_rpow hkey (by positivity)
      _ = _ := by
          rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ (ne_of_gt hm2)]
  have hnat : ENNReal.ofReal (cliqueDensity 2 W ^ (m + 2)) ≤
      ENNReal.ofReal (rootEdge W m ^ m) := by
    rw [ENNReal.ofReal_pow hp0, ENNReal.ofReal_pow hN0]
    have h7 : ENNReal.ofReal (cliqueDensity 2 W) ^ (m + 2) =
        ENNReal.ofReal (cliqueDensity 2 W) ^ ((m : ℝ) + 2) := by
      rw [← ENNReal.rpow_natCast (ENNReal.ofReal (cliqueDensity 2 W)) (m + 2)]
      congr 1
      push_cast
      ring
    have h5 : ENNReal.ofReal (rootEdge W m) ^ m =
        ENNReal.ofReal (rootEdge W m) ^ (m : ℝ) :=
      (ENNReal.rpow_natCast (ENNReal.ofReal (rootEdge W m)) m).symm
    rw [h7, h5]
    exact hbig
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hnat

/-- The `m = 5` instance, used by Atlas 104. -/
theorem pow_seven_le_pow_rootEdge (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 7 ≤ rootEdge W 5 ^ 5 :=
  pow_le_pow_rootEdge W (by norm_num)

/-- The `m = 6` instance, used by Atlas 119. -/
theorem pow_eight_le_pow_rootEdge (W : Graphon Ω μ) :
    cliqueDensity 2 W ^ 8 ≤ rootEdge W 6 ^ 6 :=
  pow_le_pow_rootEdge W (by norm_num)

end Taeyoung.Methods.OddLeaf
