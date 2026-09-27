import EvenCycleApex.Equality.CZero

/-!
# Equality

Blueprint `thm:graphon-main` (explicit one- and two-apex bounds on graphons),
`lem:even-cycle-equality` and `cor:main-equality`, i.e. **headline H2**
`commonality_equality_iff_constant`.  Route of DEVIATIONS X4: finite-host inequalities are
transferred to graphons as inequalities between `L¹`-continuous functionals
(`le_of_hosts_cont`); strictness comes from `c = t(C₄, U)`:

* `R_n = 1` forces `m = 0` (`R_n ≥ 1 + C(n,2)m²`), then `t(C_n, S_±) = 1`, then `R₄ ≤ 1`
  (`R_four_le_fourthBound`), so `c ≤ R₄ − 1 = 0`, and `W = 1/2` a.e. by `lem:c-zero`;
* for `k = 1, 2` the bounds `A_{n/2,1} ≥ (X²/(1+b))^{n/4}` with `X ≥ 1 + 2b + c/3`, and
  `A_{n/2,2} ≥ Θ(b,c)^{n/4}`, are `> 1` as soon as `c > 0`;
* for `k ≥ 3`, `A_{n/2,k} ≥ R_n ≥ 1`.

Conversely, if `W = 1/2` a.e. every edge contributes `1/2` (`homDensity_congr_ae`).
-/

open MeasureTheory Filter

set_option linter.unusedSectionVars false

namespace EvenCycleApex

open Foundation SimpleGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Densities of an almost-everywhere constant graphon -/

/-- Densities only depend on the kernel up to `μ ⊗ μ`-null sets. -/
theorem homDensity_congr_ae {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {L L' : Ω → Ω → ℝ} (h : (fun p : Ω × Ω => L p.1 p.2) =ᵐ[μ.prod μ] fun p => L' p.1 p.2) :
    homDensity F L μ = homDensity F L' μ := by
  rw [homDensity_eq_integral_edgeProd, homDensity_eq_integral_edgeProd]
  refine integral_congr_ae ?_
  have hedge : ∀ p ∈ edgePairs F, ∀ᵐ x ∂(Measure.pi fun _ : Fin v => μ),
      L (x p.1) (x p.2) = L' (x p.1) (x p.2) := fun p hp => by
    have hne : p.1 ≠ p.2 := (mem_edgePairs.mp hp).1.ne
    exact (pairMarginal_measurePreserving (μ := μ) hne).quasiMeasurePreserving.ae h
  have hall := (Finset.eventually_all (edgePairs F)).2 hedge
  filter_upwards [hall] with x hx
  exact Finset.prod_congr rfl fun p hp => hx p hp

lemma homDensity_const {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] (c : ℝ) :
    homDensity F (fun _ _ => c) μ = c ^ (edgePairs F).card := by
  rw [homDensity_eq_integral_edgeProd]
  simp [edgeProd, Finset.prod_const]

/-- `M(F, W) = 2^{1 − |E(F)|}` when `W = 1/2` almost everywhere. -/
theorem commonalityM_of_half {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {W : Ω → Ω → ℝ} (h : (fun p : Ω × Ω => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => (1 / 2 : ℝ)) :
    homDensity F W μ + homDensity F (cmpl W) μ = 2 / 2 ^ (edgePairs F).card := by
  have h1 : homDensity F W μ = homDensity F (fun _ _ => (1 / 2 : ℝ)) μ := homDensity_congr_ae F h
  have h2 : homDensity F (cmpl W) μ = homDensity F (fun _ _ => (1 / 2 : ℝ)) μ :=
    homDensity_congr_ae F (by
      filter_upwards [h] with p hp
      simp only [cmpl] at hp ⊢
      linarith)
  rw [h1, h2, homDensity_const, ← two_mul, div_pow, one_pow, mul_one_div]

/-! ### Graphon forms of the finite bounds -/

lemma continuous_fourthBound (n : ℕ) (hn : 4 < n) :
    Continuous fun p : ℝ × ℝ => FiniteKernel.fourthBound n p.1 p.2 := by
  have hn4 : (4 : ℝ) < n := by exact_mod_cast hn
  unfold FiniteKernel.fourthBound
  have h1 : Continuous fun t : ℝ => t ^ ((4 : ℝ) / n) := Real.continuous_rpow_const (by positivity)
  have h2 : Continuous fun t : ℝ => t ^ (2 / ((n : ℝ) - 2)) :=
    Real.continuous_rpow_const (div_nonneg (by norm_num) (by linarith))
  exact (h1.comp continuous_fst).add (continuous_const.mul
    (h2.comp ((continuous_fst.sub (continuous_snd.pow n)).max continuous_const)))

section Bounds

variable {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
include hW

lemma graphonB_nonneg : 0 ≤ graphonB μ W :=
  le_of_hosts_cont hW (L1ContAt.const 0 W) (graphonB_cont hW) fun hσ M hsym h0 h1 V hV => by
    rw [(graphonScalars_step hσ M hsym h0 h1 hV).2.1]
    exact FiniteKernel.b_nonneg _

lemma graphonC_nonneg : 0 ≤ graphonC μ W :=
  le_of_hosts_cont hW (L1ContAt.const 0 W) (graphonC_cont hW) fun hσ M hsym h0 h1 V hV => by
    rw [(graphonScalars_step hσ M hsym h0 h1 hV).2.2.1]
    exact FiniteKernel.c_nonneg _

/-- `X ≥ 1 + 2b + c/3` (`lem:diamond`, graphon form). -/
lemma graphonX_ge : 1 + 2 * graphonB μ W + graphonC μ W / 3 ≤ graphonX μ W := by
  refine le_of_hosts_cont hW
    (((graphonB_cont hW).prod (graphonC_cont hW)).comp
      (φ := fun p : ℝ × ℝ => 1 + 2 * p.1 + p.2 / 3) (by fun_prop))
    (graphonX_cont hW) fun hσ M hsym h0 h1 V hV => ?_
  obtain ⟨-, hb, hc, -, hX⟩ := graphonScalars_step (μ := μ) hσ M hsym h0 h1 hV
  try simp only
  rw [hb, hc, hX]
  exact (FiniteKernel.diamond_lower_bound _).2.2.2

/-- `1 + c ≤ R₄` on graphons. -/
lemma one_add_graphonC_le : 1 + graphonC μ W ≤ normalizedCycleDensity W μ 4 := by
  refine le_of_hosts_cont hW (((graphonC_cont hW)).comp (φ := fun c : ℝ => 1 + c) (by fun_prop))
    (normalizedCycleDensity_cont (by norm_num) hW) fun hσ M hsym h0 h1 V hV => ?_
  try simp only
  rw [(graphonScalars_step (μ := μ) hσ M hsym h0 h1 hV).2.2.1,
    normalizedCycleDensity_step hσ M hsym h0 h1 hV (by norm_num), FiniteKernel.R_four]
  linarith [FiniteKernel.a_nonneg (hostOfStep (μ := μ) hσ M hsym h0 h1),
    FiniteKernel.b_nonneg (hostOfStep (μ := μ) hσ M hsym h0 h1)]

/-- `R_n ≥ 1 + C(n,2) m²` on graphons. -/
lemma cycle_ge_mean {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    1 + (n.choose 2 : ℝ) * graphonM μ W ^ 2 ≤ normalizedCycleDensity W μ n := by
  refine le_of_hosts_cont hW
    ((graphonM_cont hW).comp (φ := fun m : ℝ => 1 + (n.choose 2 : ℝ) * m ^ 2) (by fun_prop))
    (normalizedCycleDensity_cont (by omega) hW) fun hσ M hsym h0 h1 V hV => ?_
  try simp only
  rw [(graphonScalars_step (μ := μ) hσ M hsym h0 h1 hV).1,
    normalizedCycleDensity_step hσ M hsym h0 h1 hV (by omega)]
  obtain ⟨ha, hb, -⟩ := FiniteKernel.even_cycle_lower_bound (hostOfStep (μ := μ) hσ M hsym h0 h1) hn h4
  linarith

/-- `t(C_n, S_σ) ≥ (1 + σm)ⁿ` on graphons. -/
lemma colour_cycle_ge_graphon {n : ℕ} (hn : Even n) (h3 : 3 ≤ n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    (1 + σ * graphonM μ W) ^ n ≤ colourDensity (cycleGraph n) σ μ W := by
  refine le_of_hosts_cont hW
    ((graphonM_cont hW).comp (φ := fun m : ℝ => (1 + σ * m) ^ n) (by fun_prop))
    (colourDensity_cont _ hσ hW) fun hσ' M hsym h0 h1 V hV => ?_
  try simp only
  rw [(graphonScalars_step (μ := μ) hσ' M hsym h0 h1 hV).1, colourDensity_step _ σ hσ' M hsym h0 h1 hV]
  exact FiniteKernel.colour_cycle_ge _ hn h3 σ

/-- `R₄ ≤ ½ ∑_σ fourthBound(t(C_n, S_σ), 1 + σm)` on graphons (DEVIATIONS X4). -/
lemma R_four_le_graphon {n : ℕ} (hn : Even n) (h5 : 4 < n) :
    normalizedCycleDensity W μ 4 ≤
      (FiniteKernel.fourthBound n (colourDensity (cycleGraph n) 1 μ W) (1 + 1 * graphonM μ W)
        + FiniteKernel.fourthBound n (colourDensity (cycleGraph n) (-1) μ W)
            (1 + -1 * graphonM μ W)) / 2 := by
  have hc := continuous_fourthBound n h5
  refine le_of_hosts_cont hW (normalizedCycleDensity_cont (by norm_num) hW)
    ((((colourDensity_cont (cycleGraph n) (Or.inl rfl) hW).prod
      ((colourDensity_cont (cycleGraph n) (Or.inr rfl) hW).prod (graphonM_cont hW))).comp
      (φ := fun p : ℝ × ℝ × ℝ => (FiniteKernel.fourthBound n p.1 (1 + 1 * p.2.2)
        + FiniteKernel.fourthBound n p.2.1 (1 + -1 * p.2.2)) / 2)
      (Continuous.continuousAt (by
        have ha : Continuous fun p : ℝ × ℝ × ℝ => FiniteKernel.fourthBound n p.1 (1 + 1 * p.2.2) :=
          hc.comp (continuous_fst.prodMk (continuous_const.add
            (continuous_const.mul (continuous_snd.comp continuous_snd))))
        have hb : Continuous fun p : ℝ × ℝ × ℝ =>
            FiniteKernel.fourthBound n p.2.1 (1 + -1 * p.2.2) :=
          hc.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_const.add
            (continuous_const.mul (continuous_snd.comp continuous_snd))))
        exact (ha.add hb).div_const 2)))) fun hσ M hsym h0 h1 V hV => ?_
  try simp only
  rw [normalizedCycleDensity_step hσ M hsym h0 h1 hV (by norm_num),
    colourDensity_step _ 1 hσ M hsym h0 h1 hV, colourDensity_step _ (-1) hσ M hsym h0 h1 hV,
    (graphonScalars_step (μ := μ) hσ M hsym h0 h1 hV).1]
  exact FiniteKernel.R_four_le_fourthBound _ hn h5

/-- **`thm:graphon-main`, one apex.**  `A_{n/2,1} ≥ (X²/(1+b))^{n/4}`. -/
theorem one_apex_graphon_bound {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    (graphonX μ W ^ 2 / (1 + graphonB μ W)) ^ ((n : ℝ) / 4) ≤ normalizedApexDensity W μ n 1 := by
  have hb := graphonB_nonneg hW
  refine le_of_hosts_cont hW
    (((graphonX_cont hW).prod (graphonB_cont hW)).comp
      (φ := fun p : ℝ × ℝ => (p.1 ^ 2 / (1 + p.2)) ^ ((n : ℝ) / 4))
      (ContinuousAt.rpow_const ((continuousAt_fst.pow 2).div (continuousAt_const.add continuousAt_snd)
        (by simp only; linarith)) (Or.inr (by positivity))))
    (normalizedApexDensity_cont (by omega) hW) fun hσ M hsym h0 h1 V hV => ?_
  try simp only
  obtain ⟨-, hbV, -, -, hXV⟩ := graphonScalars_step (μ := μ) hσ M hsym h0 h1 hV
  rw [hbV, hXV, normalizedApexDensity_step hσ M hsym h0 h1 hV (by omega)]
  exact (FiniteKernel.one_apex_bound _ hn h4).1

/-- **`thm:graphon-main`, two apices** (plan D10).  `A_{n/2,2} ≥ Θ(b, c)^{n/4}`. -/
theorem two_apex_graphon_bound {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    twoApexTheta (graphonB μ W) (graphonC μ W) ^ ((n : ℝ) / 4) ≤ normalizedApexDensity W μ n 2 := by
  have hb := graphonB_nonneg hW
  have hc := graphonC_nonneg hW
  refine le_of_hosts_cont hW
    (((graphonB_cont hW).prod (graphonC_cont hW)).comp
      (φ := fun p : ℝ × ℝ => twoApexTheta p.1 p.2 ^ ((n : ℝ) / 4))
      (ContinuousAt.rpow_const (by
        unfold twoApexTheta
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
        simp only
        positivity) (Or.inr (by positivity))))
    (normalizedApexDensity_cont (by omega) hW) fun hσ M hsym h0 h1 V hV => ?_
  try simp only
  obtain ⟨-, hbV, hcV, -, -⟩ := graphonScalars_step (μ := μ) hσ M hsym h0 h1 hV
  rw [hbV, hcV, normalizedApexDensity_step hσ M hsym h0 h1 hV (by omega)]
  exact (FiniteKernel.two_apex_bound _ hn h4).1

end Bounds

/-- **`thm:graphon-main`.**  For every graphon and every even `n ≥ 4`:
`A_{n/2,1} ≥ (X²/(1+b))^{n/4} ≥ 1`, `A_{n/2,2} ≥ Θ(b,c)^{n/4} ≥ 1` (plan D10), and
`A_{n/2,k} ≥ R_n ≥ 1` for `k ≥ 3`. -/
theorem all_even_graphon_apex_bounds {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {n : ℕ} (hn : Even n)
    (h4 : 4 ≤ n) :
    ((graphonX μ W ^ 2 / (1 + graphonB μ W)) ^ ((n : ℝ) / 4) ≤ normalizedApexDensity W μ n 1 ∧
        1 ≤ (graphonX μ W ^ 2 / (1 + graphonB μ W)) ^ ((n : ℝ) / 4)) ∧
      (twoApexTheta (graphonB μ W) (graphonC μ W) ^ ((n : ℝ) / 4) ≤ normalizedApexDensity W μ n 2 ∧
        1 ≤ twoApexTheta (graphonB μ W) (graphonC μ W) ^ ((n : ℝ) / 4)) ∧
      (∀ k, 3 ≤ k → normalizedCycleDensity W μ n ≤ normalizedApexDensity W μ n k) ∧
      1 ≤ normalizedCycleDensity W μ n := by
  have hb := graphonB_nonneg hW
  have hc := graphonC_nonneg hW
  have hX := graphonX_ge hW
  have hexp : (0 : ℝ) ≤ (n : ℝ) / 4 := by positivity
  refine ⟨⟨one_apex_graphon_bound hW hn h4, Real.one_le_rpow ?_ hexp⟩,
    ⟨two_apex_graphon_bound hW hn h4, Real.one_le_rpow (one_le_twoApexTheta hb hc) hexp⟩,
    fun k hk => normalizedCycleDensity_le_apex_of_hosts (by omega)
      (fun d K => K.apex_relative_host hn h4 hk) hW,
    one_le_normalizedCycleDensity hn h4 hW⟩
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-! ### `lem:even-cycle-equality` -/

/-- **`lem:even-cycle-equality`.**  For every graphon and even `n ≥ 4`, `R_n = 1` if and only if
`W = 1/2` almost everywhere. -/
theorem even_cycle_equality_iff_constant {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {n : ℕ}
    (hn : Even n) (h4 : 4 ≤ n) :
    normalizedCycleDensity W μ n = 1 ↔
      (fun p : Ω × Ω => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => (1 / 2 : ℝ) := by
  constructor
  · intro hR
    -- `m = 0`
    have hm0 : graphonM μ W = 0 := by
      have h := cycle_ge_mean hW hn h4
      have hC : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos (by omega)
      rw [hR] at h
      have : graphonM μ W ^ 2 ≤ 0 := by nlinarith [sq_nonneg (graphonM μ W)]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
    -- both colour cycle densities equal one
    have hmean : normalizedCycleDensity W μ n
        = (colourDensity (cycleGraph n) 1 μ W + colourDensity (cycleGraph n) (-1) μ W) / 2 :=
      normalizedCycleDensity_eq_colour_mean W μ (by omega)
    have hp := colour_cycle_ge_graphon hW hn (by omega) (σ := 1) (Or.inl rfl)
    have hq := colour_cycle_ge_graphon hW hn (by omega) (σ := -1) (Or.inr rfl)
    rw [hm0, mul_zero, add_zero, one_pow] at hp hq
    have ht1 : colourDensity (cycleGraph n) 1 μ W = 1 := by linarith
    have ht2 : colourDensity (cycleGraph n) (-1) μ W = 1 := by linarith
    -- `R₄ = 1`
    have hR4 : normalizedCycleDensity W μ 4 = 1 := by
      rcases (by omega : n = 4 ∨ 4 < n) with rfl | h5
      · exact hR
      · have hle := R_four_le_graphon hW hn h5
        rw [ht1, ht2, hm0] at hle
        have hΦ : FiniteKernel.fourthBound n 1 (1 + 1 * 0) = 1 := by
          have hβ : (0 : ℝ) < 2 / ((n : ℝ) - 2) := div_pos (by norm_num) (by
            have : (4 : ℝ) < n := by exact_mod_cast h5
            linarith)
          simp [FiniteKernel.fourthBound, Real.zero_rpow hβ.ne']
        have hΦ' : FiniteKernel.fourthBound n 1 (1 + -1 * 0) = 1 := by simpa using hΦ
        rw [hΦ, hΦ'] at hle
        have := one_le_normalizedCycleDensity (by decide : Even 4) le_rfl hW
        linarith
    -- `c = 0`
    have hc0 : graphonC μ W = 0 := by
      have h1 := one_add_graphonC_le hW
      have h2 := graphonC_nonneg hW
      linarith
    exact graphon_half_of_graphonC_zero hW hc0
  · intro h
    rw [normalizedCycleDensity, commonalityM, commonalityM_of_half _ h,
      cycleGraph_card_edgePairs (by omega)]
    field_simp

/-! ### Headline H2 -/

/-- **Headline H2** (`cor:main-equality`).  For every graphon on every probability space, every
even `n ≥ 4` and every `k ≥ 1`: `M(C_n^{+k}, W) = 2^{1 − n(k+1)}` if and only if `W = 1/2`
almost everywhere. -/
theorem commonality_equality_iff_constant {W : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    {n k : ℕ} (hn : Even n) (hn4 : 4 ≤ n) (hk : 1 ≤ k) :
    homDensity (apexCycle n k) W μ + homDensity (apexCycle n k) (cmpl W) μ = 2 / 2 ^ (n * (k + 1))
      ↔ (fun p : Ω × Ω => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => (1 / 2 : ℝ) := by
  constructor
  · intro hM
    have hA : normalizedApexDensity W μ n k = 1 := by
      rw [normalizedApexDensity, commonalityM, hM]
      field_simp
    have hb := graphonB_nonneg hW
    have hc := graphonC_nonneg hW
    have hexp : (0 : ℝ) < (n : ℝ) / 4 := by positivity
    -- in every case, `c = 0`
    have hc0 : graphonC μ W = 0 := by
      rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | h3
      · have h1 := one_apex_graphon_bound hW hn hn4
        rw [hA] at h1
        have hX := graphonX_ge hW
        have hbase : graphonX μ W ^ 2 / (1 + graphonB μ W) ≤ 1 := by
          by_contra hgt
          have := Real.one_lt_rpow (not_le.mp hgt) hexp
          linarith
        rw [div_le_one (by linarith)] at hbase
        nlinarith
      · have h2 := two_apex_graphon_bound hW hn hn4
        rw [hA] at h2
        by_contra hne
        have hpos : 0 < graphonC μ W := lt_of_le_of_ne hc (Ne.symm hne)
        have := Real.one_lt_rpow (one_lt_twoApexTheta hb hpos) hexp
        linarith
      · have hR := normalizedCycleDensity_le_apex_of_hosts (μ := μ) (by omega)
          (fun d K => K.apex_relative_host hn hn4 h3) hW
        rw [hA] at hR
        have hR1 := one_le_normalizedCycleDensity hn hn4 hW
        have hRn : normalizedCycleDensity W μ n = 1 := le_antisymm hR hR1
        have hhalf := (even_cycle_equality_iff_constant hW hn hn4).mp hRn
        -- `c = 0` directly from `W = 1/2`
        have hcc : graphonC μ W = 0 := by
          rw [graphonC, signedDensity, homDensity_congr_ae (cycleGraph 4)
            (L' := fun _ _ => (0 : ℝ)) (by
              filter_upwards [hhalf] with p hp
              simp only [signedKernel] at hp ⊢
              rw [hp]
              norm_num), homDensity_const, cycleGraph_card_edgePairs (by norm_num)]
          norm_num
        exact hcc
    exact graphon_half_of_graphonC_zero hW hc0
  · intro h
    rw [commonalityM_of_half _ h, apexCycle_edgeCount (by omega)]

/-! ### `lem:integral-moments` and `lem:c-zero`, as stated -/

/-- `R₄ = 1 + 2m² + 4b + c` on every graphon (`lem:integral-moments`). -/
theorem R_four_graphon {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    normalizedCycleDensity W μ 4
      = 1 + 2 * graphonM μ W ^ 2 + 4 * graphonB μ W + graphonC μ W := by
  have hF : L1ContAt μ (fun V => 1 + 2 * graphonM μ V ^ 2 + 4 * graphonB μ V + graphonC μ V) W :=
    ((graphonM_cont hW).prod ((graphonB_cont hW).prod (graphonC_cont hW))).comp
      (φ := fun p : ℝ × ℝ × ℝ => 1 + 2 * p.1 ^ 2 + 4 * p.2.1 + p.2.2) (by fun_prop)
  have hG := normalizedCycleDensity_cont (μ := μ) (n := 4) (by norm_num) hW
  have key : ∀ {d : ℕ} {σ : Ω → Fin d} (hσ : Measurable σ) (M : Fin d → Fin d → ℝ)
      (hsym : ∀ i j, M i j = M j i) (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i j, M i j ≤ 1)
      (V : Ω → Ω → ℝ), (∀ x y, V x y = M (σ x) (σ y)) →
      normalizedCycleDensity V μ 4 = 1 + 2 * graphonM μ V ^ 2 + 4 * graphonB μ V + graphonC μ V := by
    intro d σ hσ M hsym h0 h1 V hV
    obtain ⟨hm, hb, hc, -, -⟩ := graphonScalars_step (μ := μ) hσ M hsym h0 h1 hV
    rw [normalizedCycleDensity_step hσ M hsym h0 h1 hV (by norm_num), FiniteKernel.R_four, hm, hb,
      hc, FiniteKernel.a]
  exact le_antisymm (le_of_hosts_cont hW hG hF fun hσ M hsym h0 h1 V hV =>
      (key hσ M hsym h0 h1 V hV).le)
    (le_of_hosts_cont hW hF hG fun hσ M hsym h0 h1 V hV => (key hσ M hsym h0 h1 V hV).ge)

/-- **`lem:c-zero`.**  `c = t(C₄, 2W − 1) = 0` if and only if `W = 1/2` almost everywhere. -/
theorem fourth_signed_cycle_zero_iff {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    graphonC μ W = 0 ↔ (fun p : Ω × Ω => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => (1 / 2 : ℝ) := by
  refine ⟨graphon_half_of_graphonC_zero hW, fun h => ?_⟩
  rw [graphonC, signedDensity, homDensity_congr_ae (cycleGraph 4) (L' := fun _ _ => (0 : ℝ)) (by
      filter_upwards [h] with p hp
      simp only [signedKernel] at hp ⊢
      rw [hp]
      norm_num), homDensity_const, cycleGraph_card_edgePairs (by norm_num)]
  norm_num

end EvenCycleApex
