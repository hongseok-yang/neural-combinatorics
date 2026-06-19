import OddCycleBound.Graphon

/-!
# Path densities and Lemma 2.4 (integral form) — Stage 3

Building on `Graphon.lean`, we define the path homomorphism densities `x_j = t(P_j, U)` as the
nested integral `xden j = mean (Tʲ 1)` and prove the **path-density formulae of Lemma 2.4**
(`x₂ = q² + s₀`, `x₃ = q³ + 2q s₀ + s₁`, `x₄ = q⁴ + 3q² s₀ + 2q s₁ + s₀² + s₂`) entirely from
the integral definitions, so Lemma 2.4 leaves the *trusted* list.

Engine: the key identity `T (hₖ) = sₖ·1 + h_{k+1}`, pointwise `T`-linearity, and the
decomposition `pathFun n = xₙ·1 + (mean-zero combination of the hₖ)`, from which `xₙ` is read
off by taking `mean` (the mean-zero part drops out).
-/

open MeasureTheory

namespace OddCycleBound.Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- The constant function `1` is `Good`. -/
lemma good_one : Good (fun _ : Ω => (1 : ℝ)) :=
  ⟨stronglyMeasurable_const, ⟨1, zero_le_one, fun _ => by norm_num⟩⟩

lemma good_smul (c : ℝ) {f : Ω → ℝ} (hf : Good f) : Good (c • f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.meas.const_smul c, ⟨|c| * C, mul_nonneg (abs_nonneg _) hC0, fun x => ?_⟩⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma good_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) : Good (f + g) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bdd
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bdd
  refine ⟨hf.meas.add hg.meas, ⟨Cf + Cg, by linarith, fun x => ?_⟩⟩
  rw [Pi.add_apply]
  exact (abs_add_le _ _).trans (by linarith [hCf x, hCg x])

/-- Integrability of `y ↦ U x y * f y` for `Good f`. -/
lemma integrable_Uf (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) (x : Ω) :
    Integrable (fun y => U x y * f y) μ := by
  have hmx : Measurable (fun y => U x y) := hU.meas.comp measurable_prodMk_left
  exact (Good.mul ⟨hmx.stronglyMeasurable, ⟨1, zero_le_one, fun y => by
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y⟩⟩ hf).integrable

lemma T_one (hU : IsGraphon U μ) : T U μ (fun _ => 1) = deg U μ := by
  funext x; simp [T, deg]

lemma deg_eq (x : Ω) : deg U μ x = qval U μ + gfun U μ x := by simp [gfun]

lemma hseq_zero : hseq U μ 0 = gfun U μ := rfl

lemma deg_eq' (x : Ω) : deg U μ x = qval U μ + hseq U μ 0 x := by rw [deg_eq, hseq_zero]

/-- Pointwise additivity of `T` on `Good` functions. -/
lemma T_add' (hU : IsGraphon U μ) {f g : Ω → ℝ} (hf : Good f) (hg : Good g) (x : Ω) :
    T U μ (f + g) x = T U μ f x + T U μ g x := by
  simp only [T, Pi.add_apply]
  rw [← integral_add (integrable_Uf hU hf x) (integrable_Uf hU hg x)]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- Pointwise homogeneity of `T`. -/
lemma T_smul' (c : ℝ) (f : Ω → ℝ) (x : Ω) : T U μ (c • f) x = c * T U μ f x := by
  simp only [T, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- `mean (T (hₖ)) = sₖ`. -/
lemma mean_T_hseq (hU : IsGraphon U μ) (k : ℕ) :
    mean μ (T U μ (hseq U μ k)) = smom U μ k := by
  have h1 : mean μ (T U μ (hseq U μ k)) = ∫ x, T U μ (hseq U μ k) x * 1 ∂μ := by simp [mean]
  rw [h1, T_symm hU (good_h hU k) good_one, T_one hU]
  have hcongr : ∀ x, hseq U μ k x * deg U μ x
      = qval U μ * hseq U μ k x + gfun U μ x * hseq U μ k x := fun x => by rw [deg_eq]; ring
  rw [integral_congr_ae (ae_of_all _ hcongr),
    integral_add ((good_h hU k).integrable.const_mul _) ((good_g hU).mul (good_h hU k)).integrable,
    integral_const_mul]
  have : ∫ x, hseq U μ k x ∂μ = 0 := mean_h hU k
  rw [this, mul_zero, zero_add]
  rfl

/-- **The key recursion** `T (hₖ) = sₖ·1 + h_{k+1}`. -/
lemma T_hseq (hU : IsGraphon U μ) (k : ℕ) :
    T U μ (hseq U μ k) = fun x => smom U μ k + hseq U μ (k + 1) x := by
  funext x
  have hdef : hseq U μ (k + 1) x = T U μ (hseq U μ k) x - mean μ (T U μ (hseq U μ k)) := by
    simp only [hseq, Aop]
  rw [mean_T_hseq hU k] at hdef
  linarith [hdef]

lemma T_hseq' (hU : IsGraphon U μ) (k : ℕ) (x : Ω) :
    T U μ (hseq U μ k) x = smom U μ k + hseq U μ (k + 1) x := congrFun (T_hseq hU k) x

/-- Path-density iterate `pathFun j = Tʲ 1`. -/
noncomputable def pathFun (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => fun _ => 1
  | (k + 1) => T U μ (pathFun U μ k)

/-- The path density `x_j = t(P_j, U) = mean (Tʲ 1)`. -/
noncomputable def xden (U : Ω → Ω → ℝ) (μ : Measure Ω) (j : ℕ) : ℝ := mean μ (pathFun U μ j)

/-! ### `mean` is linear; constants and `hₖ` evaluate cleanly. -/

lemma mean_one : mean μ (fun _ : Ω => (1:ℝ)) = 1 := mean_const 1

lemma mean_smul (c : ℝ) (f : Ω → ℝ) : mean μ (c • f) = c * mean μ f := by
  simp only [mean, Pi.smul_apply, smul_eq_mul]; rw [integral_const_mul]

lemma mean_add {f g : Ω → ℝ} (hf : Good f) (hg : Good g) :
    mean μ (f + g) = mean μ f + mean μ g := by
  simp only [mean, Pi.add_apply]; exact integral_add hf.integrable hg.integrable

lemma mean_hseq (hU : IsGraphon U μ) (k : ℕ) : mean μ (hseq U μ k) = 0 := mean_h hU k

/-- For a constant times `1` plus a mean-zero `Good` function, the mean is the constant. -/
lemma mean_const_add (C : ℝ) {w : Ω → ℝ} (hw : Good w) (hw0 : mean μ w = 0) :
    mean μ (C • (fun _ : Ω => (1:ℝ)) + w) = C := by
  rw [mean_add (good_smul C good_one) hw, mean_smul, mean_one, hw0]; ring

/-! ### Decompositions `pathFun k = xₖ·1 + (mean-zero combination of hₖ)` -/

lemma decomp1 (hU : IsGraphon U μ) :
    pathFun U μ 1 = qval U μ • (fun _ : Ω => (1:ℝ)) + hseq U μ 0 := by
  have h1 : pathFun U μ 1 = deg U μ := by
    show T U μ (fun _ => 1) = deg U μ; exact T_one hU
  rw [h1]; funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  exact deg_eq' x

lemma decomp2 (hU : IsGraphon U μ) :
    pathFun U μ 2 = (qval U μ ^ 2 + smom U μ 0) • (fun _ : Ω => (1:ℝ))
      + (qval U μ • hseq U μ 0 + hseq U μ 1) := by
  funext x
  show T U μ (pathFun U μ 1) x = _
  rw [decomp1 hU, T_add' hU (good_smul _ good_one) (good_h hU 0), T_smul', T_one hU, T_hseq' hU 0,
    deg_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma decomp3 (hU : IsGraphon U μ) :
    pathFun U μ 3 = (qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1) • (fun _ : Ω => (1:ℝ))
      + ((qval U μ ^ 2 + smom U μ 0) • hseq U μ 0 + (qval U μ • hseq U μ 1 + hseq U μ 2)) := by
  funext x
  show T U μ (pathFun U μ 2) x = _
  rw [decomp2 hU,
    T_add' hU (good_smul _ good_one) (good_add (good_smul _ (good_h hU 0)) (good_h hU 1)),
    T_smul', T_one hU,
    T_add' hU (good_smul _ (good_h hU 0)) (good_h hU 1), T_smul', T_hseq' hU 0, T_hseq' hU 1,
    deg_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma decomp4 (hU : IsGraphon U μ) :
    pathFun U μ 4 = (qval U μ ^ 4 + 3 * qval U μ ^ 2 * smom U μ 0 + 2 * qval U μ * smom U μ 1
        + smom U μ 0 ^ 2 + smom U μ 2) • (fun _ : Ω => (1:ℝ))
      + ((qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1) • hseq U μ 0
          + ((qval U μ ^ 2 + smom U μ 0) • hseq U μ 1 + (qval U μ • hseq U μ 2 + hseq U μ 3))) := by
  funext x
  show T U μ (pathFun U μ 3) x = _
  rw [decomp3 hU,
    T_add' hU (good_smul _ good_one)
      (good_add (good_smul _ (good_h hU 0)) (good_add (good_smul _ (good_h hU 1)) (good_h hU 2))),
    T_smul', T_one hU,
    T_add' hU (good_smul _ (good_h hU 0)) (good_add (good_smul _ (good_h hU 1)) (good_h hU 2)),
    T_smul',
    T_add' hU (good_smul _ (good_h hU 1)) (good_h hU 2), T_smul',
    T_hseq' hU 0, T_hseq' hU 1, T_hseq' hU 2, deg_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Lemma 2.4 for `x₂, x₃, x₄` (read off by taking `mean`) -/

lemma xden_two (hU : IsGraphon U μ) : xden U μ 2 = qval U μ ^ 2 + smom U μ 0 := by
  rw [xden, decomp2 hU]
  refine mean_const_add _ (good_add (good_smul _ (good_h hU 0)) (good_h hU 1)) ?_
  rw [mean_add (good_smul _ (good_h hU 0)) (good_h hU 1), mean_smul, mean_hseq hU, mean_hseq hU]
  ring

lemma xden_three (hU : IsGraphon U μ) :
    xden U μ 3 = qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1 := by
  rw [xden, decomp3 hU]
  refine mean_const_add _
    (good_add (good_smul _ (good_h hU 0)) (good_add (good_smul _ (good_h hU 1)) (good_h hU 2))) ?_
  rw [mean_add (good_smul _ (good_h hU 0)) (good_add (good_smul _ (good_h hU 1)) (good_h hU 2)),
    mean_add (good_smul _ (good_h hU 1)) (good_h hU 2),
    mean_smul, mean_smul, mean_hseq hU, mean_hseq hU, mean_hseq hU]
  ring

lemma xden_four (hU : IsGraphon U μ) :
    xden U μ 4 = qval U μ ^ 4 + 3 * qval U μ ^ 2 * smom U μ 0 + 2 * qval U μ * smom U μ 1
      + smom U μ 0 ^ 2 + smom U μ 2 := by
  rw [xden, decomp4 hU]
  refine mean_const_add _
    (good_add (good_smul _ (good_h hU 0))
      (good_add (good_smul _ (good_h hU 1)) (good_add (good_smul _ (good_h hU 2)) (good_h hU 3)))) ?_
  rw [mean_add (good_smul _ (good_h hU 0))
        (good_add (good_smul _ (good_h hU 1)) (good_add (good_smul _ (good_h hU 2)) (good_h hU 3))),
    mean_add (good_smul _ (good_h hU 1)) (good_add (good_smul _ (good_h hU 2)) (good_h hU 3)),
    mean_add (good_smul _ (good_h hU 2)) (good_h hU 3),
    mean_smul, mean_smul, mean_smul, mean_hseq hU, mean_hseq hU, mean_hseq hU, mean_hseq hU]
  ring

/-! ### `x₅, x₆` (needed for C₇) -/

/-- Abbreviation for the `Good`ness of the degree-`≤3` `hₖ`-combination in `decomp4`. -/
private lemma good_combo4 (hU : IsGraphon U μ) :
    Good ((qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1) • hseq U μ 0
      + ((qval U μ ^ 2 + smom U μ 0) • hseq U μ 1 + (qval U μ • hseq U μ 2 + hseq U μ 3))) :=
  good_add (good_smul _ (good_h hU 0))
    (good_add (good_smul _ (good_h hU 1)) (good_add (good_smul _ (good_h hU 2)) (good_h hU 3)))

lemma decomp5 (hU : IsGraphon U μ) :
    pathFun U μ 5 = (qval U μ ^ 5 + 4 * qval U μ ^ 3 * smom U μ 0 + 3 * qval U μ ^ 2 * smom U μ 1
        + 3 * qval U μ * smom U μ 0 ^ 2 + 2 * qval U μ * smom U μ 2 + 2 * smom U μ 0 * smom U μ 1
        + smom U μ 3) • (fun _ : Ω => (1:ℝ))
      + ((qval U μ ^ 4 + 3 * qval U μ ^ 2 * smom U μ 0 + 2 * qval U μ * smom U μ 1
            + smom U μ 0 ^ 2 + smom U μ 2) • hseq U μ 0
        + ((qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1) • hseq U μ 1
          + ((qval U μ ^ 2 + smom U μ 0) • hseq U μ 2 + (qval U μ • hseq U μ 3 + hseq U μ 4)))) := by
  funext x
  show T U μ (pathFun U μ 4) x = _
  rw [decomp4 hU,
    T_add' hU (good_smul _ good_one) (good_combo4 hU), T_smul', T_one hU,
    T_add' hU (good_smul _ (good_h hU 0))
      (good_add (good_smul _ (good_h hU 1)) (good_add (good_smul _ (good_h hU 2)) (good_h hU 3))),
    T_smul',
    T_add' hU (good_smul _ (good_h hU 1)) (good_add (good_smul _ (good_h hU 2)) (good_h hU 3)),
    T_smul',
    T_add' hU (good_smul _ (good_h hU 2)) (good_h hU 3), T_smul',
    T_hseq' hU 0, T_hseq' hU 1, T_hseq' hU 2, T_hseq' hU 3, deg_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma good_combo5 (hU : IsGraphon U μ) :
    Good ((qval U μ ^ 4 + 3 * qval U μ ^ 2 * smom U μ 0 + 2 * qval U μ * smom U μ 1
          + smom U μ 0 ^ 2 + smom U μ 2) • hseq U μ 0
      + ((qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1) • hseq U μ 1
        + ((qval U μ ^ 2 + smom U μ 0) • hseq U μ 2 + (qval U μ • hseq U μ 3 + hseq U μ 4)))) :=
  good_add (good_smul _ (good_h hU 0))
    (good_add (good_smul _ (good_h hU 1))
      (good_add (good_smul _ (good_h hU 2)) (good_add (good_smul _ (good_h hU 3)) (good_h hU 4))))

lemma decomp6 (hU : IsGraphon U μ) :
    pathFun U μ 6 = (qval U μ ^ 6 + 5 * qval U μ ^ 4 * smom U μ 0 + 4 * qval U μ ^ 3 * smom U μ 1
        + 6 * qval U μ ^ 2 * smom U μ 0 ^ 2 + 3 * qval U μ ^ 2 * smom U μ 2
        + 6 * qval U μ * smom U μ 0 * smom U μ 1 + 2 * qval U μ * smom U μ 3
        + smom U μ 0 ^ 3 + 2 * smom U μ 0 * smom U μ 2 + smom U μ 1 ^ 2 + smom U μ 4)
          • (fun _ : Ω => (1:ℝ))
      + ((qval U μ ^ 5 + 4 * qval U μ ^ 3 * smom U μ 0 + 3 * qval U μ ^ 2 * smom U μ 1
            + 3 * qval U μ * smom U μ 0 ^ 2 + 2 * qval U μ * smom U μ 2 + 2 * smom U μ 0 * smom U μ 1
            + smom U μ 3) • hseq U μ 0
        + ((qval U μ ^ 4 + 3 * qval U μ ^ 2 * smom U μ 0 + 2 * qval U μ * smom U μ 1
              + smom U μ 0 ^ 2 + smom U μ 2) • hseq U μ 1
          + ((qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1) • hseq U μ 2
            + ((qval U μ ^ 2 + smom U μ 0) • hseq U μ 3 + (qval U μ • hseq U μ 4 + hseq U μ 5))))) := by
  funext x
  show T U μ (pathFun U μ 5) x = _
  rw [decomp5 hU,
    T_add' hU (good_smul _ good_one) (good_combo5 hU), T_smul', T_one hU,
    T_add' hU (good_smul _ (good_h hU 0))
      (good_add (good_smul _ (good_h hU 1))
        (good_add (good_smul _ (good_h hU 2)) (good_add (good_smul _ (good_h hU 3)) (good_h hU 4)))),
    T_smul',
    T_add' hU (good_smul _ (good_h hU 1))
      (good_add (good_smul _ (good_h hU 2)) (good_add (good_smul _ (good_h hU 3)) (good_h hU 4))),
    T_smul',
    T_add' hU (good_smul _ (good_h hU 2)) (good_add (good_smul _ (good_h hU 3)) (good_h hU 4)),
    T_smul',
    T_add' hU (good_smul _ (good_h hU 3)) (good_h hU 4), T_smul',
    T_hseq' hU 0, T_hseq' hU 1, T_hseq' hU 2, T_hseq' hU 3, T_hseq' hU 4, deg_eq']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma xden_five (hU : IsGraphon U μ) :
    xden U μ 5 = qval U μ ^ 5 + 4 * qval U μ ^ 3 * smom U μ 0 + 3 * qval U μ ^ 2 * smom U μ 1
      + 3 * qval U μ * smom U μ 0 ^ 2 + 2 * qval U μ * smom U μ 2 + 2 * smom U μ 0 * smom U μ 1
      + smom U μ 3 := by
  rw [xden, decomp5 hU]
  refine mean_const_add _ (good_combo5 hU) ?_
  rw [mean_add (good_smul _ (good_h hU 0))
        (good_add (good_smul _ (good_h hU 1))
          (good_add (good_smul _ (good_h hU 2)) (good_add (good_smul _ (good_h hU 3)) (good_h hU 4)))),
    mean_add (good_smul _ (good_h hU 1))
      (good_add (good_smul _ (good_h hU 2)) (good_add (good_smul _ (good_h hU 3)) (good_h hU 4))),
    mean_add (good_smul _ (good_h hU 2)) (good_add (good_smul _ (good_h hU 3)) (good_h hU 4)),
    mean_add (good_smul _ (good_h hU 3)) (good_h hU 4),
    mean_smul, mean_smul, mean_smul, mean_smul,
    mean_hseq hU, mean_hseq hU, mean_hseq hU, mean_hseq hU, mean_hseq hU]
  ring

lemma xden_six (hU : IsGraphon U μ) :
    xden U μ 6 = qval U μ ^ 6 + 5 * qval U μ ^ 4 * smom U μ 0 + 4 * qval U μ ^ 3 * smom U μ 1
      + 6 * qval U μ ^ 2 * smom U μ 0 ^ 2 + 3 * qval U μ ^ 2 * smom U μ 2
      + 6 * qval U μ * smom U μ 0 * smom U μ 1 + 2 * qval U μ * smom U μ 3
      + smom U μ 0 ^ 3 + 2 * smom U μ 0 * smom U μ 2 + smom U μ 1 ^ 2 + smom U μ 4 := by
  rw [xden, decomp6 hU]
  refine mean_const_add _
    (good_add (good_smul _ (good_h hU 0))
      (good_add (good_smul _ (good_h hU 1))
        (good_add (good_smul _ (good_h hU 2))
          (good_add (good_smul _ (good_h hU 3)) (good_add (good_smul _ (good_h hU 4)) (good_h hU 5)))))) ?_
  rw [mean_add (good_smul _ (good_h hU 0))
        (good_add (good_smul _ (good_h hU 1))
          (good_add (good_smul _ (good_h hU 2))
            (good_add (good_smul _ (good_h hU 3)) (good_add (good_smul _ (good_h hU 4)) (good_h hU 5))))),
    mean_add (good_smul _ (good_h hU 1))
      (good_add (good_smul _ (good_h hU 2))
        (good_add (good_smul _ (good_h hU 3)) (good_add (good_smul _ (good_h hU 4)) (good_h hU 5)))),
    mean_add (good_smul _ (good_h hU 2))
      (good_add (good_smul _ (good_h hU 3)) (good_add (good_smul _ (good_h hU 4)) (good_h hU 5))),
    mean_add (good_smul _ (good_h hU 3)) (good_add (good_smul _ (good_h hU 4)) (good_h hU 5)),
    mean_add (good_smul _ (good_h hU 4)) (good_h hU 5),
    mean_smul, mean_smul, mean_smul, mean_smul, mean_smul,
    mean_hseq hU, mean_hseq hU, mean_hseq hU, mean_hseq hU, mean_hseq hU, mean_hseq hU]
  ring

end OddCycleBound.Graphon
