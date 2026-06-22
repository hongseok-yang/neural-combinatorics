import OddCycleBound.Cycle

/-!
# The necklace identity for the cyclic complement trace

The cyclic complement density `cc_m = trace (compPow (1−U) (m−1))` telescopes (verified numerically in
`verify_necklace.py`) into an **O(m)-term** identity

  `cc_m = pc_{m-1} + Σ_{j=1}^{m-1} (−1)ʲ ⟨kernelOpʲ1, B^{m-1-j}1⟩ + (−1)ᵐ c_m`,

with `B = J − T_U` the complement operator, `pc` the path-complement density, `c_m` the cycle
density.  This file builds the foundations (complement kernel `compl`, its symmetry, `U` commuting
with its powers, the rank-one row-broadcast trace), on the way to that identity.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- The bilinear form `pairing f g = ∫ f·g`. -/
noncomputable def pairing (μ : Measure Ω) (f g : Ω → ℝ) : ℝ := ∫ x, f x * g x ∂μ

/-- The path iterates `pathIter n = kernelOpⁿ 1` are `Good`. -/
lemma good_pathIter (hU : IsGraphon U μ) : ∀ n, Good (pathIter U μ n)
  | 0 => good_one
  | (n + 1) => good_kernelOp hU (good_pathIter hU n)

/-- The complement kernel `compl = 1 − U`. -/
def compl (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 - U x y

lemma compl_eq_onesKernel_sub (x y : Ω) : compl U x y = onesKernel x y - U x y := by simp [compl, onesKernel]

lemma goodK_compl (hU : IsGraphon U μ) : GoodK (compl U) := by
  refine ⟨measurable_const.sub hU.meas, ⟨1, zero_le_one, fun x y => ?_⟩⟩
  rw [compl, abs_le]; constructor <;> nlinarith [hU.nonneg x y, hU.le_one x y]

lemma compl_symm (hU : IsGraphon U μ) (x y : Ω) : compl U x y = compl U y x := by
  simp only [compl, hU.symm x y]

/-- `U` commutes with its own composition powers: `Uᵒⁿ ∘ U = U ∘ Uᵒⁿ`. -/
lemma compPow_comm_U (hU : IsGraphon U μ) : ∀ n,
    comp μ (compPow μ U n) U = comp μ U (compPow μ U n) := by
  have hGU : GoodK U := goodK_of_isGraphon hU
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show comp μ (comp μ U (compPow μ U k)) U = comp μ U (comp μ U (compPow μ U k))
      rw [comp_assoc hGU (goodK_compPow hGU k) hGU, ih]

/-- Hence `Uᵒⁿ ∘ U = Uᵒ⁽ⁿ⁺¹⁾`. -/
lemma comp_compPow_U (hU : IsGraphon U μ) (n : ℕ) :
    comp μ (compPow μ U n) U = compPow μ U (n + 1) := by
  rw [compPow_comm_U hU]; rfl

/-- **Step B** (rank-one row-broadcast trace): `trace ((f ⊗ 1) ∘ R) = ∫ x, f x · (∫ z, R z x)`. -/
lemma trace_comp_rowBroadcast (f : Ω → ℝ) (R : Ω → Ω → ℝ) :
    trace μ (comp μ (fun x _ => f x) R) = ∫ x, f x * (∫ z, R z x ∂μ) ∂μ := by
  show ∫ x, comp μ (fun x _ => f x) R x x ∂μ = ∫ x, f x * (∫ z, R z x ∂μ) ∂μ
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, f x * R z x ∂μ) = f x * ∫ z, R z x ∂μ
  rw [integral_const_mul]

private lemma abs_sub_le'' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans (le_of_eq (by rw [abs_neg]))

/-- The complement iterate `complIter n = Bⁿ 1` where `B f = (∫f)·1 − kernelOp f`. -/
noncomputable def complIter (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => fun _ => 1
  | (n + 1) => fun x => mean μ (complIter U μ n) - kernelOp U μ (complIter U μ n) x

lemma good_complIter (hU : IsGraphon U μ) : ∀ n, Good (complIter U μ n)
  | 0 => good_one
  | (n + 1) => by
      obtain ⟨C, hC0, hC⟩ := (good_kernelOp hU (good_complIter hU n)).bdd
      refine ⟨stronglyMeasurable_const.sub (good_kernelOp hU (good_complIter hU n)).meas,
        ⟨|mean μ (complIter U μ n)| + C, by positivity, fun x => ?_⟩⟩
      show |mean μ (complIter U μ n) - kernelOp U μ (complIter U μ n) x| ≤ |mean μ (complIter U μ n)| + C
      exact (abs_sub_le'' _ _).trans (by linarith [hC x])

private lemma abs_compl_le_one (hU : IsGraphon U μ) (x z : Ω) : |compl U x z| ≤ 1 := by
  rw [compl, abs_le]; constructor <;> nlinarith [hU.nonneg x z, hU.le_one x z]

/-- The `compl` row-sum: `∫ y, complᵒ⁽ⁿ⁺¹⁾(x,y) = (B^{n+1} 1)(x)` (complement analogue of `rowsum_compPow`). -/
lemma rowsum_complPow (hU : IsGraphon U μ) : ∀ n,
    (fun x => ∫ y, compPow μ (compl U) n x y ∂μ) = complIter U μ (n + 1) := by
  have hGW : GoodK (compl U) := goodK_compl hU
  intro n
  induction n with
  | zero =>
      funext x
      show ∫ y, compl U x y ∂μ = mean μ (complIter U μ 0) - kernelOp U μ (complIter U μ 0) x
      rw [show complIter U μ 0 = (fun _ => (1:ℝ)) from rfl, mean_const, kernelOp_one hU]
      simp only [compl]
      rw [integral_sub (integrable_const 1) ((goodK_of_isGraphon hU).integrable_row x)]
      have h2 : ∫ y, U x y ∂μ = degree U μ x := rfl
      rw [h2]; simp
  | succ k ih =>
      funext x
      show ∫ y, comp μ (compl U) (compPow μ (compl U) k) x y ∂μ
          = mean μ (complIter U μ (k + 1)) - kernelOp U μ (complIter U μ (k + 1)) x
      obtain ⟨Ck, _, hCk⟩ := (goodK_compPow (μ := μ) hGW k).bdd
      have hint : Integrable (Function.uncurry fun y z => compl U x z * compPow μ (compl U) k z y) (μ.prod μ) := by
        have hSM : StronglyMeasurable (Function.uncurry fun y z => compl U x z * compPow μ (compl U) k z y) := by
          have h1 : Measurable (fun p : Ω × Ω => compl U x p.2) :=
            hGW.meas.comp (measurable_const.prodMk measurable_snd)
          have h2 : Measurable (fun p : Ω × Ω => compPow μ (compl U) k p.2 p.1) :=
            (goodK_compPow (μ := μ) hGW k).meas.comp (measurable_snd.prodMk measurable_fst)
          exact (h1.mul h2).stronglyMeasurable
        refine (integrable_const (1 * Ck)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
        rintro ⟨y, z⟩
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_compl_le_one hU x z) (hCk z y) (abs_nonneg _) (by norm_num)
      calc ∫ y, comp μ (compl U) (compPow μ (compl U) k) x y ∂μ
          = ∫ y, ∫ z, compl U x z * compPow μ (compl U) k z y ∂μ ∂μ := by simp only [comp]
        _ = ∫ z, ∫ y, compl U x z * compPow μ (compl U) k z y ∂μ ∂μ := integral_integral_swap hint
        _ = ∫ z, compl U x z * (∫ y, compPow μ (compl U) k z y ∂μ) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              show ∫ y, compl U x z * compPow μ (compl U) k z y ∂μ = compl U x z * ∫ y, compPow μ (compl U) k z y ∂μ
              rw [integral_const_mul]
        _ = ∫ z, compl U x z * complIter U μ (k + 1) z ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              have ihz : ∫ y, compPow μ (compl U) k z y ∂μ = complIter U μ (k + 1) z := congrFun ih z
              show compl U x z * (∫ y, compPow μ (compl U) k z y ∂μ) = compl U x z * complIter U μ (k + 1) z
              rw [ihz]
        _ = mean μ (complIter U μ (k + 1)) - kernelOp U μ (complIter U μ (k + 1)) x := by
              simp only [compl, sub_mul, one_mul]
              rw [integral_sub (good_complIter hU (k + 1)).integrable
                (integrable_Uf hU (good_complIter hU (k + 1)) x)]
              rfl

/-- Transpose-swap for symmetric kernels: `(K ∘ L)(y,x) = (L ∘ K)(x,y)`. -/
lemma comp_symm_swap {K L : Ω → Ω → ℝ} (hsK : ∀ x y, K x y = K y x)
    (hsL : ∀ x y, L x y = L y x) (x y : Ω) : comp μ K L y x = comp μ L K x y := by
  simp only [comp]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show K y z * L z x = L x z * K z y
  rw [hsK y z, hsL z x]; ring

/-- `K` commutes with its own powers: `Kᵒⁿ ∘ K = K ∘ Kᵒⁿ`. -/
lemma compPow_comm {K : Ω → Ω → ℝ} (hK : GoodK K) : ∀ n,
    comp μ (compPow μ K n) K = comp μ K (compPow μ K n)
  | 0 => rfl
  | (n + 1) => by
      show comp μ (comp μ K (compPow μ K n)) K = comp μ K (comp μ K (compPow μ K n))
      rw [comp_assoc hK (goodK_compPow hK n) hK, compPow_comm hK n]

/-- Powers of a symmetric kernel are symmetric. -/
lemma compPow_symm {K : Ω → Ω → ℝ} (hK : GoodK K) (hsymm : ∀ x y, K x y = K y x) :
    ∀ (n) (x y : Ω), compPow μ K n x y = compPow μ K n y x
  | 0, x, y => hsymm x y
  | (n + 1), x, y => by
      have ih : ∀ a b, compPow μ K n a b = compPow μ K n b a := fun a b => compPow_symm hK hsymm n a b
      show comp μ K (compPow μ K n) x y = comp μ K (compPow μ K n) y x
      rw [comp_symm_swap hsymm ih x y, compPow_comm hK n]

/-- `Uᵒᵃ ∘ compl = (pathFun_{a+1} ⊗ 1) − Uᵒ⁽ᵃ⁺¹⁾`. -/
lemma comp_compPow_compl (hU : IsGraphon U μ) (a : ℕ) :
    comp μ (compPow μ U a) (compl U) = fun x y => pathIter U μ (a + 1) x - compPow μ U (a + 1) x y := by
  have hGU := goodK_of_isGraphon hU
  have e : comp μ (compPow μ U a) (compl U)
      = fun x y => comp μ (compPow μ U a) onesKernel x y - comp μ (compPow μ U a) U x y := by
    rw [show (compl U) = (fun x y => onesKernel x y - U x y) from by funext x y; rw [compl_eq_onesKernel_sub]]
    exact comp_sub_right (goodK_compPow hGU a) goodK_onesKernel hGU
  rw [e, comp_compPow_U hU, comp_onesKernel_right]
  funext x y
  show (∫ z, compPow μ U a x z ∂μ) - compPow μ U (a + 1) x y
      = pathIter U μ (a + 1) x - compPow μ U (a + 1) x y
  rw [congrFun (rowsum_compPow hU a) x]

/-- The column-sum of `complᵒᵇ` equals the complement iterate `B^{b+1} 1`. -/
lemma colsum_compPow_compl (hU : IsGraphon U μ) (b : ℕ) :
    (fun x => ∫ z, compPow μ (compl U) b z x ∂μ) = complIter U μ (b + 1) := by
  have h : (fun x => ∫ z, compPow μ (compl U) b z x ∂μ)
      = (fun x => ∫ z, compPow μ (compl U) b x z ∂μ) := by
    funext x
    exact integral_congr_ae (ae_of_all _ fun z =>
      compPow_symm (goodK_compl hU) (compl_symm hU) b z x)
  rw [h, rowsum_complPow hU b]

/-- `mixedTrace a b = trace(Uᵒ⁽ᵃ⁺¹⁾ ∘ complᵒ⁽ᵇ⁺¹⁾)`. -/
noncomputable def mixedTrace (U : Ω → Ω → ℝ) (μ : Measure Ω) (a b : ℕ) : ℝ :=
  trace μ (comp μ (compPow μ U a) (compPow μ (compl U) b))

/-- **The telescoping recursion.** -/
lemma mixedTrace_succ (hU : IsGraphon U μ) (a b : ℕ) :
    mixedTrace U μ a (b + 1)
      = pairing μ (pathIter U μ (a + 1)) (complIter U μ (b + 1)) - mixedTrace U μ (a + 1) b := by
  have hGU := goodK_of_isGraphon hU
  have hGW := goodK_compl hU
  have hrow : GoodK (fun _x _y => pathIter U μ (a + 1) _x) :=
    goodK_rowBroadcast (good_pathIter hU (a + 1))
  show trace μ (comp μ (compPow μ U a) (compPow μ (compl U) (b + 1))) = _
  rw [show compPow μ (compl U) (b + 1) = comp μ (compl U) (compPow μ (compl U) b) from rfl,
    ← comp_assoc (goodK_compPow hGU a) hGW (goodK_compPow hGW b), comp_compPow_compl hU a,
    comp_sub_left hrow (goodK_compPow hGU (a + 1)) (goodK_compPow hGW b),
    trace_sub (goodK_comp hrow (goodK_compPow hGW b)) (goodK_comp (goodK_compPow hGU (a + 1)) (goodK_compPow hGW b)),
    trace_comp_rowBroadcast]
  show (∫ x, pathIter U μ (a + 1) x * (∫ z, compPow μ (compl U) b z x ∂μ) ∂μ) - mixedTrace U μ (a + 1) b
      = pairing μ (pathIter U μ (a + 1)) (complIter U μ (b + 1)) - mixedTrace U μ (a + 1) b
  congr 1
  show (∫ x, pathIter U μ (a + 1) x * (∫ z, compPow μ (compl U) b z x ∂μ) ∂μ)
      = ∫ x, pathIter U μ (a + 1) x * complIter U μ (b + 1) x ∂μ
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show pathIter U μ (a + 1) x * (∫ z, compPow μ (compl U) b z x ∂μ)
      = pathIter U μ (a + 1) x * complIter U μ (b + 1) x
  rw [congrFun (colsum_compPow_compl hU b) x]

/-- The base case: `mixedTrace a 0 = x_{a+1} − c_{a+1}` (with `c` the cycle density `trace (Uᵒ⁽ᵃ⁺¹⁾)`). -/
lemma mixedTrace_zero (hU : IsGraphon U μ) (a : ℕ) :
    mixedTrace U μ a 0 = pathDensity U μ (a + 1) - trace μ (compPow μ U (a + 1)) := by
  have hGU := goodK_of_isGraphon hU
  show trace μ (comp μ (compPow μ U a) (compl U)) = _
  rw [show (compl U) = (fun x y => onesKernel x y - U x y) from by funext x y; rw [compl_eq_onesKernel_sub],
    comp_sub_right (goodK_compPow hGU a) goodK_onesKernel hGU,
    trace_sub (goodK_comp (goodK_compPow hGU a) goodK_onesKernel) (goodK_comp (goodK_compPow hGU a) hGU),
    trace_comp_onesKernel_right, doubleMean_compPow hU a, comp_compPow_U hU]

/-- Splitting `compl = onesKernel − U` on the left of a composition (with `L` abstract, so the rewrite
does not touch `L`'s internals). -/
lemma comp_compl_left (hU : IsGraphon U μ) {L : Ω → Ω → ℝ} (hL : GoodK L) :
    comp μ (compl U) L = fun x y => comp μ onesKernel L x y - comp μ U L x y := by
  have hWeq : compl U = fun x y => onesKernel x y - U x y := by funext x y; rw [compl_eq_onesKernel_sub]
  rw [hWeq]; exact comp_sub_left goodK_onesKernel (goodK_of_isGraphon hU) hL

/-- The peeling step: `trace (complᵒ⁽ᵐ⁺¹⁾) = ∫∫ complᵒᵐ − mixedTrace 0 m`. -/
lemma complTrace_peel (hU : IsGraphon U μ) (m : ℕ) :
    trace μ (compPow μ (compl U) (m + 1)) = doubleMean μ (compPow μ (compl U) m) - mixedTrace U μ 0 m := by
  have hGU := goodK_of_isGraphon hU
  have hGW := goodK_compl hU
  show trace μ (comp μ (compl U) (compPow μ (compl U) m)) = _
  rw [comp_compl_left hU (goodK_compPow hGW m),
    trace_sub (goodK_comp goodK_onesKernel (goodK_compPow hGW m)) (goodK_comp hGU (goodK_compPow hGW m)),
    trace_comp_onesKernel (goodK_compPow hGW m)]
  rfl

/-- `∫∫ complᵒⁿ = mean (B^{n+1} 1)` (the path complement density). -/
lemma doubleMean_complPow (hU : IsGraphon U μ) (n : ℕ) :
    doubleMean μ (compPow μ (compl U) n) = mean μ (complIter U μ (n + 1)) := by
  rw [doubleMean, show (fun x => ∫ y, compPow μ (compl U) n x y ∂μ) = complIter U μ (n + 1) from rowsum_complPow hU n]
  rfl

/-- `kernelOp` is self-adjoint as a form on `Good` functions: `∫ (kernelOp f)·g = ∫ f·(kernelOp g)`. -/
lemma kernelOp_selfadj (hU : IsGraphon U μ) {f g : Ω → ℝ} (hf : Good f) (hg : Good g) :
    ∫ x, kernelOp U μ f x * g x ∂μ = ∫ x, f x * kernelOp U μ g x ∂μ := by
  have hGU := goodK_of_isGraphon hU
  obtain ⟨Cf, _, hCf⟩ := hf.bdd
  obtain ⟨Cg, _, hCg⟩ := hg.bdd
  have hint : Integrable (Function.uncurry fun x y => U x y * f y * g x) (μ.prod μ) := by
    have hSM : StronglyMeasurable (Function.uncurry fun x y => U x y * f y * g x) :=
      ((hGU.meas).mul (hf.meas.measurable.comp measurable_snd)).mul
        (hg.meas.measurable.comp measurable_fst) |>.stronglyMeasurable
    refine (integrable_const (1 * Cf * Cg)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
    rintro ⟨x, y⟩
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (mul_le_mul ?_ (hCf y) (abs_nonneg _) (by norm_num)) (hCg x) (abs_nonneg _)
      (by positivity)
    rw [abs_of_nonneg (hU.nonneg x y)]; exact hU.le_one x y
  calc ∫ x, kernelOp U μ f x * g x ∂μ
      = ∫ x, ∫ y, U x y * f y * g x ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show kernelOp U μ f x * g x = ∫ y, U x y * f y * g x ∂μ
        rw [kernelOp, integral_mul_const]
    _ = ∫ y, ∫ x, U x y * f y * g x ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, f y * kernelOp U μ g y ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show (∫ x, U x y * f y * g x ∂μ) = f y * kernelOp U μ g y
        rw [kernelOp, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show U x y * f y * g x = f y * (U y x * g x)
        rw [hU.symm x y]; ring

lemma pathIter_one (hU : IsGraphon U μ) : pathIter U μ 1 = degree U μ := by
  show kernelOp U μ (fun _ => 1) = degree U μ; exact kernelOp_one hU

/-- `x₀ = mean 1 = 1`. -/
lemma pathDensity_zero : pathDensity U μ 0 = 1 := by rw [pathDensity]; exact mean_one

lemma pathDensity_one (hU : IsGraphon U μ) : pathDensity U μ 1 = edgeDensity U μ := by
  rw [pathDensity, pathIter_one hU]; rfl

lemma complMean_zero : mean μ (complIter U μ 0) = 1 := mean_const 1

lemma pairing_complIter_zero (hU : IsGraphon U μ) (j : ℕ) :
    pairing μ (pathIter U μ j) (complIter U μ 0) = pathDensity U μ j := by
  simp only [pairing, complIter, mul_one]; rfl

/-- `mean (kernelOp f) = ⟨T1, f⟩ = ⟨pathIter 1, f⟩`. -/
lemma mean_kernelOp_eq (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) :
    mean μ (kernelOp U μ f) = pairing μ (pathIter U μ 1) f := by
  have h1 : mean μ (kernelOp U μ f) = ∫ x, kernelOp U μ f x * 1 ∂μ := by simp [mean]
  rw [h1, kernelOp_selfadj hU hf good_one]
  simp only [pairing, pathIter_one hU]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show f x * kernelOp U μ (fun _ => 1) x = degree U μ x * f x
  rw [kernelOp_one hU]; ring

/-- The inner-product recursion (uses `kernelOp` self-adjointness). -/
lemma pairing_complIter_succ (hU : IsGraphon U μ) (j k : ℕ) :
    pairing μ (pathIter U μ j) (complIter U μ (k + 1))
      = mean μ (complIter U μ k) * pathDensity U μ j - pairing μ (pathIter U μ (j + 1)) (complIter U μ k) := by
  have hpj := good_pathIter hU j
  have hvk := good_complIter hU k
  have key : ∀ x, pathIter U μ j x * complIter U μ (k + 1) x
      = mean μ (complIter U μ k) * pathIter U μ j x - pathIter U μ j x * kernelOp U μ (complIter U μ k) x := by
    intro x
    show pathIter U μ j x * (mean μ (complIter U μ k) - kernelOp U μ (complIter U μ k) x) = _
    ring
  simp only [pairing]
  rw [integral_congr_ae (ae_of_all _ key),
    integral_sub (hpj.integrable.const_mul _) ((hpj.mul (good_kernelOp hU hvk)).integrable),
    integral_const_mul]
  congr 1
  rw [← kernelOp_selfadj hU hpj hvk]
  rfl

/-- The path-complement recursion. -/
lemma complMean_succ (hU : IsGraphon U μ) (k : ℕ) :
    mean μ (complIter U μ (k + 1)) = mean μ (complIter U μ k) - pairing μ (pathIter U μ 1) (complIter U μ k) := by
  have hvk := good_complIter hU k
  have key : ∀ x, complIter U μ (k + 1) x = mean μ (complIter U μ k) - kernelOp U μ (complIter U μ k) x := fun x => rfl
  show ∫ x, complIter U μ (k + 1) x ∂μ = mean μ (complIter U μ k) - pairing μ (pathIter U μ 1) (complIter U μ k)
  rw [integral_congr_ae (ae_of_all _ key),
    integral_sub (integrable_const _) (good_kernelOp hU hvk).integrable]
  rw [show (∫ _x : Ω, mean μ (complIter U μ k) ∂μ) = mean μ (complIter U μ k) from by simp,
    show (∫ x, kernelOp U μ (complIter U μ k) x ∂μ) = mean μ (kernelOp U μ (complIter U μ k)) from rfl,
    mean_kernelOp_eq hU hvk]

/-- **Closed form for the necklace pairings.**  Every inner product `⟨pathIter j, complIter k⟩`
reduces, by the recursion `pairing_complIter_succ`, to the path densities `x_{j+i}` weighted by the
lower complement means `mean (complIter (k−1−i))`:

  `⟨pathIter j, complIter k⟩ = Σ_{i<k} (−1)ⁱ · mean(complIter (k−1−i)) · x_{j+i} + (−1)ᵏ · x_{j+k}`.

This is the general replacement for the `O(m²)` hand-unrolled `ip_{j,k}` facts in the per-cycle
assemblies (`BoundsC5C7.lean`, `C9.lean`): only the `O(m)` complement means remain to be expanded. -/
lemma pairing_pathIter_complIter_closed (hU : IsGraphon U μ) : ∀ (k j : ℕ),
    pairing μ (pathIter U μ j) (complIter U μ k)
      = (∑ i ∈ Finset.range k,
          (-1 : ℝ) ^ i * (mean μ (complIter U μ (k - 1 - i)) * pathDensity U μ (j + i)))
        + (-1 : ℝ) ^ k * pathDensity U μ (j + k) := by
  intro k
  induction k with
  | zero => intro j; simp [pairing_complIter_zero hU j]
  | succ k ih =>
      intro j
      rw [pairing_complIter_succ hU j k, ih (j + 1),
        Finset.sum_range_succ' (fun i =>
          (-1 : ℝ) ^ i * (mean μ (complIter U μ (k + 1 - 1 - i)) * pathDensity U μ (j + i))) k]
      have hsum : ∀ i ∈ Finset.range k,
          (-1 : ℝ) ^ (i + 1) * (mean μ (complIter U μ (k + 1 - 1 - (i + 1))) * pathDensity U μ (j + (i + 1)))
            = -((-1 : ℝ) ^ i * (mean μ (complIter U μ (k - 1 - i)) * pathDensity U μ ((j + 1) + i))) := by
        intro i _
        have e1 : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
        have e2 : j + (i + 1) = (j + 1) + i := by omega
        rw [e1, e2, pow_succ]; ring
      rw [Finset.sum_congr rfl hsum, Finset.sum_neg_distrib]
      have e3 : k + 1 - 1 - 0 = k := by omega
      have e4 : j + 0 = j := by omega
      have e5 : j + (k + 1) = j + 1 + k := by omega
      rw [e3, e4, e5]
      ring

omit [IsProbabilityMeasure μ] in
/-- The `j = 0` inner product is just the mean: `⟨pathIter 0, v⟩ = ⟨1, v⟩ = mean v`. -/
lemma pairing_pathIter_zero (v : Ω → ℝ) : pairing μ (pathIter U μ 0) v = mean μ v := by
  simp only [pairing, pathIter, one_mul, mean]

/-- **Telescoping of `mixedTrace`.**  For all `b a`,
`mixedTrace a b = Σ_{i<b} (−1)ⁱ ⟨pathIter (a+1+i), complIter (b−i)⟩ + (−1)ᵇ mixedTrace (a+b) 0`. -/
lemma mixedTrace_telescope (hU : IsGraphon U μ) : ∀ (b a : ℕ),
    mixedTrace U μ a b
      = (∑ i ∈ Finset.range b,
          (-1 : ℝ) ^ i * pairing μ (pathIter U μ (a + 1 + i)) (complIter U μ (b - i)))
        + (-1 : ℝ) ^ b * mixedTrace U μ (a + b) 0 := by
  intro b
  induction b with
  | zero => intro a; simp
  | succ b ih =>
      intro a
      have hsum : ∀ i ∈ Finset.range b,
          (-1 : ℝ) ^ (i + 1) * pairing μ (pathIter U μ (a + 1 + (i + 1))) (complIter U μ (b + 1 - (i + 1)))
            = -((-1 : ℝ) ^ i * pairing μ (pathIter U μ (a + 1 + 1 + i)) (complIter U μ (b - i))) := by
        intro i _
        have e1 : a + 1 + (i + 1) = a + 1 + 1 + i := by omega
        have e2 : b + 1 - (i + 1) = b - i := Nat.succ_sub_succ b i
        rw [e1, e2, pow_succ]; ring
      rw [mixedTrace_succ hU a b, ih (a + 1),
        Finset.sum_range_succ' (fun i =>
          (-1 : ℝ) ^ i * pairing μ (pathIter U μ (a + 1 + i)) (complIter U μ (b + 1 - i))) b,
        Finset.sum_congr rfl hsum, Finset.sum_neg_distrib]
      have eb : a + 1 + b = a + (b + 1) := by omega
      rw [eb, pow_succ]
      simp only [pow_zero, one_mul, Nat.sub_zero, zero_add, Nat.add_zero]
      ring

/-- **The general-`m` necklace identity.**  For every `n`,
`trace (complᵒ⁽ⁿ⁺¹⁾) = Σ_{j=0}^{n} (−1)ʲ ⟨pathIter j, complIter (n+1−j)⟩ + (−1)ⁿ⁺¹ (x_{n+1} − c_{n+1})`. -/
lemma complTrace_necklace (hU : IsGraphon U μ) (n : ℕ) :
    trace μ (compPow μ (compl U) (n + 1))
      = (∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * pairing μ (pathIter U μ j) (complIter U μ (n + 1 - j)))
        + (-1 : ℝ) ^ (n + 1) * (pathDensity U μ (n + 1) - trace μ (compPow μ U (n + 1))) := by
  rw [complTrace_peel hU n, doubleMean_complPow hU n, mixedTrace_telescope hU n 0]
  simp only [Nat.zero_add]
  rw [mixedTrace_zero hU n,
    Finset.sum_range_succ' (fun j =>
      (-1 : ℝ) ^ j * pairing μ (pathIter U μ j) (complIter U μ (n + 1 - j))) n,
    pairing_pathIter_zero]
  have hsum : ∀ i ∈ Finset.range n,
      (-1 : ℝ) ^ (i + 1) * pairing μ (pathIter U μ (i + 1)) (complIter U μ (n + 1 - (i + 1)))
        = -((-1 : ℝ) ^ i * pairing μ (pathIter U μ (1 + i)) (complIter U μ (n - i))) := by
    intro i _
    have e1 : (1 : ℕ) + i = i + 1 := by omega
    have e2 : n + 1 - (i + 1) = n - i := Nat.succ_sub_succ n i
    rw [e1, e2, pow_succ]; ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_neg_distrib, pow_succ]
  simp only [Nat.sub_zero]
  ring

/-! ### C₇ -/

lemma edgeDensity_nonneg (hU : IsGraphon U μ) : 0 ≤ edgeDensity U μ :=
  integral_nonneg fun x => integral_nonneg fun y => hU.nonneg x y

lemma edgeDensity_le_one (hU : IsGraphon U μ) : edgeDensity U μ ≤ 1 := by
  rw [edgeDensity, mean]
  calc ∫ x, degree U μ x ∂μ ≤ ∫ _x, (1:ℝ) ∂μ := by
        refine integral_mono ((goodK_of_isGraphon hU).colsum_integrable.congr
          (ae_of_all _ fun x => by rw [degree]; exact integral_congr_ae (ae_of_all _ fun y => hU.symm y x)))
          (integrable_const 1) (fun x => ?_)
        rw [degree]
        calc ∫ y, U x y ∂μ ≤ ∫ _y, (1:ℝ) ∂μ :=
              integral_mono ((goodK_of_isGraphon hU).integrable_row x) (integrable_const 1)
                (fun y => hU.le_one x y)
          _ = 1 := by simp
    _ = 1 := by simp

/-- The complement kernel `compl U = 1 − U` is itself a graphon. -/
lemma isGraphon_compl (hU : IsGraphon U μ) : IsGraphon (compl U) μ where
  meas := by
    have h : Function.uncurry (compl U) = fun p : Ω × Ω => 1 - U p.1 p.2 := rfl
    rw [h]; exact measurable_const.sub hU.meas
  nonneg := fun x y => by rw [compl]; linarith [hU.le_one x y]
  le_one := fun x y => by rw [compl]; linarith [hU.nonneg x y]
  symm := fun x y => by rw [compl, compl, hU.symm x y]

end OddCycleBound
