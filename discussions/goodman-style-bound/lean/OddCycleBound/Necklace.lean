import OddCycleBound.Cycle

/-!
# The necklace identity for the cyclic complement trace — Stage 4c (general tool)

The cyclic complement density `cc_m = tr (Kpow (1−U) (m−1))` telescopes (verified numerically in
`verify_necklace.py`) into an **O(m)-term** identity

  `cc_m = pc_{m-1} + Σ_{j=1}^{m-1} (−1)ʲ ⟨Tʲ1, B^{m-1-j}1⟩ + (−1)ᵐ c_m`,

with `B = J − T_U` the complement operator, `pc` the path-complement density, `c_m` the cycle
density.  This file builds the foundations (complement kernel `Wk`, its symmetry, `U` commuting
with its powers, the rank-one row-broadcast trace), on the way to that identity.
-/

open MeasureTheory

namespace OddCycleBound.Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- The bilinear form `ip f g = ∫ f·g`. -/
noncomputable def ip (μ : Measure Ω) (f g : Ω → ℝ) : ℝ := ∫ x, f x * g x ∂μ

/-- The path iterates `pathFun n = Tⁿ 1` are `Good`. -/
lemma good_pathFun (hU : IsGraphon U μ) : ∀ n, Good (pathFun U μ n)
  | 0 => good_one
  | (n + 1) => good_T hU (good_pathFun hU n)

/-- The complement kernel `Wk = 1 − U`. -/
def Wk (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 - U x y

lemma Wk_eq_Jk_sub (x y : Ω) : Wk U x y = Jk x y - U x y := by simp [Wk, Jk]

lemma goodK_Wk (hU : IsGraphon U μ) : GoodK (Wk U) := by
  refine ⟨measurable_const.sub hU.meas, ⟨1, zero_le_one, fun x y => ?_⟩⟩
  rw [Wk, abs_le]; constructor <;> nlinarith [hU.nonneg x y, hU.le_one x y]

lemma Wk_symm (hU : IsGraphon U μ) (x y : Ω) : Wk U x y = Wk U y x := by
  simp only [Wk, hU.symm x y]

/-- `U` commutes with its own composition powers: `Uᵒⁿ ∘ U = U ∘ Uᵒⁿ`. -/
lemma Kpow_comm_U (hU : IsGraphon U μ) : ∀ n,
    comp μ (Kpow μ U n) U = comp μ U (Kpow μ U n) := by
  have hGU : GoodK U := goodK_of_isGraphon hU
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show comp μ (comp μ U (Kpow μ U k)) U = comp μ U (comp μ U (Kpow μ U k))
      rw [comp_assoc hGU (goodK_Kpow hGU k) hGU, ih]

/-- Hence `Uᵒⁿ ∘ U = Uᵒ⁽ⁿ⁺¹⁾`. -/
lemma comp_Kpow_U (hU : IsGraphon U μ) (n : ℕ) :
    comp μ (Kpow μ U n) U = Kpow μ U (n + 1) := by
  rw [Kpow_comm_U hU]; rfl

/-- **Step B** (rank-one row-broadcast trace): `tr ((f ⊗ 1) ∘ R) = ∫ x, f x · (∫ z, R z x)`. -/
lemma tr_comp_rowBroadcast (f : Ω → ℝ) (R : Ω → Ω → ℝ) :
    tr μ (comp μ (fun x _ => f x) R) = ∫ x, f x * (∫ z, R z x ∂μ) ∂μ := by
  show ∫ x, comp μ (fun x _ => f x) R x x ∂μ = ∫ x, f x * (∫ z, R z x ∂μ) ∂μ
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, f x * R z x ∂μ) = f x * ∫ z, R z x ∂μ
  rw [integral_const_mul]

private lemma abs_sub_le'' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans (le_of_eq (by rw [abs_neg]))

/-- The complement iterate `vcomp n = Bⁿ 1` where `B f = (∫f)·1 − T f`. -/
noncomputable def vcomp (U : Ω → Ω → ℝ) (μ : Measure Ω) : ℕ → (Ω → ℝ)
  | 0 => fun _ => 1
  | (n + 1) => fun x => mean μ (vcomp U μ n) - T U μ (vcomp U μ n) x

lemma good_vcomp (hU : IsGraphon U μ) : ∀ n, Good (vcomp U μ n)
  | 0 => good_one
  | (n + 1) => by
      obtain ⟨C, hC0, hC⟩ := (good_T hU (good_vcomp hU n)).bdd
      refine ⟨stronglyMeasurable_const.sub (good_T hU (good_vcomp hU n)).meas,
        ⟨|mean μ (vcomp U μ n)| + C, by positivity, fun x => ?_⟩⟩
      show |mean μ (vcomp U μ n) - T U μ (vcomp U μ n) x| ≤ |mean μ (vcomp U μ n)| + C
      exact (abs_sub_le'' _ _).trans (by linarith [hC x])

private lemma abs_Wk_le_one (hU : IsGraphon U μ) (x z : Ω) : |Wk U x z| ≤ 1 := by
  rw [Wk, abs_le]; constructor <;> nlinarith [hU.nonneg x z, hU.le_one x z]

/-- The `Wk` row-sum: `∫ y, Wkᵒ⁽ⁿ⁺¹⁾(x,y) = (B^{n+1} 1)(x)` (complement analogue of `rowsum_Kpow`). -/
lemma rowsum_Wpow (hU : IsGraphon U μ) : ∀ n,
    (fun x => ∫ y, Kpow μ (Wk U) n x y ∂μ) = vcomp U μ (n + 1) := by
  have hGW : GoodK (Wk U) := goodK_Wk hU
  intro n
  induction n with
  | zero =>
      funext x
      show ∫ y, Wk U x y ∂μ = mean μ (vcomp U μ 0) - T U μ (vcomp U μ 0) x
      rw [show vcomp U μ 0 = (fun _ => (1:ℝ)) from rfl, mean_const, T_one hU]
      simp only [Wk]
      rw [integral_sub (integrable_const 1) ((goodK_of_isGraphon hU).integrable_row x)]
      have h2 : ∫ y, U x y ∂μ = deg U μ x := rfl
      rw [h2]; simp
  | succ k ih =>
      funext x
      show ∫ y, comp μ (Wk U) (Kpow μ (Wk U) k) x y ∂μ
          = mean μ (vcomp U μ (k + 1)) - T U μ (vcomp U μ (k + 1)) x
      obtain ⟨Ck, _, hCk⟩ := (goodK_Kpow (μ := μ) hGW k).bdd
      have hint : Integrable (Function.uncurry fun y z => Wk U x z * Kpow μ (Wk U) k z y) (μ.prod μ) := by
        have hSM : StronglyMeasurable (Function.uncurry fun y z => Wk U x z * Kpow μ (Wk U) k z y) := by
          have h1 : Measurable (fun p : Ω × Ω => Wk U x p.2) :=
            hGW.meas.comp (measurable_const.prodMk measurable_snd)
          have h2 : Measurable (fun p : Ω × Ω => Kpow μ (Wk U) k p.2 p.1) :=
            (goodK_Kpow (μ := μ) hGW k).meas.comp (measurable_snd.prodMk measurable_fst)
          exact (h1.mul h2).stronglyMeasurable
        refine (integrable_const (1 * Ck)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
        rintro ⟨y, z⟩
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_Wk_le_one hU x z) (hCk z y) (abs_nonneg _) (by norm_num)
      calc ∫ y, comp μ (Wk U) (Kpow μ (Wk U) k) x y ∂μ
          = ∫ y, ∫ z, Wk U x z * Kpow μ (Wk U) k z y ∂μ ∂μ := by simp only [comp]
        _ = ∫ z, ∫ y, Wk U x z * Kpow μ (Wk U) k z y ∂μ ∂μ := integral_integral_swap hint
        _ = ∫ z, Wk U x z * (∫ y, Kpow μ (Wk U) k z y ∂μ) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              show ∫ y, Wk U x z * Kpow μ (Wk U) k z y ∂μ = Wk U x z * ∫ y, Kpow μ (Wk U) k z y ∂μ
              rw [integral_const_mul]
        _ = ∫ z, Wk U x z * vcomp U μ (k + 1) z ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              have ihz : ∫ y, Kpow μ (Wk U) k z y ∂μ = vcomp U μ (k + 1) z := congrFun ih z
              show Wk U x z * (∫ y, Kpow μ (Wk U) k z y ∂μ) = Wk U x z * vcomp U μ (k + 1) z
              rw [ihz]
        _ = mean μ (vcomp U μ (k + 1)) - T U μ (vcomp U μ (k + 1)) x := by
              simp only [Wk, sub_mul, one_mul]
              rw [integral_sub (good_vcomp hU (k + 1)).integrable
                (integrable_Uf hU (good_vcomp hU (k + 1)) x)]
              rfl

/-- Transpose-swap for symmetric kernels: `(K ∘ L)(y,x) = (L ∘ K)(x,y)`. -/
lemma comp_symm_swap {K L : Ω → Ω → ℝ} (hsK : ∀ x y, K x y = K y x)
    (hsL : ∀ x y, L x y = L y x) (x y : Ω) : comp μ K L y x = comp μ L K x y := by
  simp only [comp]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show K y z * L z x = L x z * K z y
  rw [hsK y z, hsL z x]; ring

/-- `K` commutes with its own powers: `Kᵒⁿ ∘ K = K ∘ Kᵒⁿ`. -/
lemma Kpow_comm {K : Ω → Ω → ℝ} (hK : GoodK K) : ∀ n,
    comp μ (Kpow μ K n) K = comp μ K (Kpow μ K n)
  | 0 => rfl
  | (n + 1) => by
      show comp μ (comp μ K (Kpow μ K n)) K = comp μ K (comp μ K (Kpow μ K n))
      rw [comp_assoc hK (goodK_Kpow hK n) hK, Kpow_comm hK n]

/-- Powers of a symmetric kernel are symmetric. -/
lemma Kpow_symm {K : Ω → Ω → ℝ} (hK : GoodK K) (hsymm : ∀ x y, K x y = K y x) :
    ∀ (n) (x y : Ω), Kpow μ K n x y = Kpow μ K n y x
  | 0, x, y => hsymm x y
  | (n + 1), x, y => by
      have ih : ∀ a b, Kpow μ K n a b = Kpow μ K n b a := fun a b => Kpow_symm hK hsymm n a b
      show comp μ K (Kpow μ K n) x y = comp μ K (Kpow μ K n) y x
      rw [comp_symm_swap hsymm ih x y, Kpow_comm hK n]

/-- `Uᵒᵃ ∘ Wk = (pathFun_{a+1} ⊗ 1) − Uᵒ⁽ᵃ⁺¹⁾`. -/
lemma comp_Kpow_Wk (hU : IsGraphon U μ) (a : ℕ) :
    comp μ (Kpow μ U a) (Wk U) = fun x y => pathFun U μ (a + 1) x - Kpow μ U (a + 1) x y := by
  have hGU := goodK_of_isGraphon hU
  have e : comp μ (Kpow μ U a) (Wk U)
      = fun x y => comp μ (Kpow μ U a) Jk x y - comp μ (Kpow μ U a) U x y := by
    rw [show (Wk U) = (fun x y => Jk x y - U x y) from by funext x y; rw [Wk_eq_Jk_sub]]
    exact comp_sub_right (goodK_Kpow hGU a) goodK_Jk hGU
  rw [e, comp_Kpow_U hU, comp_Jk_right]
  funext x y
  show (∫ z, Kpow μ U a x z ∂μ) - Kpow μ U (a + 1) x y
      = pathFun U μ (a + 1) x - Kpow μ U (a + 1) x y
  rw [congrFun (rowsum_Kpow hU a) x]

/-- The column-sum of `Wkᵒᵇ` equals the complement iterate `B^{b+1} 1`. -/
lemma colsum_Kpow_Wk (hU : IsGraphon U μ) (b : ℕ) :
    (fun x => ∫ z, Kpow μ (Wk U) b z x ∂μ) = vcomp U μ (b + 1) := by
  have h : (fun x => ∫ z, Kpow μ (Wk U) b z x ∂μ)
      = (fun x => ∫ z, Kpow μ (Wk U) b x z ∂μ) := by
    funext x
    exact integral_congr_ae (ae_of_all _ fun z =>
      Kpow_symm (goodK_Wk hU) (Wk_symm hU) b z x)
  rw [h, rowsum_Wpow hU b]

/-- `Htr a b = tr(Uᵒ⁽ᵃ⁺¹⁾ ∘ Wkᵒ⁽ᵇ⁺¹⁾)`. -/
noncomputable def Htr (U : Ω → Ω → ℝ) (μ : Measure Ω) (a b : ℕ) : ℝ :=
  tr μ (comp μ (Kpow μ U a) (Kpow μ (Wk U) b))

/-- **The telescoping recursion.** -/
lemma Htr_succ (hU : IsGraphon U μ) (a b : ℕ) :
    Htr U μ a (b + 1)
      = ip μ (pathFun U μ (a + 1)) (vcomp U μ (b + 1)) - Htr U μ (a + 1) b := by
  have hGU := goodK_of_isGraphon hU
  have hGW := goodK_Wk hU
  have hrow : GoodK (fun _x _y => pathFun U μ (a + 1) _x) :=
    goodK_rowBroadcast (good_pathFun hU (a + 1))
  show tr μ (comp μ (Kpow μ U a) (Kpow μ (Wk U) (b + 1))) = _
  rw [show Kpow μ (Wk U) (b + 1) = comp μ (Wk U) (Kpow μ (Wk U) b) from rfl,
    ← comp_assoc (goodK_Kpow hGU a) hGW (goodK_Kpow hGW b), comp_Kpow_Wk hU a,
    comp_sub_left hrow (goodK_Kpow hGU (a + 1)) (goodK_Kpow hGW b),
    tr_sub (goodK_comp hrow (goodK_Kpow hGW b)) (goodK_comp (goodK_Kpow hGU (a + 1)) (goodK_Kpow hGW b)),
    tr_comp_rowBroadcast]
  show (∫ x, pathFun U μ (a + 1) x * (∫ z, Kpow μ (Wk U) b z x ∂μ) ∂μ) - Htr U μ (a + 1) b
      = ip μ (pathFun U μ (a + 1)) (vcomp U μ (b + 1)) - Htr U μ (a + 1) b
  congr 1
  show (∫ x, pathFun U μ (a + 1) x * (∫ z, Kpow μ (Wk U) b z x ∂μ) ∂μ)
      = ∫ x, pathFun U μ (a + 1) x * vcomp U μ (b + 1) x ∂μ
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show pathFun U μ (a + 1) x * (∫ z, Kpow μ (Wk U) b z x ∂μ)
      = pathFun U μ (a + 1) x * vcomp U μ (b + 1) x
  rw [congrFun (colsum_Kpow_Wk hU b) x]

/-- The base case: `Htr a 0 = x_{a+1} − c_{a+1}` (with `c` the cycle density `tr (Uᵒ⁽ᵃ⁺¹⁾)`). -/
lemma Htr_zero (hU : IsGraphon U μ) (a : ℕ) :
    Htr U μ a 0 = xden U μ (a + 1) - tr μ (Kpow μ U (a + 1)) := by
  have hGU := goodK_of_isGraphon hU
  show tr μ (comp μ (Kpow μ U a) (Wk U)) = _
  rw [show (Wk U) = (fun x y => Jk x y - U x y) from by funext x y; rw [Wk_eq_Jk_sub],
    comp_sub_right (goodK_Kpow hGU a) goodK_Jk hGU,
    tr_sub (goodK_comp (goodK_Kpow hGU a) goodK_Jk) (goodK_comp (goodK_Kpow hGU a) hGU),
    tr_comp_Jk_right, dmean_Kpow hU a, comp_Kpow_U hU]

/-- Splitting `Wk = Jk − U` on the left of a composition (with `L` abstract, so the rewrite
does not touch `L`'s internals). -/
lemma comp_Wk_left (hU : IsGraphon U μ) {L : Ω → Ω → ℝ} (hL : GoodK L) :
    comp μ (Wk U) L = fun x y => comp μ Jk L x y - comp μ U L x y := by
  have hWeq : Wk U = fun x y => Jk x y - U x y := by funext x y; rw [Wk_eq_Jk_sub]
  rw [hWeq]; exact comp_sub_left goodK_Jk (goodK_of_isGraphon hU) hL

/-- The peeling step: `tr (Wkᵒ⁽ᵐ⁺¹⁾) = ∫∫ Wkᵒᵐ − Htr 0 m`. -/
lemma ccomp_peel (hU : IsGraphon U μ) (m : ℕ) :
    tr μ (Kpow μ (Wk U) (m + 1)) = dmean μ (Kpow μ (Wk U) m) - Htr U μ 0 m := by
  have hGU := goodK_of_isGraphon hU
  have hGW := goodK_Wk hU
  show tr μ (comp μ (Wk U) (Kpow μ (Wk U) m)) = _
  rw [comp_Wk_left hU (goodK_Kpow hGW m),
    tr_sub (goodK_comp goodK_Jk (goodK_Kpow hGW m)) (goodK_comp hGU (goodK_Kpow hGW m)),
    tr_comp_Jk (goodK_Kpow hGW m)]
  rfl

/-- `∫∫ Wkᵒⁿ = mean (B^{n+1} 1)` (the path complement density). -/
lemma dmean_Wpow (hU : IsGraphon U μ) (n : ℕ) :
    dmean μ (Kpow μ (Wk U) n) = mean μ (vcomp U μ (n + 1)) := by
  rw [dmean, show (fun x => ∫ y, Kpow μ (Wk U) n x y ∂μ) = vcomp U μ (n + 1) from rowsum_Wpow hU n]
  rfl

/-- `T` is self-adjoint as a form on `Good` functions: `∫ (T f)·g = ∫ f·(T g)`. -/
lemma T_selfadj (hU : IsGraphon U μ) {f g : Ω → ℝ} (hf : Good f) (hg : Good g) :
    ∫ x, T U μ f x * g x ∂μ = ∫ x, f x * T U μ g x ∂μ := by
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
  calc ∫ x, T U μ f x * g x ∂μ
      = ∫ x, ∫ y, U x y * f y * g x ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show T U μ f x * g x = ∫ y, U x y * f y * g x ∂μ
        rw [T, integral_mul_const]
    _ = ∫ y, ∫ x, U x y * f y * g x ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, f y * T U μ g y ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show (∫ x, U x y * f y * g x ∂μ) = f y * T U μ g y
        rw [T, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show U x y * f y * g x = f y * (U y x * g x)
        rw [hU.symm x y]; ring

lemma pathFun_one (hU : IsGraphon U μ) : pathFun U μ 1 = deg U μ := by
  show T U μ (fun _ => 1) = deg U μ; exact T_one hU

lemma xden_one (hU : IsGraphon U μ) : xden U μ 1 = qval U μ := by
  rw [xden, pathFun_one hU]; rfl

lemma pcomp_zero : mean μ (vcomp U μ 0) = 1 := mean_const 1

lemma ip_vcomp_zero (hU : IsGraphon U μ) (j : ℕ) :
    ip μ (pathFun U μ j) (vcomp U μ 0) = xden U μ j := by
  simp only [ip, vcomp, mul_one]; rfl

/-- `mean (T f) = ⟨T1, f⟩ = ⟨pathFun 1, f⟩`. -/
lemma mean_T_eq (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) :
    mean μ (T U μ f) = ip μ (pathFun U μ 1) f := by
  have h1 : mean μ (T U μ f) = ∫ x, T U μ f x * 1 ∂μ := by simp [mean]
  rw [h1, T_selfadj hU hf good_one]
  simp only [ip, pathFun_one hU]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show f x * T U μ (fun _ => 1) x = deg U μ x * f x
  rw [T_one hU]; ring

/-- The inner-product recursion (uses `T` self-adjointness). -/
lemma ip_vcomp_succ (hU : IsGraphon U μ) (j k : ℕ) :
    ip μ (pathFun U μ j) (vcomp U μ (k + 1))
      = mean μ (vcomp U μ k) * xden U μ j - ip μ (pathFun U μ (j + 1)) (vcomp U μ k) := by
  have hpj := good_pathFun hU j
  have hvk := good_vcomp hU k
  have key : ∀ x, pathFun U μ j x * vcomp U μ (k + 1) x
      = mean μ (vcomp U μ k) * pathFun U μ j x - pathFun U μ j x * T U μ (vcomp U μ k) x := by
    intro x
    show pathFun U μ j x * (mean μ (vcomp U μ k) - T U μ (vcomp U μ k) x) = _
    ring
  simp only [ip]
  rw [integral_congr_ae (ae_of_all _ key),
    integral_sub (hpj.integrable.const_mul _) ((hpj.mul (good_T hU hvk)).integrable),
    integral_const_mul]
  congr 1
  rw [← T_selfadj hU hpj hvk]
  rfl

/-- The path-complement recursion. -/
lemma pcomp_succ (hU : IsGraphon U μ) (k : ℕ) :
    mean μ (vcomp U μ (k + 1)) = mean μ (vcomp U μ k) - ip μ (pathFun U μ 1) (vcomp U μ k) := by
  have hvk := good_vcomp hU k
  have key : ∀ x, vcomp U μ (k + 1) x = mean μ (vcomp U μ k) - T U μ (vcomp U μ k) x := fun x => rfl
  show ∫ x, vcomp U μ (k + 1) x ∂μ = mean μ (vcomp U μ k) - ip μ (pathFun U μ 1) (vcomp U μ k)
  rw [integral_congr_ae (ae_of_all _ key),
    integral_sub (integrable_const _) (good_T hU hvk).integrable]
  rw [show (∫ _x : Ω, mean μ (vcomp U μ k) ∂μ) = mean μ (vcomp U μ k) from by simp,
    show (∫ x, T U μ (vcomp U μ k) x ∂μ) = mean μ (T U μ (vcomp U μ k)) from rfl,
    mean_T_eq hU hvk]

/-- **The C₅ necklace identity** (`cc₅` in path-complement / inner-product form). -/
lemma ccomp5_necklace (hU : IsGraphon U μ) :
    tr μ (Kpow μ (Wk U) 4)
      = mean μ (vcomp U μ 4) - ip μ (pathFun U μ 1) (vcomp U μ 3)
        + ip μ (pathFun U μ 2) (vcomp U μ 2) - ip μ (pathFun U μ 3) (vcomp U μ 1)
        + xden U μ 4 - tr μ (Kpow μ U 4) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, ccomp_peel hU 3, dmean_Wpow hU 3,
    Htr_succ hU 0 2, Htr_succ hU 1 1, Htr_succ hU 2 0, Htr_zero hU 3]
  ring

/-- **`C₅` for all edge densities, fully integral-grounded.**  `t(C₅, 1−U) ≥ p⁵ − p(1−p)⁴`
(`p = 1 − q`, `q = ∫∫U`), with *only the integral definition of homomorphism density trusted*. -/
theorem C5_integral (hU : IsGraphon U μ) :
    tr μ (Kpow μ (Wk U) 4) ≥ (1 - qval U μ) ^ 5 - (1 - qval U μ) * qval U μ ^ 4 := by
  -- shorthand
  have hx1 : xden U μ 1 = qval U μ := xden_one hU
  have hx2 : xden U μ 2 = qval U μ ^ 2 + smom U μ 0 := xden_two hU
  have hx3 : xden U μ 3 = qval U μ ^ 3 + 2 * qval U μ * smom U μ 0 + smom U μ 1 := xden_three hU
  have hx4 : xden U μ 4 = qval U μ ^ 4 + 3 * qval U μ ^ 2 * smom U μ 0
      + 2 * qval U μ * smom U μ 1 + smom U μ 0 ^ 2 + smom U μ 2 := xden_four hU
  -- mean(vcomp k) and inner products, reduced to xden via the recursions
  have v1 : mean μ (vcomp U μ 1) = 1 - xden U μ 1 := by
    have h := pcomp_succ hU 0; rw [pcomp_zero, ip_vcomp_zero hU 1] at h; simpa using h
  have ip11 : ip μ (pathFun U μ 1) (vcomp U μ 1) = xden U μ 1 - xden U μ 2 := by
    have h := ip_vcomp_succ hU 1 0; rw [pcomp_zero, ip_vcomp_zero hU 2] at h; simpa using h
  have ip21 : ip μ (pathFun U μ 2) (vcomp U μ 1) = xden U μ 2 - xden U μ 3 := by
    have h := ip_vcomp_succ hU 2 0; rw [pcomp_zero, ip_vcomp_zero hU 3] at h; simpa using h
  have ip31 : ip μ (pathFun U μ 3) (vcomp U μ 1) = xden U μ 3 - xden U μ 4 := by
    have h := ip_vcomp_succ hU 3 0; rw [pcomp_zero, ip_vcomp_zero hU 4] at h; simpa using h
  have v2 : mean μ (vcomp U μ 2) = (1 - xden U μ 1) - (xden U μ 1 - xden U μ 2) := by
    have h := pcomp_succ hU 1; rw [v1, ip11] at h; simpa using h
  have ip12 : ip μ (pathFun U μ 1) (vcomp U μ 2)
      = mean μ (vcomp U μ 1) * xden U μ 1 - (xden U μ 2 - xden U μ 3) := by
    have h := ip_vcomp_succ hU 1 1; rw [ip21] at h; simpa using h
  have ip22 : ip μ (pathFun U μ 2) (vcomp U μ 2)
      = mean μ (vcomp U μ 1) * xden U μ 2 - (xden U μ 3 - xden U μ 4) := by
    have h := ip_vcomp_succ hU 2 1; rw [ip31] at h; simpa using h
  have v3 : mean μ (vcomp U μ 3) = mean μ (vcomp U μ 2) - ip μ (pathFun U μ 1) (vcomp U μ 2) := by
    have h := pcomp_succ hU 2; simpa using h
  have ip13 : ip μ (pathFun U μ 1) (vcomp U μ 3)
      = mean μ (vcomp U μ 2) * xden U μ 1 - ip μ (pathFun U μ 2) (vcomp U μ 2) := by
    have h := ip_vcomp_succ hU 1 2; simpa using h
  have v4 : mean μ (vcomp U μ 4) = mean μ (vcomp U μ 3) - ip μ (pathFun U μ 1) (vcomp U μ 3) := by
    have h := pcomp_succ hU 3; simpa using h
  have hed : tr μ (Kpow μ U 4) ≤ xden U μ 4 := edge_deletion_general hU 3
  have hcert := cert5_smom hU (qval U μ)
  rw [ccomp5_necklace hU, v4, v3, ip13, ip12, ip22, v2, ip31, v1, hx1, hx2, hx3, hx4]
  rw [hx4] at hed
  nlinarith [hcert, hed]

/-! ### C₇ -/

lemma qval_nonneg (hU : IsGraphon U μ) : 0 ≤ qval U μ :=
  integral_nonneg fun x => integral_nonneg fun y => hU.nonneg x y

lemma qval_le_one (hU : IsGraphon U μ) : qval U μ ≤ 1 := by
  rw [qval, mean]
  calc ∫ x, deg U μ x ∂μ ≤ ∫ _x, (1:ℝ) ∂μ := by
        refine integral_mono ((goodK_of_isGraphon hU).colsum_integrable.congr
          (ae_of_all _ fun x => by rw [deg]; exact integral_congr_ae (ae_of_all _ fun y => hU.symm y x)))
          (integrable_const 1) (fun x => ?_)
        rw [deg]
        calc ∫ y, U x y ∂μ ≤ ∫ _y, (1:ℝ) ∂μ :=
              integral_mono ((goodK_of_isGraphon hU).integrable_row x) (integrable_const 1)
                (fun y => hU.le_one x y)
          _ = 1 := by simp
    _ = 1 := by simp

/-- **The C₇ necklace identity.** -/
lemma ccomp7_necklace (hU : IsGraphon U μ) :
    tr μ (Kpow μ (Wk U) 6)
      = mean μ (vcomp U μ 6) - ip μ (pathFun U μ 1) (vcomp U μ 5)
        + ip μ (pathFun U μ 2) (vcomp U μ 4) - ip μ (pathFun U μ 3) (vcomp U μ 3)
        + ip μ (pathFun U μ 4) (vcomp U μ 2) - ip μ (pathFun U μ 5) (vcomp U μ 1)
        + xden U μ 6 - tr μ (Kpow μ U 6) := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, ccomp_peel hU 5, dmean_Wpow hU 5,
    Htr_succ hU 0 4, Htr_succ hU 1 3, Htr_succ hU 2 2, Htr_succ hU 3 1, Htr_succ hU 4 0,
    Htr_zero hU 5]
  ring

/-- **`C₇`, nontrivial regime `q ≤ ½`, fully integral-grounded.** -/
theorem C7_integral (hU : IsGraphon U μ) (hq : qval U μ ≤ 1 / 2) :
    tr μ (Kpow μ (Wk U) 6) ≥ (1 - qval U μ) ^ 7 - (1 - qval U μ) * qval U μ ^ 6 := by
  have hx1 : xden U μ 1 = qval U μ := xden_one hU
  have hx2 := xden_two hU; have hx3 := xden_three hU; have hx4 := xden_four hU
  have hx5 := xden_five hU; have hx6 := xden_six hU
  -- k = 1 inner products
  have ip11 : ip μ (pathFun U μ 1) (vcomp U μ 1) = xden U μ 1 - xden U μ 2 := by
    have h := ip_vcomp_succ hU 1 0; rw [pcomp_zero, ip_vcomp_zero hU 2] at h; simpa using h
  have ip21 : ip μ (pathFun U μ 2) (vcomp U μ 1) = xden U μ 2 - xden U μ 3 := by
    have h := ip_vcomp_succ hU 2 0; rw [pcomp_zero, ip_vcomp_zero hU 3] at h; simpa using h
  have ip31 : ip μ (pathFun U μ 3) (vcomp U μ 1) = xden U μ 3 - xden U μ 4 := by
    have h := ip_vcomp_succ hU 3 0; rw [pcomp_zero, ip_vcomp_zero hU 4] at h; simpa using h
  have ip41 : ip μ (pathFun U μ 4) (vcomp U μ 1) = xden U μ 4 - xden U μ 5 := by
    have h := ip_vcomp_succ hU 4 0; rw [pcomp_zero, ip_vcomp_zero hU 5] at h; simpa using h
  have ip51 : ip μ (pathFun U μ 5) (vcomp U μ 1) = xden U μ 5 - xden U μ 6 := by
    have h := ip_vcomp_succ hU 5 0; rw [pcomp_zero, ip_vcomp_zero hU 6] at h; simpa using h
  have v1 : mean μ (vcomp U μ 1) = 1 - xden U μ 1 := by
    have h := pcomp_succ hU 0; rw [pcomp_zero, ip_vcomp_zero hU 1] at h; simpa using h
  -- k = 2
  have ip12 : ip μ (pathFun U μ 1) (vcomp U μ 2)
      = mean μ (vcomp U μ 1) * xden U μ 1 - ip μ (pathFun U μ 2) (vcomp U μ 1) := by
    have h := ip_vcomp_succ hU 1 1; simpa using h
  have ip22 : ip μ (pathFun U μ 2) (vcomp U μ 2)
      = mean μ (vcomp U μ 1) * xden U μ 2 - ip μ (pathFun U μ 3) (vcomp U μ 1) := by
    have h := ip_vcomp_succ hU 2 1; simpa using h
  have ip32 : ip μ (pathFun U μ 3) (vcomp U μ 2)
      = mean μ (vcomp U μ 1) * xden U μ 3 - ip μ (pathFun U μ 4) (vcomp U μ 1) := by
    have h := ip_vcomp_succ hU 3 1; simpa using h
  have ip42 : ip μ (pathFun U μ 4) (vcomp U μ 2)
      = mean μ (vcomp U μ 1) * xden U μ 4 - ip μ (pathFun U μ 5) (vcomp U μ 1) := by
    have h := ip_vcomp_succ hU 4 1; simpa using h
  have v2 : mean μ (vcomp U μ 2) = mean μ (vcomp U μ 1) - ip μ (pathFun U μ 1) (vcomp U μ 1) := by
    have h := pcomp_succ hU 1; simpa using h
  -- k = 3
  have ip13 : ip μ (pathFun U μ 1) (vcomp U μ 3)
      = mean μ (vcomp U μ 2) * xden U μ 1 - ip μ (pathFun U μ 2) (vcomp U μ 2) := by
    have h := ip_vcomp_succ hU 1 2; simpa using h
  have ip23 : ip μ (pathFun U μ 2) (vcomp U μ 3)
      = mean μ (vcomp U μ 2) * xden U μ 2 - ip μ (pathFun U μ 3) (vcomp U μ 2) := by
    have h := ip_vcomp_succ hU 2 2; simpa using h
  have ip33 : ip μ (pathFun U μ 3) (vcomp U μ 3)
      = mean μ (vcomp U μ 2) * xden U μ 3 - ip μ (pathFun U μ 4) (vcomp U μ 2) := by
    have h := ip_vcomp_succ hU 3 2; simpa using h
  have v3 : mean μ (vcomp U μ 3) = mean μ (vcomp U μ 2) - ip μ (pathFun U μ 1) (vcomp U μ 2) := by
    have h := pcomp_succ hU 2; simpa using h
  -- k = 4
  have ip14 : ip μ (pathFun U μ 1) (vcomp U μ 4)
      = mean μ (vcomp U μ 3) * xden U μ 1 - ip μ (pathFun U μ 2) (vcomp U μ 3) := by
    have h := ip_vcomp_succ hU 1 3; simpa using h
  have ip24 : ip μ (pathFun U μ 2) (vcomp U μ 4)
      = mean μ (vcomp U μ 3) * xden U μ 2 - ip μ (pathFun U μ 3) (vcomp U μ 3) := by
    have h := ip_vcomp_succ hU 2 3; simpa using h
  have v4 : mean μ (vcomp U μ 4) = mean μ (vcomp U μ 3) - ip μ (pathFun U μ 1) (vcomp U μ 3) := by
    have h := pcomp_succ hU 3; simpa using h
  -- k = 5
  have ip15 : ip μ (pathFun U μ 1) (vcomp U μ 5)
      = mean μ (vcomp U μ 4) * xden U μ 1 - ip μ (pathFun U μ 2) (vcomp U μ 4) := by
    have h := ip_vcomp_succ hU 1 4; simpa using h
  have v5 : mean μ (vcomp U μ 5) = mean μ (vcomp U μ 4) - ip μ (pathFun U μ 1) (vcomp U μ 4) := by
    have h := pcomp_succ hU 4; simpa using h
  have v6 : mean μ (vcomp U μ 6) = mean μ (vcomp U μ 5) - ip μ (pathFun U μ 1) (vcomp U μ 5) := by
    have h := pcomp_succ hU 5; simpa using h
  have hed : tr μ (Kpow μ U 6) ≤ xden U μ 6 := edge_deletion_general hU 5
  have hcert := cert7_smom hU (qval U μ) (qval_nonneg hU) hq
  -- The necklace expands to `g₇ + Φ₇ + (x₆ − c₆)` as a pure polynomial identity (`ring`);
  -- `Φ₇ ≥ 0` (`hcert`) and `x₆ − c₆ ≥ 0` (`hed`) then finish by linear arithmetic.
  have key : tr μ (Kpow μ (Wk U) 6)
      = ((1 - qval U μ) ^ 7 - (1 - qval U μ) * qval U μ ^ 6)
        + (6 * smom U μ 4 + (12 * qval U μ - 7) * smom U μ 3
            + (18 * qval U μ ^ 2 - 21 * qval U μ + 7) * smom U μ 2
            + (24 * qval U μ ^ 3 - 42 * qval U μ ^ 2 + 28 * qval U μ - 7) * smom U μ 1
            + (30 * qval U μ ^ 4 - 70 * qval U μ ^ 3 + 70 * qval U μ ^ 2 - 35 * qval U μ + 7) * smom U μ 0
            + 12 * smom U μ 0 * smom U μ 2 + (36 * qval U μ - 21) * smom U μ 0 * smom U μ 1
            + (36 * qval U μ ^ 2 - 42 * qval U μ + 14) * (smom U μ 0) ^ 2 + 6 * (smom U μ 0) ^ 3
            + 6 * (smom U μ 1) ^ 2)
        + (xden U μ 6 - tr μ (Kpow μ U 6)) := by
    rw [ccomp7_necklace hU]
    simp only [v6, v5, v4, v3, v2, v1, ip15, ip24, ip14, ip33, ip23, ip13,
      ip42, ip32, ip22, ip12, ip51, ip41, ip31, ip21, ip11]
    rw [hx1, hx2, hx3, hx4, hx5, hx6]
    ring
  rw [key]
  linarith [hcert, hed]

/-- The complement kernel `Wk U = 1 − U` is itself a graphon. -/
lemma isGraphon_Wk (hU : IsGraphon U μ) : IsGraphon (Wk U) μ where
  meas := by
    have h : Function.uncurry (Wk U) = fun p : Ω × Ω => 1 - U p.1 p.2 := rfl
    rw [h]; exact measurable_const.sub hU.meas
  nonneg := fun x y => by rw [Wk]; linarith [hU.le_one x y]
  le_one := fun x y => by rw [Wk]; linarith [hU.nonneg x y]
  symm := fun x y => by rw [Wk, Wk, hU.symm x y]

/-- **`C₇` for all edge densities, fully integral-grounded.**  In the regime `q > ½` the bound
is trivial: `g₇ = (1−q)((1−q)⁶ − q⁶) ≤ 0 ≤ t(C₇, 1−U)`. -/
theorem C7_integral_all (hU : IsGraphon U μ) :
    tr μ (Kpow μ (Wk U) 6) ≥ (1 - qval U μ) ^ 7 - (1 - qval U μ) * qval U μ ^ 6 := by
  rcases le_total (qval U μ) (1 / 2) with hq | hq
  · exact C7_integral hU hq
  · have hcc : 0 ≤ tr μ (Kpow μ (Wk U) 6) := by
      rw [tr]; exact integral_nonneg fun x => Kpow_nonneg (isGraphon_Wk hU) 6 x x
    have h1 : 0 ≤ 1 - qval U μ := by linarith [qval_le_one hU]
    have hpow : (1 - qval U μ) ^ 6 ≤ qval U μ ^ 6 :=
      pow_le_pow_left₀ h1 (by linarith) 6
    have hg7 : (1 - qval U μ) ^ 7 - (1 - qval U μ) * qval U μ ^ 6 ≤ 0 := by
      nlinarith [mul_nonneg h1 (sub_nonneg.mpr hpow)]
    linarith [hcc, hg7]

end OddCycleBound.Graphon
