import OddCycleBound.Kernel
import OddCycleBound.IntegralCert

/-!
# Cycle densities, edge deletion, and the inclusion–exclusion bridge — Stage 4c/4d

Built on the kernel-composition algebra (`Kernel.lean`):

* `rowsum_Kpow` / `dmean_Kpow` — the path-density bridge `∫∫ Uᵒˡ = x_ℓ` (i.e. `dmean (Kpow U n) = xden (n+1)`);
* `Kpow_nonneg`, `cden` — the cycle density `c_m = tr (Kpow U (m−1))`;
* `edge_deletion_general` — `c_m ≤ x_{m−1}` for the actual `m`-cycle.

These reduce the remaining gap to the pure cyclic inclusion–exclusion expansion of
`tr (Kpow (1−U) (m−1))` into the `x_ℓ` and `c_m`.
-/

open MeasureTheory

namespace OddCycleBound.Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- The row-sum of `Kpow U n` is the path iterate `pathFun (n+1)`: `∫ y, Uᵒ⁽ⁿ⁺¹⁾(x,y) = (Tⁿ⁺¹1)(x)`. -/
lemma rowsum_Kpow (hU : IsGraphon U μ) : ∀ n,
    (fun x => ∫ y, Kpow μ U n x y ∂μ) = pathFun U μ (n + 1) := by
  have hGU : GoodK U := goodK_of_isGraphon hU
  intro n
  induction n with
  | zero =>
      funext x
      show ∫ y, U x y ∂μ = pathFun U μ 1 x
      have h1 : pathFun U μ 1 = deg U μ := by
        show T U μ (fun _ => 1) = deg U μ; exact T_one hU
      rw [h1]; rfl
  | succ k ih =>
      funext x
      show ∫ y, comp μ U (Kpow μ U k) x y ∂μ = pathFun U μ (k + 2) x
      obtain ⟨Ck, _, hCk⟩ := (goodK_Kpow (μ := μ) hGU k).bdd
      have hint : Integrable (Function.uncurry fun y z => U x z * Kpow μ U k z y) (μ.prod μ) := by
        have hSM : StronglyMeasurable (Function.uncurry fun y z => U x z * Kpow μ U k z y) := by
          have h1 : Measurable (fun p : Ω × Ω => U x p.2) :=
            hGU.meas.comp (measurable_const.prodMk measurable_snd)
          have h2 : Measurable (fun p : Ω × Ω => Kpow μ U k p.2 p.1) :=
            (goodK_Kpow (μ := μ) hGU k).meas.comp (measurable_snd.prodMk measurable_fst)
          exact (h1.mul h2).stronglyMeasurable
        refine (integrable_const (1 * Ck)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
        rintro ⟨y, z⟩
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by rw [abs_of_nonneg (hU.nonneg x z)]; exact hU.le_one x z) (hCk z y)
          (abs_nonneg _) (by norm_num)
      calc ∫ y, comp μ U (Kpow μ U k) x y ∂μ
          = ∫ y, ∫ z, U x z * Kpow μ U k z y ∂μ ∂μ := by simp only [comp]
        _ = ∫ z, ∫ y, U x z * Kpow μ U k z y ∂μ ∂μ := integral_integral_swap hint
        _ = ∫ z, U x z * (∫ y, Kpow μ U k z y ∂μ) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              show ∫ y, U x z * Kpow μ U k z y ∂μ = U x z * ∫ y, Kpow μ U k z y ∂μ
              rw [integral_const_mul]
        _ = ∫ z, U x z * pathFun U μ (k + 1) z ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              have ihz : ∫ y, Kpow μ U k z y ∂μ = pathFun U μ (k + 1) z := congrFun ih z
              show U x z * (∫ y, Kpow μ U k z y ∂μ) = U x z * pathFun U μ (k + 1) z
              rw [ihz]
        _ = pathFun U μ (k + 2) x := rfl

/-- The path-density bridge: `∫∫ Uᵒ⁽ⁿ⁺¹⁾ = x_{n+1}`. -/
lemma dmean_Kpow (hU : IsGraphon U μ) (n : ℕ) : dmean μ (Kpow μ U n) = xden U μ (n + 1) := by
  rw [dmean, show (fun x => ∫ y, Kpow μ U n x y ∂μ) = pathFun U μ (n + 1) from rowsum_Kpow hU n]
  rfl

lemma Kpow_nonneg (hU : IsGraphon U μ) : ∀ (n) (x y : Ω), 0 ≤ Kpow μ U n x y
  | 0, x, y => hU.nonneg x y
  | (n + 1), x, y => by
      show 0 ≤ comp μ U (Kpow μ U n) x y
      rw [comp]
      exact integral_nonneg fun z => mul_nonneg (hU.nonneg x z) (Kpow_nonneg hU n z y)

/-- The cycle density `c_m = t(C_m, U) = tr (Kpow U (m−1))`. -/
noncomputable def cden (μ : Measure Ω) (U : Ω → Ω → ℝ) (m : ℕ) : ℝ := tr μ (Kpow μ U (m - 1))

/-- **Edge deletion** for the actual cycle: `c_{k+2} ≤ x_{k+1}` (drop the closing edge `≤ 1`). -/
lemma edge_deletion_general (hU : IsGraphon U μ) (k : ℕ) :
    cden μ U (k + 2) ≤ xden U μ (k + 1) := by
  have hGU : GoodK U := goodK_of_isGraphon hU
  have hGK : GoodK (Kpow μ U k) := goodK_Kpow (μ := μ) hGU k
  obtain ⟨Ck, _, hCk⟩ := hGK.bdd
  have hintZ : ∀ x, Integrable (fun z => U x z * Kpow μ U k z x) μ := fun x => by
    have hm : Measurable (fun z => U x z * Kpow μ U k z x) :=
      (hGU.meas.comp measurable_prodMk_left).mul
        (hGK.meas.comp (measurable_id.prodMk measurable_const))
    refine (integrable_const Ck).mono' hm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU.nonneg x z)]
    calc U x z * |Kpow μ U k z x| ≤ 1 * Ck :=
          mul_le_mul (hU.le_one x z) (hCk z x) (abs_nonneg _) (by norm_num)
      _ = Ck := one_mul _
  have hintK : ∀ x, Integrable (fun z => Kpow μ U k z x) μ := fun x => hGK.integrable_col x
  have hswap : Integrable (Function.uncurry fun x z => Kpow μ U k z x) (μ.prod μ) := by
    have hm : Measurable (Function.uncurry fun x z => Kpow μ U k z x) :=
      hGK.meas.comp (measurable_snd.prodMk measurable_fst)
    refine (integrable_const Ck).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]; exact hCk p.2 p.1
  have key : cden μ U (k + 2) = ∫ x, ∫ z, U x z * Kpow μ U k z x ∂μ ∂μ := by
    simp only [cden, tr, Nat.add_sub_cancel]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show comp μ U (Kpow μ U k) x x = ∫ z, U x z * Kpow μ U k z x ∂μ
    rw [comp]
  rw [key]
  calc ∫ x, ∫ z, U x z * Kpow μ U k z x ∂μ ∂μ
      ≤ ∫ x, ∫ z, Kpow μ U k z x ∂μ ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hGK.colsum_integrable
          (ae_of_all _ fun x => ?_)
        · exact integral_nonneg fun z => mul_nonneg (hU.nonneg x z) (Kpow_nonneg hU k z x)
        · refine integral_mono (hintZ x) (hintK x) (fun z => ?_)
          calc U x z * Kpow μ U k z x ≤ 1 * Kpow μ U k z x :=
                mul_le_mul_of_nonneg_right (hU.le_one x z) (Kpow_nonneg hU k z x)
            _ = Kpow μ U k z x := one_mul _
    _ = ∫ z, ∫ x, Kpow μ U k z x ∂μ ∂μ := integral_integral_swap hswap
    _ = dmean μ (Kpow μ U k) := rfl
    _ = xden U μ (k + 1) := dmean_Kpow hU k

end OddCycleBound.Graphon
