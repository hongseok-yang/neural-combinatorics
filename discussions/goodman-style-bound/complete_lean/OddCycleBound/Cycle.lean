import OddCycleBound.Kernel
import OddCycleBound.MomentSOS

/-!
# Cycle densities, edge deletion, and the inclusion–exclusion bridge

Built on the kernel-composition algebra (`Kernel.lean`):

* `rowsum_compPow` / `doubleMean_compPow` — the path-density bridge `∫∫ Uᵒˡ = x_ℓ` (i.e. `doubleMean (compPow U n) = pathDensity (n+1)`);
* `compPow_nonneg`, `cycleDensity` — the cycle density `c_m = trace (compPow U (m−1))`;
* `edge_deletion_general` — `c_m ≤ x_{m−1}` for the actual `m`-cycle.

These reduce the remaining gap to the pure cyclic inclusion–exclusion expansion of
`trace (compPow (1−U) (m−1))` into the `x_ℓ` and `c_m`.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- The row-sum of `compPow U n` is the path iterate `pathIter (n+1)`: `∫ y, Uᵒ⁽ⁿ⁺¹⁾(x,y) = (kernelOpⁿ⁺¹1)(x)`. -/
lemma rowsum_compPow (hU : IsGraphon U μ) : ∀ n,
    (fun x => ∫ y, compPow μ U n x y ∂μ) = pathIter U μ (n + 1) := by
  have hGU : GoodK U := goodK_of_isGraphon hU
  intro n
  induction n with
  | zero =>
      funext x
      show ∫ y, U x y ∂μ = pathIter U μ 1 x
      have h1 : pathIter U μ 1 = degree U μ := by
        show kernelOp U μ (fun _ => 1) = degree U μ; exact kernelOp_one hU
      rw [h1]; rfl
  | succ k ih =>
      funext x
      show ∫ y, comp μ U (compPow μ U k) x y ∂μ = pathIter U μ (k + 2) x
      obtain ⟨Ck, _, hCk⟩ := (goodK_compPow (μ := μ) hGU k).bdd
      have hint : Integrable (Function.uncurry fun y z => U x z * compPow μ U k z y) (μ.prod μ) := by
        have hSM : StronglyMeasurable (Function.uncurry fun y z => U x z * compPow μ U k z y) := by
          have h1 : Measurable (fun p : Ω × Ω => U x p.2) :=
            hGU.meas.comp (measurable_const.prodMk measurable_snd)
          have h2 : Measurable (fun p : Ω × Ω => compPow μ U k p.2 p.1) :=
            (goodK_compPow (μ := μ) hGU k).meas.comp (measurable_snd.prodMk measurable_fst)
          exact (h1.mul h2).stronglyMeasurable
        refine (integrable_const (1 * Ck)).mono' hSM.aestronglyMeasurable (ae_of_all _ ?_)
        rintro ⟨y, z⟩
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by rw [abs_of_nonneg (hU.nonneg x z)]; exact hU.le_one x z) (hCk z y)
          (abs_nonneg _) (by norm_num)
      calc ∫ y, comp μ U (compPow μ U k) x y ∂μ
          = ∫ y, ∫ z, U x z * compPow μ U k z y ∂μ ∂μ := by simp only [comp]
        _ = ∫ z, ∫ y, U x z * compPow μ U k z y ∂μ ∂μ := integral_integral_swap hint
        _ = ∫ z, U x z * (∫ y, compPow μ U k z y ∂μ) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              show ∫ y, U x z * compPow μ U k z y ∂μ = U x z * ∫ y, compPow μ U k z y ∂μ
              rw [integral_const_mul]
        _ = ∫ z, U x z * pathIter U μ (k + 1) z ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun z => ?_)
              have ihz : ∫ y, compPow μ U k z y ∂μ = pathIter U μ (k + 1) z := congrFun ih z
              show U x z * (∫ y, compPow μ U k z y ∂μ) = U x z * pathIter U μ (k + 1) z
              rw [ihz]
        _ = pathIter U μ (k + 2) x := rfl

/-- The path-density bridge: `∫∫ Uᵒ⁽ⁿ⁺¹⁾ = x_{n+1}`. -/
lemma doubleMean_compPow (hU : IsGraphon U μ) (n : ℕ) : doubleMean μ (compPow μ U n) = pathDensity U μ (n + 1) := by
  rw [doubleMean, show (fun x => ∫ y, compPow μ U n x y ∂μ) = pathIter U μ (n + 1) from rowsum_compPow hU n]
  rfl

lemma compPow_nonneg (hU : IsGraphon U μ) : ∀ (n) (x y : Ω), 0 ≤ compPow μ U n x y
  | 0, x, y => hU.nonneg x y
  | (n + 1), x, y => by
      show 0 ≤ comp μ U (compPow μ U n) x y
      rw [comp]
      exact integral_nonneg fun z => mul_nonneg (hU.nonneg x z) (compPow_nonneg hU n z y)

/-- The cycle density `c_m = t(C_m, U) = trace (compPow U (m−1))`. -/
noncomputable def cycleDensity (μ : Measure Ω) (U : Ω → Ω → ℝ) (m : ℕ) : ℝ := trace μ (compPow μ U (m - 1))

/-- **Edge deletion** for the actual cycle: `c_{k+2} ≤ x_{k+1}` (drop the closing edge `≤ 1`). -/
lemma edge_deletion_general (hU : IsGraphon U μ) (k : ℕ) :
    cycleDensity μ U (k + 2) ≤ pathDensity U μ (k + 1) := by
  have hGU : GoodK U := goodK_of_isGraphon hU
  have hGK : GoodK (compPow μ U k) := goodK_compPow (μ := μ) hGU k
  obtain ⟨Ck, _, hCk⟩ := hGK.bdd
  have hintZ : ∀ x, Integrable (fun z => U x z * compPow μ U k z x) μ := fun x => by
    have hm : Measurable (fun z => U x z * compPow μ U k z x) :=
      (hGU.meas.comp measurable_prodMk_left).mul
        (hGK.meas.comp (measurable_id.prodMk measurable_const))
    refine (integrable_const Ck).mono' hm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU.nonneg x z)]
    calc U x z * |compPow μ U k z x| ≤ 1 * Ck :=
          mul_le_mul (hU.le_one x z) (hCk z x) (abs_nonneg _) (by norm_num)
      _ = Ck := one_mul _
  have hintK : ∀ x, Integrable (fun z => compPow μ U k z x) μ := fun x => hGK.integrable_col x
  have hswap : Integrable (Function.uncurry fun x z => compPow μ U k z x) (μ.prod μ) := by
    have hm : Measurable (Function.uncurry fun x z => compPow μ U k z x) :=
      hGK.meas.comp (measurable_snd.prodMk measurable_fst)
    refine (integrable_const Ck).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]; exact hCk p.2 p.1
  have key : cycleDensity μ U (k + 2) = ∫ x, ∫ z, U x z * compPow μ U k z x ∂μ ∂μ := by
    simp only [cycleDensity, trace, Nat.add_sub_cancel]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show comp μ U (compPow μ U k) x x = ∫ z, U x z * compPow μ U k z x ∂μ
    rw [comp]
  rw [key]
  calc ∫ x, ∫ z, U x z * compPow μ U k z x ∂μ ∂μ
      ≤ ∫ x, ∫ z, compPow μ U k z x ∂μ ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hGK.colsum_integrable
          (ae_of_all _ fun x => ?_)
        · exact integral_nonneg fun z => mul_nonneg (hU.nonneg x z) (compPow_nonneg hU k z x)
        · refine integral_mono (hintZ x) (hintK x) (fun z => ?_)
          calc U x z * compPow μ U k z x ≤ 1 * compPow μ U k z x :=
                mul_le_mul_of_nonneg_right (hU.le_one x z) (compPow_nonneg hU k z x)
            _ = compPow μ U k z x := one_mul _
    _ = ∫ z, ∫ x, compPow μ U k z x ∂μ ∂μ := integral_integral_swap hswap
    _ = doubleMean μ (compPow μ U k) := rfl
    _ = pathDensity U μ (k + 1) := doubleMean_compPow hU k

end OddCycleBound
