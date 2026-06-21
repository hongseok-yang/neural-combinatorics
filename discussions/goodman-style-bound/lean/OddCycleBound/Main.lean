import OddCycleBound.Necklace
import OddCycleBound.C9

/-!
# Main results: the odd-cycle Goodman-type bound for a graphon `W`

For a graphon `W` over a probability space `(Ω, μ)` with edge density `p = ∫∫ W`,

* `C5_bound` : `t(C₅, W) ≥ p⁵ − p(1−p)⁴`,
* `C7_bound` : `t(C₇, W) ≥ p⁷ − p(1−p)⁶`,

both for **all** edge densities `p`, and

* `C9_path_bound` : `t(C₉, W) ≥ p⁹ − p(1−p)⁸` for `p ≥ 1003/2000` (the path-certificate range).

Here the homomorphism density `t(C_m, W)` is the cyclic trace `tr μ (Kpow μ W (m−1))` and
`p = qval W μ = ∫∫ W`, all defined as plain integrals.

These are the `W`-facing restatements of `C5_integral` / `C7_integral_all` / `C9_path_integral`
(which are phrased for the complement `U = 1 − W`).  The only trusted input remains the integral
definition of the homomorphism density.  The `C₉` proof additionally goes through the bivariate
sum-of-squares certificate `cert9_Q`; it is still axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open MeasureTheory

namespace OddCycleBound.Graphon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The complement of the complement is the original kernel. -/
private lemma Wk_Wk (W : Ω → Ω → ℝ) : Wk (Wk W) = W := by
  funext x y; simp only [Wk]; ring

/-- Edge density of the complement: `∫∫(1−W) = 1 − ∫∫W`. -/
private lemma qval_Wk (hW : IsGraphon W μ) : qval (Wk W) μ = 1 - qval W μ := by
  have hGW : GoodK W := goodK_of_isGraphon hW
  have hdegint : Integrable (deg W μ) μ :=
    hGW.colsum_integrable.congr (ae_of_all _ fun x => by
      rw [deg]; exact integral_congr_ae (ae_of_all _ fun y => hW.symm y x))
  have hone : (∫ _x : Ω, (1 : ℝ) ∂μ) = 1 := by simp
  have hdeg : ∀ x, deg (Wk W) μ x = 1 - deg W μ x := fun x => by
    show (∫ y, Wk W x y ∂μ) = 1 - deg W μ x
    have hwk : (fun y => Wk W x y) = fun y => (1 : ℝ) - W x y := rfl
    rw [hwk, integral_sub (integrable_const 1) (hGW.integrable_row x), hone, deg]
  show (∫ x, deg (Wk W) μ x ∂μ) = 1 - qval W μ
  rw [integral_congr_ae (ae_of_all _ hdeg), integral_sub (integrable_const 1) hdegint, hone]
  rfl

/-- **`C₅` Goodman-type bound.**  `t(C₅, W) ≥ p⁵ − p(1−p)⁴`, with `p = ∫∫W`, for all densities. -/
theorem C5_bound (hW : IsGraphon W μ) :
    tr μ (Kpow μ W 4) ≥ qval W μ ^ 5 - qval W μ * (1 - qval W μ) ^ 4 := by
  have h := C5_integral (isGraphon_Wk hW)
  rw [Wk_Wk, qval_Wk hW] at h
  have e : 1 - (1 - qval W μ) = qval W μ := by ring
  rw [e] at h
  exact h

/-- **`C₇` Goodman-type bound.**  `t(C₇, W) ≥ p⁷ − p(1−p)⁶`, with `p = ∫∫W`, for all densities. -/
theorem C7_bound (hW : IsGraphon W μ) :
    tr μ (Kpow μ W 6) ≥ qval W μ ^ 7 - qval W μ * (1 - qval W μ) ^ 6 := by
  have h := C7_integral_all (isGraphon_Wk hW)
  rw [Wk_Wk, qval_Wk hW] at h
  have e : 1 - (1 - qval W μ) = qval W μ := by ring
  rw [e] at h
  exact h

/-- **`C₉` path-certificate bound.**  `t(C₉, W) ≥ p⁹ − p(1−p)⁸`, with `p = ∫∫W`, for every
graphon `W` with edge density `p ≥ 1003/2000`.  (The complement edge density is then
`q = 1 − p ≤ 997/2000`, the path-certificate range of §6.1.) -/
theorem C9_path_bound (hW : IsGraphon W μ) (hp : 1003 / 2000 ≤ qval W μ) :
    tr μ (Kpow μ W 8) ≥ qval W μ ^ 9 - qval W μ * (1 - qval W μ) ^ 8 := by
  have hq : qval (Wk W) μ ≤ 997 / 2000 := by rw [qval_Wk hW]; linarith
  have h := C9_path_integral (isGraphon_Wk hW) hq
  rw [Wk_Wk, qval_Wk hW] at h
  have e : 1 - (1 - qval W μ) = qval W μ := by ring
  rw [e] at h
  exact h

end OddCycleBound.Graphon
