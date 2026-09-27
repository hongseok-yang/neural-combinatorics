import EvenCycleApex.Host.Scalars

/-!
# Basic bounds on the scalar moments

Blueprint `lem:scalar-bounds`.  For every finite kernel:

* `abs_m_le_one`, `b_nonneg`, `b_le_one`, `a_le_b`: every `f(i)` is a weighted average of numbers
  in `[−1, 1]`; `a = m² ≤ b` is the weighted power-mean (Cauchy–Schwarz) inequality;
* `c_nonneg`, `c_le_one`: `c = ∑ λᵢ⁴ ≤ (∑ λᵢ²)² = (Tr T²)²` and
  `Tr T² = ∑ᵢⱼ wᵢ wⱼ U(i, j)² ≤ 1`;
* `r_nonneg`, `r_le_one`, `abs_eigen_le_r`: `r = c^{1/4}` bounds every eigenvalue of `T`, i.e.
  `‖T‖_op ≤ r`;
* `abs_p3_le`: `|p₃| ≤ b r`, since `p₃ = ⟨F, TF⟩` for `F = Tu`, `‖F‖² = b`;
* `c_eq_sum_cod_sq`: `c = ∑ᵢⱼ wᵢ wⱼ K(i, j)²`.

`basic_scalar_bounds` collects them in the blueprint's form, after complementation (`m ≥ 0`).
The blueprint's `c = 0 ⟺ U = 0` is used only for graphons (`lem:c-zero`, plan D9), not here.
-/

open Finset Matrix

namespace EvenCycleApex

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

lemma abs_m_le_one : |K.m| ≤ 1 := by
  calc |K.m| ≤ ∑ i, |K.w i * K.f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, K.w i := sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (K.w_nonneg i)]
        exact mul_le_of_le_one_right (K.w_nonneg i) (K.f_abs_le i)
    _ = 1 := K.w_sum

lemma b_nonneg : 0 ≤ K.b := sum_nonneg fun i _ => mul_nonneg (K.w_nonneg i) (sq_nonneg _)

lemma b_le_one : K.b ≤ 1 := by
  calc K.b ≤ ∑ i, K.w i := sum_le_sum fun i _ => by
        have h := K.f_abs_le i
        have h2 : K.f i ^ 2 ≤ 1 := by
          rw [← sq_abs]; nlinarith [abs_nonneg (K.f i)]
        exact mul_le_of_le_one_right (K.w_nonneg i) h2
    _ = 1 := K.w_sum

lemma a_nonneg : 0 ≤ K.a := sq_nonneg _

/-- `a = m² ≤ b`. -/
lemma a_le_b : K.a ≤ K.b :=
  Real.pow_arith_mean_le_arith_mean_pow_of_even univ K.w K.f (fun i _ => K.w_nonneg i) K.w_sum
    even_two

/-! ### Spectral bounds -/

/-- The eigenvalues of `T`. -/
noncomputable def eig : Fin d → ℝ := (eigenSystemOf K.T_isHermitian).val

lemma c_eq_sum_eig : K.c = ∑ i, K.eig i ^ 4 := by
  rw [c_eq_trace, trace_pow_eq_sum_eigen K.T_isHermitian]
  rfl

lemma c_nonneg : 0 ≤ K.c := by
  rw [c_eq_sum_eig]
  exact sum_nonneg fun i _ => by positivity

/-- `Tr T² = ∑ᵢⱼ wᵢ wⱼ U(i, j)² ≤ 1`. -/
lemma trace_T_sq_le_one : trace (K.T ^ 2) ≤ 1 := by
  have hT : trace (K.T ^ 2) = ∑ i, ∑ j, K.w i * K.w j * K.U i j ^ 2 := by
    rw [sq, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, T, hostMatrix_apply]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have hi := Real.mul_self_sqrt (K.w_nonneg i)
    have hj := Real.mul_self_sqrt (K.w_nonneg j)
    rw [K.U_symm j i]
    calc K.U i j * Real.sqrt (K.w i) * Real.sqrt (K.w j) *
          (K.U i j * Real.sqrt (K.w j) * Real.sqrt (K.w i))
        = (Real.sqrt (K.w i) * Real.sqrt (K.w i)) * (Real.sqrt (K.w j) * Real.sqrt (K.w j)) *
            (K.U i j * K.U i j) := by ring
      _ = K.w i * K.w j * K.U i j ^ 2 := by rw [hi, hj]; ring
  rw [hT]
  calc ∑ i, ∑ j, K.w i * K.w j * K.U i j ^ 2 ≤ ∑ i, ∑ j, K.w i * K.w j :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => by
          have h := K.U_abs_le i j
          have h2 : K.U i j ^ 2 ≤ 1 := by
            rw [← sq_abs]; nlinarith [abs_nonneg (K.U i j)]
          exact mul_le_of_le_one_right (mul_nonneg (K.w_nonneg i) (K.w_nonneg j)) h2
    _ = 1 := by simp only [← mul_sum, K.w_sum, mul_one]

lemma c_le_one : K.c ≤ 1 := by
  have h2 : trace (K.T ^ 2) = ∑ i, K.eig i ^ 2 := by
    rw [trace_pow_eq_sum_eigen K.T_isHermitian]; rfl
  have hsq : ∑ i, (K.eig i ^ 2) ^ 2 ≤ (∑ i, K.eig i ^ 2) ^ 2 := by
    rw [sq (∑ i, K.eig i ^ 2), sum_mul]
    refine sum_le_sum fun i _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left
      (single_le_sum (f := fun j => K.eig j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i))
      (sq_nonneg _)
  have htr := K.trace_T_sq_le_one
  have htr0 : 0 ≤ trace (K.T ^ 2) := trace_pow_nonneg K.T_isHermitian even_two
  rw [c_eq_sum_eig]
  calc ∑ i, K.eig i ^ 4 = ∑ i, (K.eig i ^ 2) ^ 2 := by simp_rw [← pow_mul]
    _ ≤ (∑ i, K.eig i ^ 2) ^ 2 := hsq
    _ = trace (K.T ^ 2) ^ 2 := by rw [h2]
    _ ≤ 1 := by nlinarith

lemma r_nonneg : 0 ≤ K.r := Real.rpow_nonneg K.c_nonneg _

lemma r_le_one : K.r ≤ 1 := Real.rpow_le_one K.c_nonneg K.c_le_one (by norm_num)

/-- Every eigenvalue of `T` is at most `r` in absolute value: `‖T‖_op ≤ r`. -/
lemma abs_eigen_le_r (i : Fin d) : |K.eig i| ≤ K.r := by
  have h4 : K.eig i ^ 4 ≤ K.c := by
    rw [c_eq_sum_eig]
    exact single_le_sum (f := fun j => K.eig j ^ 4) (fun j _ => by positivity) (mem_univ i)
  have habs : |K.eig i| = (|K.eig i| ^ 4) ^ (((4 : ℕ) : ℝ)⁻¹) :=
    (Real.pow_rpow_inv_natCast (abs_nonneg _) (by norm_num)).symm
  rw [habs, r, show ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  rw [pow_abs, abs_of_nonneg (by positivity)]
  exact h4

/-! ### `|p₃| ≤ b r` -/

/-- `F = T u`, the image of the degree function `f`: `Fᵢ = √wᵢ f(i)`. -/
noncomputable def degVec : Fin d → ℝ := K.T *ᵥ hostUnit K.w

lemma degVec_apply (i : Fin d) : K.degVec i = Real.sqrt (K.w i) * K.f i := by
  simp only [degVec, mulVec, dotProduct, T, hostMatrix_apply, hostUnit, f, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_assoc (K.U i j * _), Real.mul_self_sqrt (K.w_nonneg j)]
  ring

lemma degVec_dot_self : K.degVec ⬝ᵥ K.degVec = K.b := by
  simp only [dotProduct, degVec_apply, b]
  refine sum_congr rfl fun i _ => ?_
  have := Real.mul_self_sqrt (K.w_nonneg i)
  calc Real.sqrt (K.w i) * K.f i * (Real.sqrt (K.w i) * K.f i)
      = (Real.sqrt (K.w i) * Real.sqrt (K.w i)) * K.f i ^ 2 := by ring
    _ = K.w i * K.f i ^ 2 := by rw [this]

/-- `p₃ = ∑ⱼₖ wⱼ wₖ f(j) U(j, k) f(k)`: sum out the two end vertices of the path. -/
lemma p3_eq_sum_f : K.p3 = ∑ j, ∑ k, K.w j * K.w k * (K.f j * K.U j k * K.f k) := by
  unfold p3
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  simp only [f, sum_mul, mul_sum]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
  rw [K.U_symm i j]
  ring

lemma degVec_rayleigh : K.degVec ⬝ᵥ (K.T *ᵥ K.degVec) = K.p3 := by
  rw [p3_eq_sum_f]
  simp only [dotProduct, mulVec, degVec_apply, T, hostMatrix_apply, mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  have hj := Real.mul_self_sqrt (K.w_nonneg j)
  have hk := Real.mul_self_sqrt (K.w_nonneg k)
  calc Real.sqrt (K.w j) * K.f j *
        (K.U j k * Real.sqrt (K.w j) * Real.sqrt (K.w k) * (Real.sqrt (K.w k) * K.f k))
      = (Real.sqrt (K.w j) * Real.sqrt (K.w j)) * (Real.sqrt (K.w k) * Real.sqrt (K.w k)) *
          (K.f j * K.U j k * K.f k) := by ring
    _ = K.w j * K.w k * (K.f j * K.U j k * K.f k) := by rw [hj, hk]

/-- `|p₃| ≤ b r`. -/
lemma abs_p3_le : |K.p3| ≤ K.b * K.r := by
  have hB := K.T_isHermitian
  rw [← K.degVec_rayleigh, dot_mulVec_eq_sum_eigen hB, ← K.degVec_dot_self,
    ← sum_eigenCoord_sq hB K.degVec, sum_mul]
  calc |∑ i, (eigenSystemOf hB).val i * eigenCoord hB K.degVec i ^ 2|
      ≤ ∑ i, |(eigenSystemOf hB).val i * eigenCoord hB K.degVec i ^ 2| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, eigenCoord hB K.degVec i ^ 2 * K.r := sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (eigenCoord hB K.degVec i)), mul_comm]
        exact mul_le_mul_of_nonneg_left (K.abs_eigen_le_r i) (sq_nonneg _)

/-! ### `c` as a codegree square sum -/

/-- `c = ∑ᵢⱼ wᵢ wⱼ K(i, j)²`: split the four-cycle at two opposite vertices. -/
lemma c_eq_sum_cod_sq : K.c = ∑ i, ∑ k, K.w i * K.w k * K.cod i k ^ 2 := by
  unfold c
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  simp only [cod, sq, sum_mul, mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
  rw [K.U_symm j k, K.U_symm l i]
  ring

/-- **`lem:scalar-bounds`** (after complementation, `m ≥ 0`). -/
theorem basic_scalar_bounds (hm : 0 ≤ K.m) :
    0 ≤ K.m ∧ K.m ≤ 1 ∧ 0 ≤ K.a ∧ K.a ≤ K.b ∧ K.b ≤ 1 ∧ 0 ≤ K.c ∧ K.c ≤ 1 ∧
      0 ≤ K.r ∧ K.r ≤ 1 ∧ (∀ i, |K.eig i| ≤ K.r) ∧ |K.p3| ≤ K.b * K.r ∧
      K.c = ∑ i, ∑ k, K.w i * K.w k * K.cod i k ^ 2 :=
  ⟨hm, (abs_le.mp K.abs_m_le_one).2, K.a_nonneg, K.a_le_b, K.b_le_one, K.c_nonneg, K.c_le_one,
    K.r_nonneg, K.r_le_one, K.abs_eigen_le_r, K.abs_p3_le, K.c_eq_sum_cod_sq⟩

end FiniteKernel

end EvenCycleApex
