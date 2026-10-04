import ApicesCommonness.Cycles.Foundation.Model.StepModel
import ApicesCommonness.Cycles.Foundation.Spectral.EigenSystem
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Trace bounds for real symmetric matrices

Blueprint `lem:finite-spectral`.  For a real symmetric `d × d` matrix `B` with eigenvalues `λᵢ`,
`Tr B^n = ∑ λᵢ^n`, and for every unit vector `g` (`g ⬝ᵥ g = 1`):

* `normSq_pow_le_trace_pow`:      `‖Bg‖^{2m} ≤ Tr B^{2m}`;
* `rayleigh_pow_le_trace_pow`:    `⟨g, Bg⟩^n ≤ Tr B^n` for even `n`;
* `trace_pow_le_trace_four_rpow`: `Tr B^n ≤ (Tr B⁴)^{n/4}` for even `n ≥ 4` (real exponent, D8).

In the eigenbasis `g` has coordinates `cᵢ` with `∑ cᵢ² = 1`, `⟨g, Bg⟩ = ∑ cᵢ² λᵢ` and
`‖Bg‖² = ∑ cᵢ² λᵢ²`; the first two bounds are the weighted power-mean inequality with weights `cᵢ²`
followed by `cᵢ² ≤ 1`, and the third is `∑ xᵢ^s ≤ (∑ xᵢ)^s` for `xᵢ = λᵢ⁴ ≥ 0`, `s = n/4 ≥ 1`
(`sum_rpow_le_rpow_sum`, the third part of `lem:moment-basics`).  The statements use plain
`dotProduct` and `mulVec`; the eigen-decomposition is the copied `EigenSystem` of the operator
`Matrix.toEuclideanLin B`.
-/

open Finset Matrix
open scoped RealInnerProductSpace

namespace ApicesCommonness

/-- **`lem:moment-basics`, third part.**  `∑ xᵢ^s ≤ (∑ xᵢ)^s` for `xᵢ ≥ 0` and real `s ≥ 1`. -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {p : ℝ} (hp : 1 ≤ p) : ∑ i ∈ s, x i ^ p ≤ (∑ i ∈ s, x i) ^ p := by
  set S := ∑ i ∈ s, x i with hS
  have hS0 : 0 ≤ S := sum_nonneg hx
  have hp0 : p ≠ 0 := by linarith
  rcases hS0.eq_or_lt with hS0' | hSpos
  · -- all terms vanish
    have hzero : ∀ i ∈ s, x i = 0 := (sum_eq_zero_iff_of_nonneg hx).mp hS0'.symm
    rw [← hS0', Real.zero_rpow hp0]
    exact (sum_eq_zero fun i hi => by rw [hzero i hi, Real.zero_rpow hp0]).le
  · have hterm : ∀ i ∈ s, x i ^ p / S ^ p ≤ x i / S := by
      intro i hi
      rw [← Real.div_rpow (hx i hi) hSpos.le]
      have h0 : 0 ≤ x i / S := div_nonneg (hx i hi) hSpos.le
      have h1 : x i / S ≤ 1 := by
        rw [div_le_one hSpos]
        exact single_le_sum hx hi
      exact Real.rpow_le_self_of_le_one h0 h1 hp
    have hsum : ∑ i ∈ s, x i ^ p / S ^ p ≤ 1 := by
      calc ∑ i ∈ s, x i ^ p / S ^ p ≤ ∑ i ∈ s, x i / S := sum_le_sum hterm
        _ = 1 := by rw [← sum_div, div_self hSpos.ne']
    have hSp : 0 < S ^ p := Real.rpow_pos_of_pos hSpos p
    rw [← sum_div, div_le_one hSp] at hsum
    exact hsum

variable {d : ℕ} {B : Matrix (Fin d) (Fin d) ℝ}

/-- The eigen-decomposition of a symmetric matrix, as an `EigenSystem` of its Euclidean operator. -/
noncomputable def eigenSystemOf (hB : B.IsHermitian) : EigenSystem d (Matrix.toEuclideanLin B) :=
  EigenSystem.ofSymmetric (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace_fin

/-- `Tr B^n = ∑ λᵢ^n`. -/
lemma trace_pow_eq_sum_eigen (hB : B.IsHermitian) (n : ℕ) :
    trace (B ^ n) = ∑ i, (eigenSystemOf hB).val i ^ n := by
  rw [← (eigenSystemOf hB).trace_pow_eq_sum n,
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    StepGraphon.toMatrix_pow]

/-- The coordinates of `g` in the eigenbasis. -/
noncomputable def eigenCoord (hB : B.IsHermitian) (g : Fin d → ℝ) (i : Fin d) : ℝ :=
  (eigenSystemOf hB).basis.repr (WithLp.toLp 2 g) i

lemma sum_eigenCoord_sq (hB : B.IsHermitian) (g : Fin d → ℝ) :
    ∑ i, eigenCoord hB g i ^ 2 = g ⬝ᵥ g := by
  unfold eigenCoord
  rw [← norm_sq_eq_sum (eigenSystemOf hB).basis, EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

lemma dot_mulVec_eq_sum_eigen (hB : B.IsHermitian) (g : Fin d → ℝ) :
    g ⬝ᵥ (B *ᵥ g) = ∑ i, (eigenSystemOf hB).val i * eigenCoord hB g i ^ 2 := by
  unfold eigenCoord
  rw [← (eigenSystemOf hB).inner_apply_eq_sum]
  change g ⬝ᵥ (B *ᵥ g) = (B *ᵥ g) ⬝ᵥ star g
  rw [star_trivial, dotProduct_comm]

lemma mulVec_dot_self_eq_sum_eigen (hB : B.IsHermitian) (g : Fin d → ℝ) :
    (B *ᵥ g) ⬝ᵥ (B *ᵥ g)
      = ∑ i, eigenCoord hB g i ^ 2 * ((eigenSystemOf hB).val i ^ 2) := by
  unfold eigenCoord
  have h := norm_sq_eq_sum (eigenSystemOf hB).basis
    (Matrix.toEuclideanLin B (WithLp.toLp 2 g))
  simp_rw [(eigenSystemOf hB).repr_apply] at h
  rw [EuclideanSpace.real_norm_sq_eq] at h
  have h' : ∑ i, (Matrix.toEuclideanLin B (WithLp.toLp 2 g)) i ^ 2 = (B *ᵥ g) ⬝ᵥ (B *ᵥ g) := by
    simp [dotProduct, sq, Matrix.toLin'_apply]
  rw [← h', h]
  refine sum_congr rfl fun i _ => by ring

/-- `cᵢ² ≤ 1` for a unit vector. -/
lemma eigenCoord_sq_le_one (hB : B.IsHermitian) {g : Fin d → ℝ} (hg : g ⬝ᵥ g = 1) (i : Fin d) :
    eigenCoord hB g i ^ 2 ≤ 1 := by
  rw [← hg, ← sum_eigenCoord_sq hB g]
  exact single_le_sum (f := fun j => eigenCoord hB g j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)

/-- **`lem:finite-spectral`: `‖Bg‖^{2m} ≤ Tr B^{2m}`** for a unit vector `g`. -/
theorem normSq_pow_le_trace_pow (hB : B.IsHermitian) {g : Fin d → ℝ} (hg : g ⬝ᵥ g = 1) (m : ℕ) :
    ((B *ᵥ g) ⬝ᵥ (B *ᵥ g)) ^ m ≤ trace (B ^ (2 * m)) := by
  set S := eigenSystemOf hB
  set c := eigenCoord hB g
  rw [mulVec_dot_self_eq_sum_eigen hB g, trace_pow_eq_sum_eigen hB]
  have hw : ∀ i ∈ (univ : Finset (Fin d)), 0 ≤ c i ^ 2 := fun i _ => sq_nonneg _
  have hw' : ∑ i, c i ^ 2 = 1 := by rw [sum_eigenCoord_sq hB g, hg]
  calc (∑ i, c i ^ 2 * S.val i ^ 2) ^ m ≤ ∑ i, c i ^ 2 * (S.val i ^ 2) ^ m :=
        Real.pow_arith_mean_le_arith_mean_pow univ _ _ hw hw' (fun i _ => sq_nonneg _) m
    _ ≤ ∑ i, (S.val i ^ 2) ^ m := by
        refine sum_le_sum fun i _ => ?_
        have := eigenCoord_sq_le_one hB hg i
        have h0 : 0 ≤ (S.val i ^ 2) ^ m := pow_nonneg (sq_nonneg _) m
        nlinarith
    _ = ∑ i, S.val i ^ (2 * m) := by simp_rw [pow_mul]

/-- **`lem:finite-spectral`: `⟨g, Bg⟩^n ≤ Tr B^n`** for even `n` and a unit vector `g`. -/
theorem rayleigh_pow_le_trace_pow (hB : B.IsHermitian) {g : Fin d → ℝ} (hg : g ⬝ᵥ g = 1)
    {n : ℕ} (hn : Even n) : (g ⬝ᵥ (B *ᵥ g)) ^ n ≤ trace (B ^ n) := by
  set S := eigenSystemOf hB
  set c := eigenCoord hB g
  rw [dot_mulVec_eq_sum_eigen hB g, trace_pow_eq_sum_eigen hB]
  have hw' : ∑ i, c i ^ 2 = 1 := by rw [sum_eigenCoord_sq hB g, hg]
  calc (∑ i, S.val i * c i ^ 2) ^ n = (∑ i, c i ^ 2 * S.val i) ^ n := by
        simp_rw [mul_comm (S.val _)]
    _ ≤ ∑ i, c i ^ 2 * S.val i ^ n :=
        Real.pow_arith_mean_le_arith_mean_pow_of_even univ _ _ (fun i _ => sq_nonneg _) hw' hn
    _ ≤ ∑ i, S.val i ^ n := by
        refine sum_le_sum fun i _ => ?_
        have := eigenCoord_sq_le_one hB hg i
        have h0 : 0 ≤ S.val i ^ n := hn.pow_nonneg _
        nlinarith

/-- For even `n`, `Tr B^n ≥ 0`. -/
lemma trace_pow_nonneg (hB : B.IsHermitian) {n : ℕ} (hn : Even n) : 0 ≤ trace (B ^ n) := by
  rw [trace_pow_eq_sum_eigen hB]
  exact sum_nonneg fun i _ => hn.pow_nonneg _

/-- **`lem:finite-spectral`: `Tr B^n ≤ (Tr B⁴)^{n/4}`** for even `n ≥ 4`. -/
theorem trace_pow_le_trace_four_rpow (hB : B.IsHermitian) {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    trace (B ^ n) ≤ trace (B ^ 4) ^ ((n : ℝ) / 4) := by
  set S := eigenSystemOf hB
  rw [trace_pow_eq_sum_eigen hB, trace_pow_eq_sum_eigen hB]
  have hpow : ∀ i, (S.val i ^ 4) ^ ((n : ℝ) / 4) = S.val i ^ n := by
    intro i
    have h4' : S.val i ^ 4 = |S.val i| ^ ((4 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, pow_abs, abs_of_nonneg (by positivity)]
    rw [h4', ← Real.rpow_mul (abs_nonneg _), show ((4 : ℕ) : ℝ) * ((n : ℝ) / 4) = (n : ℝ) by
      push_cast; ring, Real.rpow_natCast, hn.pow_abs]
  calc ∑ i, S.val i ^ n = ∑ i, (S.val i ^ 4) ^ ((n : ℝ) / 4) := by simp_rw [hpow]
    _ ≤ (∑ i, S.val i ^ 4) ^ ((n : ℝ) / 4) :=
        sum_rpow_le_rpow_sum univ _ (fun i _ => by positivity)
          (by rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]; exact_mod_cast (by omega : 1 * 4 ≤ n))

end ApicesCommonness
