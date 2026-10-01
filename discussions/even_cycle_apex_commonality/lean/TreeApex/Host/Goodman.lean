import TreeApex.Host.Double

/-!
# Goodman's identity on a host (paper `lem:goodman`)

Plan T-D9.  With `σ = m(P₃) = t(P₃, M) + t(P₃, 1 − M)` and `τ = m(K₃)`:

* `Mh_K₂`: `m(K₂) = 1`;
* `sigma_eq`: `σ = 1 − 2E + 2D`, hence `half_le_sigma`: `σ ≥ 1/2` (`σ − 1/2 = 2 ∑ w (deg − 1/2)²`);
* `tau_eq`: `τ = 1 − 3E + 3D` (expand `(1−a)(1−b)(1−c) + abc` under the triple sum; each linear
  term sums to `E` and each quadratic term to `D`), hence `host_goodman_identity`:
  `τ = (3/2) σ − 1/2`.
-/

open Finset SimpleGraph

namespace TreeApex

namespace ProbHost

variable {V : Type*} [Fintype V] (K : ProbHost V)

/-! ### Triple sums -/

omit K in
lemma sum3_add (f g : V → V → V → ℝ) :
    ∑ x, ∑ y, ∑ z, f x y z + ∑ x, ∑ y, ∑ z, g x y z = ∑ x, ∑ y, ∑ z, (f x y z + g x y z) := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun y _ => (sum_add_distrib).symm

lemma sum3_one : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z = 1 := by
  simp only [← mul_sum, K.w_sum, mul_one]

lemma sum3_xy : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z * K.M x y = K.E := by
  rw [E_eq_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [show ∑ z, K.w x * K.w y * K.w z * K.M x y = K.w x * K.w y * K.M x y * ∑ z, K.w z by
    rw [mul_sum]; exact sum_congr rfl fun z _ => by ring, K.w_sum, mul_one]

lemma sum3_xz : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z * K.M x z = K.E := by
  rw [← K.sum3_xy]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun z _ => sum_congr rfl fun y _ => by ring

lemma sum3_yz : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z * K.M y z = K.E := by
  rw [← K.sum3_xy, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun z _ => sum_congr rfl fun x _ => by ring

lemma sum3_xy_xz : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z * (K.M x y * K.M x z) = K.D := by
  simp only [D, deg, sq, mul_sum, sum_mul]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => by ring

lemma sum3_xy_yz : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z * (K.M x y * K.M y z) = K.D := by
  rw [← K.hostDens_P₃_eq, hostDens_P₃]

lemma sum3_xz_yz : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z * (K.M x z * K.M y z) = K.D := by
  rw [← K.sum3_xy_yz]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun z _ => sum_congr rfl fun y _ => ?_
  rw [K.M_symm y z]
  ring

lemma sum3_xyz : ∑ x, ∑ y, ∑ z, K.w x * K.w y * K.w z * (K.M x y * (K.M x z * K.M y z)) = K.R := by
  rw [← K.hostDens_K₃_eq, hostDens_K₃]

/-! ### Goodman -/

lemma Mh_K₂ : K.Mh (⊤ : SimpleGraph (Fin 2)) = 1 := by
  rw [Mh, hostDens_K₂, hostDens_K₂, ← sum_add_distrib]
  simp only [← sum_add_distrib, Mc]
  simp only [show ∀ x y, K.w x * K.w y * K.M x y + K.w x * K.w y * (1 - K.M x y) = K.w x * K.w y
    from fun x y => by ring, ← mul_sum, K.w_sum, mul_one]

/-- `σ = 1 − 2E + 2D`. -/
lemma sigma_eq : K.Mh (pathGraph 3) = 1 - 2 * K.E + 2 * K.D := by
  have key : ∀ x y z, K.w x * K.w y * K.w z * (K.M x y * K.M y z)
      + K.w x * K.w y * K.w z * (K.Mc x y * K.Mc y z)
      = K.w x * K.w y * K.w z - K.w x * K.w y * K.w z * K.M x y
        - K.w x * K.w y * K.w z * K.M y z + K.w x * K.w y * K.w z * (K.M x y * K.M y z)
        + K.w x * K.w y * K.w z * (K.M x y * K.M y z) :=
    fun x y z => by simp only [Mc]; ring
  rw [Mh, hostDens_P₃, hostDens_P₃, sum3_add]
  simp only [key, sum_add_distrib, sum_sub_distrib]
  rw [K.sum3_one, K.sum3_xy, K.sum3_yz, K.sum3_xy_yz]
  ring

/-- `τ = 1 − 3E + 3D`. -/
lemma tau_eq : K.Mh (⊤ : SimpleGraph (Fin 3)) = 1 - 3 * K.E + 3 * K.D := by
  have key : ∀ x y z, K.w x * K.w y * K.w z * (K.M x y * (K.M x z * K.M y z))
      + K.w x * K.w y * K.w z * (K.Mc x y * (K.Mc x z * K.Mc y z))
      = K.w x * K.w y * K.w z - K.w x * K.w y * K.w z * K.M x y
        - K.w x * K.w y * K.w z * K.M x z - K.w x * K.w y * K.w z * K.M y z
        + K.w x * K.w y * K.w z * (K.M x y * K.M x z)
        + K.w x * K.w y * K.w z * (K.M x y * K.M y z)
        + K.w x * K.w y * K.w z * (K.M x z * K.M y z) :=
    fun x y z => by simp only [Mc]; ring
  rw [Mh, hostDens_K₃, hostDens_K₃, sum3_add]
  simp only [key, sum_add_distrib, sum_sub_distrib]
  rw [K.sum3_one, K.sum3_xy, K.sum3_xz, K.sum3_yz, K.sum3_xy_xz, K.sum3_xy_yz, K.sum3_xz_yz]
  ring

/-- **`lem:goodman`, first part** (host): `σ ≥ 1/2`. -/
theorem host_half_le_sigma : 1 / 2 ≤ K.Mh (pathGraph 3) := by
  rw [sigma_eq]
  have h : 0 ≤ ∑ x, K.w x * (K.deg x - 1 / 2) ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (K.w_nonneg x) (sq_nonneg _)
  have h' : ∑ x, K.w x * (K.deg x - 1 / 2) ^ 2 = K.D - K.E + 1 / 4 := by
    simp only [D, E, show ∀ x, K.w x * (K.deg x - 1 / 2) ^ 2
      = K.w x * K.deg x ^ 2 - K.w x * K.deg x + K.w x / 4 from fun x => by ring,
      sum_add_distrib, sum_sub_distrib, ← sum_div, K.w_sum]
  linarith

/-- **Goodman's identity** (host): `τ = (3/2) σ − 1/2`. -/
theorem host_goodman_identity :
    K.Mh (⊤ : SimpleGraph (Fin 3)) = 3 / 2 * K.Mh (pathGraph 3) - 1 / 2 := by
  rw [tau_eq, sigma_eq]
  ring

end ProbHost

end TreeApex
