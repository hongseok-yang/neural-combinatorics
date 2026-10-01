import TreeApex.Entropy.RelEnt
import TreeApex.Host.ProbHost

/-!
# The random triangle (paper `sec:finite`, `lem:triangle`), weighted

Plan §2.4.  On a host with `R > 0` the uniform ordered triangle becomes the law
`P(x,y,z) = w_x w_y w_z M_xy M_yz M_xz / R`; only two of its marginals are needed:

```
  P₂(x, y) = w_x w_y M_xy cod(x,y) / R            (the pair (X, Y)),
  P₁(x)    = w_x tri(x) / R                        (the vertex X).
```

With `h = ∑ P₂ log cod` (the weighted `H(Z | X, Y)`) and `A = ∑ P₁ log tri`, the paper's
`I = I(Y; Z | X)` is `A − 2h`, and `eq:triangle-bounds` reads

* `h_ge` (**T1**): `h ≥ log R − log E`;
* `I_le` (**T2**): `A − 2h ≤ log D − log R`.

Both are Gibbs' inequality (`relEnt_le_log_sum`): T1 against the reference `w_x w_y M_xy` (total
`E`), T2 in two steps, against `w_x tri(x) w_y M_xy / (R deg(x))` on pairs (a law) and against
`w_x deg(x)² / R` on vertices (total `D / R`).  The second step replaces the paper's concavity of
`log`, and the first its `H(Y | X = x) ≤ log d(x)`.
-/

open Finset

namespace TreeApex

namespace ProbHost

variable {V : Type*} [Fintype V] (K : ProbHost V)

/-- The pair marginal `P₂(x, y) = w_x w_y M_xy cod(x,y) / R`. -/
noncomputable def P₂ (x y : V) : ℝ := K.w x * K.w y * K.M x y * K.cod x y / K.R

/-- The vertex marginal `P₁(x) = w_x tri(x) / R`. -/
noncomputable def P₁ (x : V) : ℝ := K.w x * K.tri x / K.R

/-- `h = ∑ P₂ log cod`, the weighted `H(Z | X, Y)`. -/
noncomputable def h : ℝ := ∑ x, ∑ y, K.P₂ x y * Real.log (K.cod x y)

/-- `A = ∑ P₁ log tri`. -/
noncomputable def A : ℝ := ∑ x, K.P₁ x * Real.log (K.tri x)

/-- `L = ∑ P₁ log deg`. -/
noncomputable def Ldeg : ℝ := ∑ x, K.P₁ x * Real.log (K.deg x)

lemma P₂_nonneg (x y : V) : 0 ≤ K.P₂ x y :=
  div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (K.w_nonneg x) (K.w_nonneg y)) (K.M_nonneg x y))
    (K.cod_nonneg x y)) K.R_nonneg

lemma P₁_nonneg (x : V) : 0 ≤ K.P₁ x :=
  div_nonneg (mul_nonneg (K.w_nonneg x) (K.tri_nonneg x)) K.R_nonneg

lemma P₂_symm (x y : V) : K.P₂ x y = K.P₂ y x := by
  simp only [P₂, K.M_symm x y, K.cod_symm x y]
  ring

lemma sum_P₂ (x : V) : ∑ y, K.P₂ x y = K.P₁ x := by
  simp only [P₂, P₁, tri, ← sum_div, mul_sum]
  exact congrArg (· / K.R) (sum_congr rfl fun y _ => by ring)

lemma sum_P₁ (hR : 0 < K.R) : ∑ x, K.P₁ x = 1 := by
  simp only [P₁, ← sum_div]
  exact div_self hR.ne'

lemma sum_sum_P₂ (hR : 0 < K.R) : ∑ x, ∑ y, K.P₂ x y = 1 := by
  simp only [sum_P₂, K.sum_P₁ hR]

/-- Summing a function of the first vertex against `P₂`. -/
lemma sum_P₂_mul_left (f : V → ℝ) : ∑ x, ∑ y, K.P₂ x y * f x = ∑ x, K.P₁ x * f x := by
  simp only [← sum_mul, sum_P₂]

/-- On the support of `P₂` every factor is nonzero. -/
lemma P₂_support {x y : V} (h : K.P₂ x y ≠ 0) :
    K.w x ≠ 0 ∧ K.w y ≠ 0 ∧ K.M x y ≠ 0 ∧ K.cod x y ≠ 0 ∧ K.R ≠ 0 := by
  simp only [P₂, div_ne_zero_iff, mul_ne_zero_iff] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma P₁_support {x : V} (h : K.P₁ x ≠ 0) : K.w x ≠ 0 ∧ K.tri x ≠ 0 ∧ K.R ≠ 0 := by
  simp only [P₁, div_ne_zero_iff, mul_ne_zero_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **T1** (`eq:triangle-bounds`, first part): `h ≥ log R − log E`. -/
theorem h_ge (hR : 0 < K.R) : Real.log K.R - Real.log K.E ≤ K.h := by
  set p : V × V → ℝ := fun q => K.P₂ q.1 q.2
  set ρ : V × V → ℝ := fun q => K.w q.1 * K.w q.2 * K.M q.1 q.2
  have hp0 : ∀ q, 0 ≤ p q := fun q => K.P₂_nonneg _ _
  have hp1 : ∑ q, p q = 1 := by rw [Fintype.sum_prod_type]; exact K.sum_sum_P₂ hR
  have hρ0 : ∀ q, 0 ≤ ρ q := fun q =>
    mul_nonneg (mul_nonneg (K.w_nonneg _) (K.w_nonneg _)) (K.M_nonneg _ _)
  have hsupp : ∀ q, p q ≠ 0 → ρ q ≠ 0 := fun q hq => by
    obtain ⟨h1, h2, h3, -, -⟩ := K.P₂_support hq
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  have hG := relEnt_le_log_sum hp0 hp1 hρ0 hsupp
  have hρsum : ∑ q, ρ q = K.E := by rw [Fintype.sum_prod_type, E_eq_sum]
  rw [hρsum, relEnt_congr (fun q => Real.log K.R - Real.log (K.cod q.1 q.2)) fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := K.P₂_support hq
    simp only [ρ, p, P₂]
    rw [show K.w q.1 * K.w q.2 * K.M q.1 q.2 /
        (K.w q.1 * K.w q.2 * K.M q.1 q.2 * K.cod q.1 q.2 / K.R) = K.R / K.cod q.1 q.2 by
      field_simp, Real.log_div h5 h4]] at hG
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hp1, one_mul] at hG
  rw [Fintype.sum_prod_type] at hG
  unfold h
  linarith

/-- First half of **T2**: `A − L − h ≤ 0`, Gibbs against the law `w_x tri(x) w_y M_xy / (R deg x)`. -/
lemma A_sub_Ldeg_le_h (hR : 0 < K.R) : K.A - K.Ldeg ≤ K.h := by
  set p : V × V → ℝ := fun q => K.P₂ q.1 q.2
  set ρ : V × V → ℝ := fun q => K.w q.1 * K.tri q.1 * (K.w q.2 * K.M q.1 q.2) / (K.R * K.deg q.1)
  have hp0 : ∀ q, 0 ≤ p q := fun q => K.P₂_nonneg _ _
  have hp1 : ∑ q, p q = 1 := by rw [Fintype.sum_prod_type]; exact K.sum_sum_P₂ hR
  have hρ0 : ∀ q, 0 ≤ ρ q := fun q =>
    div_nonneg (mul_nonneg (mul_nonneg (K.w_nonneg _) (K.tri_nonneg _))
      (mul_nonneg (K.w_nonneg _) (K.M_nonneg _ _))) (mul_nonneg K.R_nonneg (K.deg_nonneg _))
  have hρ1 : ∑ q, ρ q = 1 := by
    rw [Fintype.sum_prod_type, ← K.sum_P₁ hR]
    refine sum_congr rfl fun x _ => ?_
    simp only [ρ, ← sum_div, ← mul_sum]
    by_cases hd : K.deg x = 0
    · have ht : K.tri x = 0 := le_antisymm (by simpa [hd] using K.tri_le_deg_sq x) (K.tri_nonneg x)
      simp [P₁, ht]
    · rw [show ∑ i, K.w i * K.M x i = K.deg x from rfl]
      rw [P₁]
      field_simp
  have hsupp : ∀ q, p q ≠ 0 → ρ q ≠ 0 := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := K.P₂_support hq
    have ht := K.tri_pos_of (x := q.1) (y := q.2) (mul_ne_zero (mul_ne_zero h2 h3) h4)
    have hd := K.deg_pos_of_tri_pos ht
    exact div_ne_zero (mul_ne_zero (mul_ne_zero h1 ht.ne') (mul_ne_zero h2 h3))
      (mul_ne_zero h5 hd.ne')
  have hG := relEnt_nonpos_of_law hp0 hp1 hρ0 hρ1 hsupp
  rw [relEnt_congr (fun q => Real.log (K.tri q.1) - Real.log (K.deg q.1)
      - Real.log (K.cod q.1 q.2)) fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := K.P₂_support hq
    have ht := K.tri_pos_of (x := q.1) (y := q.2) (mul_ne_zero (mul_ne_zero h2 h3) h4)
    have hd := K.deg_pos_of_tri_pos ht
    simp only [ρ, p, P₂]
    rw [show K.w q.1 * K.tri q.1 * (K.w q.2 * K.M q.1 q.2) / (K.R * K.deg q.1) /
        (K.w q.1 * K.w q.2 * K.M q.1 q.2 * K.cod q.1 q.2 / K.R)
        = K.tri q.1 / K.deg q.1 / K.cod q.1 q.2 by field_simp,
      Real.log_div (div_ne_zero ht.ne' hd.ne') h4, Real.log_div ht.ne' hd.ne']] at hG
  rw [Fintype.sum_prod_type] at hG
  simp only [p, mul_sub, sum_sub_distrib, K.sum_P₂_mul_left] at hG
  unfold A Ldeg h
  linarith

/-- Second half of **T2**: `2L − A ≤ log D − log R`, Gibbs against `w_x deg(x)² / R`. -/
lemma two_Ldeg_sub_A_le (hR : 0 < K.R) : 2 * K.Ldeg - K.A ≤ Real.log K.D - Real.log K.R := by
  set ρ : V → ℝ := fun x => K.w x * K.deg x ^ 2 / K.R
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x =>
    div_nonneg (mul_nonneg (K.w_nonneg _) (sq_nonneg _)) K.R_nonneg
  have hsupp : ∀ x, K.P₁ x ≠ 0 → ρ x ≠ 0 := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := K.P₁_support hx
    have hd := K.deg_pos_of_tri_pos ((K.tri_nonneg x).lt_of_ne h2.symm)
    exact div_ne_zero (mul_ne_zero h1 (pow_ne_zero 2 hd.ne')) h3
  have hG := relEnt_le_log_sum K.P₁_nonneg (K.sum_P₁ hR) hρ0 hsupp
  have hρsum : ∑ x, ρ x = K.D / K.R := by simp only [ρ, ← sum_div]; rfl
  rw [hρsum, Real.log_div (K.pos_of_R_pos hR).2.ne' hR.ne',
    relEnt_congr (fun x => 2 * Real.log (K.deg x) - Real.log (K.tri x)) fun x hx => by
      obtain ⟨h1, h2, h3⟩ := K.P₁_support hx
      have hd := K.deg_pos_of_tri_pos ((K.tri_nonneg x).lt_of_ne h2.symm)
      simp only [ρ, P₁]
      rw [show K.w x * K.deg x ^ 2 / K.R / (K.w x * K.tri x / K.R) = K.deg x ^ 2 / K.tri x by
        field_simp, Real.log_div (pow_ne_zero 2 hd.ne') h2, Real.log_pow]
      push_cast
      ring] at hG
  simp only [mul_sub, sum_sub_distrib] at hG
  unfold Ldeg A
  rw [mul_sum]
  have : ∑ x, K.P₁ x * (2 * Real.log (K.deg x)) = ∑ x, 2 * (K.P₁ x * Real.log (K.deg x)) :=
    sum_congr rfl fun x _ => by ring
  linarith

/-- **T2** (`eq:triangle-bounds`, second part): `I = A − 2h ≤ log D − log R`. -/
theorem I_le (hR : 0 < K.R) : K.A - 2 * K.h ≤ Real.log K.D - Real.log K.R := by
  have h1 := K.A_sub_Ldeg_le_h hR
  have h2 := K.two_Ldeg_sub_A_le hR
  linarith

end ProbHost

end TreeApex
