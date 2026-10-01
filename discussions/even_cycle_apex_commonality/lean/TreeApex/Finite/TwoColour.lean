import TreeApex.Finite.OneColour
import TreeApex.Host.Goodman

/-!
# Two colours and commonness on hosts (paper `sec:two-colors`)

Plan §2.6, with `σ = m(P₃)`, `τ = m(K₃)` on the host and `m(F) = t(F, M) + t(F, 1 − M)` (`Mh`).
For a recursive tree on `n = m + 2` vertices and `k = j + 1` apices, `a = n + k − 3 = m + j`,
`b = (k − 1)(n − 2) = j m`, `c = k (n − 1) = (j + 1)(m + 1)`:

* `host_two_colour_polynomial` (`eq:two-color-polynomial`): `τ^c ≤ m(T^{+k}) σ^b`, the one-colour
  inequality on the doubled host (`t(K₂) = 1/4`, `t(P₃) = σ/8`, `t(K₃) = τ/8`,
  `t(T^{+k}) = m(T^{+k}) / 2^{n+k}`), the powers of two cancelling by `eq:vertex-balance`;
* `commonness_scalar` (the display in the proof of `thm:common`):
  `σ ≥ 1/2`, `τ = 3σ/2 − 1/2`, `τ^c ≤ x σ^b` imply `x ≥ 4 / 2^{(k+1) n}`;
* `host_commonness`, and `host_star_commonness` for the one-vertex tree (`T^{+k} = K_{1,k}`,
  `m = ∑ w (deg^k + (1 − deg)^k) ≥ 2^{1−k}`).
-/

open Finset SimpleGraph

namespace TreeApex

namespace ProbHost

variable {V : Type*} [Fintype V] (K : ProbHost V)

/-! ### The doubled host's scalars -/

lemma double_E : K.double.E = 1 / 4 := by
  rw [← K.double.hostDens_K₂_eq, K.hostDens_double_of_connected _ connected_K₂, Mh_K₂]
  norm_num

lemma double_D : K.double.D = K.Mh (pathGraph 3) / 8 := by
  rw [← K.double.hostDens_P₃_eq, K.hostDens_double_of_connected _ connected_P₃]
  norm_num

lemma double_R : K.double.R = K.Mh (⊤ : SimpleGraph (Fin 3)) / 8 := by
  rw [← K.double.hostDens_K₃_eq, K.hostDens_double_of_connected _ connected_K₃]
  norm_num

/-- **`eq:vertex-balance`**: `(n + k) + 2a + 3b = 3c` with `n = m + 2`, `k = j + 1`. -/
lemma vertex_balance (m j : ℕ) :
    (m + 2 + (j + 1)) + 2 * (m + j) + 3 * (j * m) = 3 * ((j + 1) * (m + 1)) := by ring

/-- **`eq:two-color-polynomial`, host form**: `τ^c ≤ m(T^{+k}) σ^b`. -/
theorem host_two_colour_polynomial (par : ℕ → ℕ) (m j : ℕ) :
    K.Mh (⊤ : SimpleGraph (Fin 3)) ^ ((j + 1) * (m + 1))
      ≤ K.Mh (apexGraph (treeGraph par (m + 1)) (j + 1)) * K.Mh (pathGraph 3) ^ (j * m) := by
  have h := K.double.finite_counting_inequality' par m j
  rw [K.double_R, K.double_E, K.double_D,
    K.hostDens_double_of_connected _ (apexGraph_connected _ (by omega) (by omega))] at h
  set τ := K.Mh (⊤ : SimpleGraph (Fin 3))
  set σ := K.Mh (pathGraph 3)
  set x := K.Mh (apexGraph (treeGraph par (m + 1)) (j + 1))
  have key : (8 : ℝ) ^ ((j + 1) * (m + 1))
      = 2 ^ (m + 1 + 1 + (j + 1)) * 4 ^ (m + j) * 8 ^ (j * m) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
      ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  calc τ ^ ((j + 1) * (m + 1)) = (τ / 8) ^ ((j + 1) * (m + 1)) * 8 ^ ((j + 1) * (m + 1)) := by
        rw [div_pow]; field_simp
    _ ≤ x / 2 ^ (m + 1 + 1 + (j + 1)) * (1 / 4) ^ (m + j) * (σ / 8) ^ (j * m)
          * 8 ^ ((j + 1) * (m + 1)) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = x * σ ^ (j * m) := by
        rw [key, div_pow, div_pow, one_pow]
        field_simp

/-- **The commonness display** (proof of `thm:common`): with `n = m + 2`, `k = j + 1`, from
`σ ≥ 1/2`, `τ = 3σ/2 − 1/2` and `τ^c ≤ x σ^b` follows `x ≥ 4 / 2^{(k+1) n}`. -/
theorem commonness_scalar {σ τ x : ℝ} (m j : ℕ) (hσ : 1 / 2 ≤ σ) (hτ : τ = 3 / 2 * σ - 1 / 2)
    (h : τ ^ ((j + 1) * (m + 1)) ≤ x * σ ^ (j * m)) : 4 / 2 ^ ((j + 2) * (m + 2)) ≤ x := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / 2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; norm_num
  have hσ0 : 0 < σ := by linarith
  have hτ4 : u ^ 2 ≤ τ := by rw [hτ, hu]; nlinarith
  have hτ0 : 0 ≤ τ := le_trans (sq_nonneg u) hτ4
  have hτσ : σ * u ≤ τ := by rw [hτ, hu]; linarith
  -- `τ^{j+1} ≥ τ (σ/2)^j` and `τ ≥ 1/4`
  have h1 : τ * (σ * u) ^ j ≤ τ ^ (j + 1) := by
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hτσ j) hτ0
  have h2 : (u ^ 2) ^ (j + 1) ≤ τ ^ (j + 1) := pow_le_pow_left₀ (by positivity) hτ4 (j + 1)
  have h3 : (u ^ 2 * (σ * u) ^ j) ^ m ≤ (τ ^ (j + 1)) ^ m :=
    pow_le_pow_left₀ (by positivity)
      ((mul_le_mul_of_nonneg_right hτ4 (by positivity)).trans h1) m
  have hc : τ ^ ((j + 1) * (m + 1)) = τ ^ (j + 1) * (τ ^ (j + 1)) ^ m := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have h4 : (4 : ℝ) / 2 ^ ((j + 2) * (m + 2)) = u ^ (2 * (j + 1) + 2 * m + j * m) := by
    rw [show (j + 2) * (m + 2) = (2 * (j + 1) + 2 * m + j * m) + 2 by ring,
      pow_add (2 : ℝ) (2 * (j + 1) + 2 * m + j * m) 2, hu, one_div_pow,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hlow : 4 / 2 ^ ((j + 2) * (m + 2)) * σ ^ (j * m)
      = (u ^ 2) ^ (j + 1) * (u ^ 2 * (σ * u) ^ j) ^ m := by
    rw [h4]
    ring
  have hmain : 4 / 2 ^ ((j + 2) * (m + 2)) * σ ^ (j * m) ≤ x * σ ^ (j * m) := by
    rw [hlow]
    calc (u ^ 2) ^ (j + 1) * (u ^ 2 * (σ * u) ^ j) ^ m ≤ τ ^ (j + 1) * (τ ^ (j + 1)) ^ m :=
          mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = τ ^ ((j + 1) * (m + 1)) := hc.symm
      _ ≤ x * σ ^ (j * m) := h
  exact le_of_mul_le_mul_right hmain (by positivity)

/-- **Commonness on hosts** (`n = m + 2 ≥ 2`, `k = j + 1`): `m(T^{+k}) ≥ 4 / 2^{(k+1) n}`. -/
theorem host_commonness (par : ℕ → ℕ) (m j : ℕ) :
    4 / 2 ^ ((j + 2) * (m + 2)) ≤ K.Mh (apexGraph (treeGraph par (m + 1)) (j + 1)) :=
  commonness_scalar m j K.host_half_le_sigma K.host_goodman_identity
    (K.host_two_colour_polynomial par m j)

/-- The density of the star `K_{1,k}` (the one-vertex tree with `k` apices) in any kernel. -/
lemma hostDens_star (L : V → V → ℝ) (par : ℕ → ℕ) (k : ℕ) :
    hostDens K.w (apexGraph (treeGraph par 0) k) L = ∑ x, K.w x * (∑ z, K.w z * L x z) ^ k := by
  rw [hostDens_apexGraph_treeGraph, sum_comm]
  rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
  refine sum_congr rfl fun a _ => ?_
  simp only [Equiv.funUnique_symm_apply, univ_eq_empty, prod_empty, mul_one]
  rw [← sum_pages_prod (fun z => K.w z * L a z), mul_sum]
  refine sum_congr rfl fun s _ => ?_
  simp only [prod_mul_distrib, uniqueElim_const, prod_const, card_univ, Fintype.card_fin]
  ring

/-- **The star case of `thm:common`** (`n = 1`, `k = j + 1`): `m(K_{1,k}) ≥ 4 / 2^{k+1}`. -/
theorem host_star_commonness (par : ℕ → ℕ) (j : ℕ) :
    4 / 2 ^ ((j + 2) * 1) ≤ K.Mh (apexGraph (treeGraph par 0) (j + 1)) := by
  rw [Mh, hostDens_star, hostDens_star, ← sum_add_distrib]
  have hdc : ∀ x, ∑ z, K.w z * K.Mc x z = 1 - K.deg x := fun x => by
    simp only [Mc, mul_sub, mul_one, sum_sub_distrib, K.w_sum, deg]
  have hd : ∀ x, ∑ z, K.w z * K.M x z = K.deg x := fun x => rfl
  simp only [hdc, hd, ← mul_add]
  have hpt : ∀ x, 1 / 2 ^ j ≤ K.deg x ^ (j + 1) + (1 - K.deg x) ^ (j + 1) := by
    intro x
    have h := add_pow_le (K.deg_nonneg x) (by linarith [K.deg_le_one x] : 0 ≤ 1 - K.deg x) (j + 1)
    rw [add_sub_cancel, one_pow, Nat.add_sub_cancel] at h
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc 4 / 2 ^ ((j + 2) * 1) = ∑ x, K.w x * (1 / 2 ^ j) := by
        rw [← sum_mul, K.w_sum, one_mul, div_eq_div_iff (by positivity) (by positivity)]
        ring
    _ ≤ ∑ x, K.w x * (K.deg x ^ (j + 1) + (1 - K.deg x) ^ (j + 1)) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (K.w_nonneg x)

end ProbHost

end TreeApex
