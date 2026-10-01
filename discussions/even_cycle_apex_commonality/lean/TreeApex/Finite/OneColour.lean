import TreeApex.Entropy.Book
import TreeApex.Graph.RecTree

/-!
# The finite counting inequality (paper `thm:finite`), on weighted hosts

Plan §2.5.  For a host `K` with scalars `E = t(K₂)`, `D = t(P₃)`, `R = t(K₃)`, a recursive tree on
`n = m + 1 ≥ 2` vertices and `k ≥ 1` apices:

```
  R^{k(n−1)} ≤ t(T^{+k}) · E^{n+k−3} · D^{(k−1)(n−2)}.                 (eq:finite-count)
```

* `hostDens_apexGraph_treeGraph`: `t(T^{+k})` is the total reference weight of the tree law,
  `∑_{z⃗, x⃗} ∏ w_{zᵢ} ∏_u (w_{x_u} ∏ᵢ M_{x_u zᵢ}) ∏_{edges} M` (`Fin.append` splits the vertices,
  `prod_edgePairs_apexGraph` and `prod_edgePairs_treeGraph` the edges).
* `finite_counting_inequality`: if `R = 0` the left side vanishes; otherwise Gibbs along the tree
  (`relEnt_book_add_le_log`), `relEnt_book` (B1), `h_ge` (T1) and `g_ge` (B2) give
  `log t(T^{+k}) ≥ c log R − a log E − b log D`, and exponentiating finishes.
-/

open Finset EvenCycleApex

namespace TreeApex

variable {V : Type*} [Fintype V]

lemma hostDens_nonneg {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) {v : ℕ} (F : SimpleGraph (Fin v))
    [DecidableRel F.Adj] {L : V → V → ℝ} (hL : ∀ i j, 0 ≤ L i j) : 0 ≤ hostDens w F L :=
  sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => hw _) (prod_nonneg fun _ _ => hL _ _)

/-- **The weights of `T^{+k}`**: the density of the apex graph of a recursive tree, as a sum over
apex images `z⃗` and tree images `x⃗`. -/
theorem hostDens_apexGraph_treeGraph (w : V → ℝ) (M : V → V → ℝ) (par : ℕ → ℕ) (m k : ℕ) :
    hostDens w (apexGraph (treeGraph par m) k) M
      = ∑ s : Fin k → V, ∑ x : Fin (m + 1) → V, (∏ i, w (s i)) *
          (∏ u, (w (x u) * ∏ i, M (x u) (s i))) * ∏ i : Fin m, M (x (parV par i)) (x i.succ) := by
  unfold hostDens
  rw [← (appendEquiv (m + 1) k V).sum_comp, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun s _ => sum_congr rfl fun x _ => ?_
  simp only [appendEquiv, Equiv.coe_fn_mk]
  rw [Fin.prod_univ_add, prod_edgePairs_apexGraph (treeGraph par m)
    (fun a b => M (Fin.append x s a) (Fin.append x s b))]
  simp only [Fin.append_left, Fin.append_right, prod_mul_distrib]
  rw [prod_edgePairs_treeGraph par m (fun a b => M (x a) (x b))]
  ring

namespace ProbHost

variable (K : ProbHost V)

/-- `t(T^{+k})` is the total tree weight of the book reference factors. -/
lemma hostDens_eq_sum_treeWeight (j : ℕ) (hR : 0 < K.R) (par : ℕ → ℕ) (m : ℕ) :
    hostDens K.w (apexGraph (treeGraph par m) (j + 1)) K.M
      = ∑ q, (K.bookRef j hR).treeWeight par m q := by
  rw [hostDens_apexGraph_treeGraph, Fintype.sum_prod_type]
  rfl

/-- **`thm:finite`, weighted**, with `n = m + 2` tree vertices and `k = j + 1` apices:
`R^{(j+1)(m+1)} ≤ t(T^{+k}) E^{m+j} D^{jm}`. -/
theorem finite_counting_inequality' (par : ℕ → ℕ) (m j : ℕ) :
    K.R ^ ((j + 1) * (m + 1))
      ≤ hostDens K.w (apexGraph (treeGraph par (m + 1)) (j + 1)) K.M * K.E ^ (m + j)
          * K.D ^ (j * m) := by
  rcases K.R_nonneg.lt_or_eq with hR | hR
  swap
  · rw [← hR, zero_pow (by positivity)]
    exact mul_nonneg (mul_nonneg (hostDens_nonneg K.w_nonneg _ K.M_nonneg)
      (pow_nonneg K.E_nonneg _)) (pow_nonneg K.D_nonneg _)
  obtain ⟨hE, hD⟩ := K.pos_of_R_pos hR
  have ht := (K.bookLaw j hR).sum_treeWeight_pos (K.bookRef j hR) par (m + 1)
  rw [← K.hostDens_eq_sum_treeWeight j hR] at ht
  have hlog := (K.bookLaw j hR).relEnt_book_add_le_log (K.bookRef j hR) par m
  rw [K.relEnt_book j hR, ← K.hostDens_eq_sum_treeWeight j hR] at hlog
  have hh := K.h_ge hR
  have hg := K.g_ge j hR
  set t := hostDens K.w (apexGraph (treeGraph par (m + 1)) (j + 1)) K.M
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_mul
    (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 := mul_le_mul_of_nonneg_left hh hj
  have h2 := mul_le_mul_of_nonneg_left hg hm
  push_cast
  nlinarith

/-- **`thm:finite`, weighted** (plan §2.5): for a recursive tree on `n = m + 1 ≥ 2` vertices and
`k ≥ 1` apices, `R^{k(n−1)} ≤ t(T^{+k}) E^{n+k−3} D^{(k−1)(n−2)}`. -/
theorem finite_counting_inequality (par : ℕ → ℕ) {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    K.R ^ (k * m)
      ≤ hostDens K.w (apexGraph (treeGraph par m) k) K.M * K.E ^ (m + k - 2)
          * K.D ^ ((k - 1) * (m - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := K.finite_counting_inequality' par m j
  rwa [show m + 1 + (j + 1) - 2 = m + j by omega, show j + 1 - 1 = j by omega,
    show m + 1 - 1 = m by omega]

end ProbHost

end TreeApex
