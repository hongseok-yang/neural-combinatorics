import ApicesCommonness.Trees.Main
import ApicesCommonness.Cycles.Main
import ApicesCommonness.Cycles.Equality.Main

/-!
# Main results

The main theorems of *Commonness of independent apices of trees and even cycles*: Theorems 1.2
and 1.3 (trees) and Theorem 1.4 (even cycles).  They hold for every graphon `W` on every
probability space `(Ω, μ)`, not only on `[0,1]`.  Each is proved by the corresponding theorem of
`Trees/` or `Cycles/`.

The statements use these definitions.

* `IsGraphon W μ`, in `Common/Foundation/Graphon.lean`: the hypothesis on `W`.
* `homDensity F W μ`, in `Common/Graph/HomDensity.lean`: the homomorphism density `t(F, W)`.
* `commonalityM F W μ`, in `Common/Graph/HomDensity.lean`: `M(F, W) = t(F, W) + t(F, 1 − W)`.
* `cmpl W`, in `Common/Foundation/Defs.lean`: the kernel `1 − W`.
* `edgePairs F`, in `Common/Graph/Apex.lean`: the edges of `F`, as the pairs `(i, j)` with
  `i < j`; `(edgePairs F).card` is the number of edges `e(F)`.
* `apexCycle n k`, in `Common/Graph/Apex.lean`: the graph `C_n^{+k}`.
* `apexGraph T k`, in `Trees/Graph/Apex.lean`: the graph `T^{+k}`.
* From mathlib: `SimpleGraph.IsTree`, `cycleGraph n` (the cycle `C_n`), `pathGraph 3` (the path
  `P_2` with two edges) and `⊤ : SimpleGraph (Fin m)` (the complete graph `K_m`).

A graph `F` is common when `M(F, W) ≥ 2^{1 − e(F)}` for every graphon `W`, written here as
`2 / 2 ^ (edgePairs F).card ≤ commonalityM F W μ`.
-/

open MeasureTheory SimpleGraph

namespace ApicesCommonness.MainResults

open Foundation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/-! ### Trees -/

/-- **Theorem 1.2**, commonness: for every tree `T` and every `k ≥ 1`, the graph `T^{+k}` is
common. -/
theorem trees_common {n : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj] (hT : T.IsTree)
    {k : ℕ} (hk : 1 ≤ k) (hW : IsGraphon W μ) :
    2 / 2 ^ (edgePairs (apexGraph T k)).card ≤ commonalityM (apexGraph T k) W μ := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hT.connected.nonempty
  have hkn : 0 < (k + 1) * n := Nat.mul_pos (by omega) hn
  obtain ⟨e, he⟩ : ∃ e, (k + 1) * n = e + 1 := ⟨(k + 1) * n - 1, by omega⟩
  have h := tree_apex_common T hW hT hk
  rw [he] at h
  rw [apexGraph_edgeCount T hT, he, Nat.add_sub_cancel]
  calc (2 : ℝ) / 2 ^ e = 4 / 2 ^ (e + 1) := by rw [pow_succ]; ring
    _ ≤ commonalityM (apexGraph T k) W μ := h

/-- **Theorem 1.2**, the two-colour inequality: for a tree `T` on `n ≥ 2` vertices and `k ≥ 1`,
the denominator `M(P_2, W)` is positive and
`M(T^{+k}, W) ≥ M(K_3, W)^{k(n−1)} / M(P_2, W)^{(k−1)(n−2)}`. -/
theorem trees_two_colour {n : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj] (hT : T.IsTree)
    (hn : 2 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hW : IsGraphon W μ) :
    0 < commonalityM (pathGraph 3) W μ ∧
      commonalityM (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
          / commonalityM (pathGraph 3) W μ ^ ((k - 1) * (n - 2))
        ≤ commonalityM (apexGraph T k) W μ :=
  ⟨lt_of_lt_of_le (by norm_num) (half_le_commonalityM_path hW), tree_apex_two_colour T hW hT hn hk⟩

/-- **Theorem 1.3**, the one-colour inequality: for a tree `T` on `n ≥ 2` vertices and `k ≥ 1`,
`t(T^{+k}, W) t(K_2, W)^{n+k−3} t(P_2, W)^{(k−1)(n−2)} ≥ t(K_3, W)^{k(n−1)}`. -/
theorem trees_one_colour {n : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj] (hT : T.IsTree)
    (hn : 2 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hW : IsGraphon W μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
      ≤ homDensity (apexGraph T k) W μ
          * homDensity (⊤ : SimpleGraph (Fin 2)) W μ ^ (n + k - 3)
          * homDensity (pathGraph 3) W μ ^ ((k - 1) * (n - 2)) :=
  tree_apex_one_colour T hW hT hn hk

/-! ### Even cycles -/

/-- **Theorem 1.4**, commonness: for every even `n ≥ 4` and every `k ≥ 1`, the graph `C_n^{+k}`
is common. -/
theorem cycles_common {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hW : IsGraphon W μ) :
    2 / 2 ^ (edgePairs (apexCycle n k)).card ≤ commonalityM (apexCycle n k) W μ := by
  rw [apexCycle_edgeCount (by omega)]
  exact commonality_all_even_all_apices hW hn hn4 hk

/-- **Theorem 1.4**, equality: for every even `n ≥ 4` and every `k ≥ 1`, equality holds in the
commonness bound for `C_n^{+k}` if and only if `W = 1/2` almost everywhere. -/
theorem cycles_equality_iff {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hW : IsGraphon W μ) :
    commonalityM (apexCycle n k) W μ = 2 / 2 ^ (edgePairs (apexCycle n k)).card ↔
      (fun p : Ω × Ω => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => (1 / 2 : ℝ) := by
  rw [apexCycle_edgeCount (by omega)]
  exact commonality_equality_iff_constant hW hn hn4 hk

/-- **Theorem 1.4**, the relative bound: for every even `n ≥ 4` and every `k ≥ 3`,
`M(C_n^{+k}, W) ≥ 2^{−nk} M(C_n, W) ≥ 2^{1−n(k+1)}`. -/
theorem cycles_relative {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) {k : ℕ} (hk : 3 ≤ k)
    (hW : IsGraphon W μ) :
    commonalityM (cycleGraph n) W μ / 2 ^ (n * k) ≤ commonalityM (apexCycle n k) W μ ∧
      2 / 2 ^ (n * (k + 1)) ≤ commonalityM (cycleGraph n) W μ / 2 ^ (n * k) := by
  have h1 : 2 ^ (n * (k + 1)) / 2 * commonalityM (apexCycle n k) W μ
      ≥ 2 ^ n / 2 * commonalityM (cycleGraph n) W μ := apex_relative_of_three_le hW hn hn4 hk
  have h2 : 1 ≤ 2 ^ n / 2 * commonalityM (cycleGraph n) W μ := one_le_cycle_normalized hW hn hn4
  have hp : (2 : ℝ) ^ (n * (k + 1)) = 2 ^ n * 2 ^ (n * k) := by rw [← pow_add]; ring_nf
  have hq : (0 : ℝ) < 2 ^ (n * k) := by positivity
  have hr : (0 : ℝ) < 2 ^ n := by positivity
  rw [hp] at h1
  constructor
  · rw [div_le_iff₀ hq]
    have h3 : 2 ^ n / 2 * commonalityM (cycleGraph n) W μ
        ≤ 2 ^ n / 2 * (commonalityM (apexCycle n k) W μ * 2 ^ (n * k)) := by
      linarith
    exact le_of_mul_le_mul_left h3 (by positivity)
  · rw [le_div_iff₀ hq, hp, div_mul_eq_mul_div, mul_div_mul_right _ _ hq.ne', div_le_iff₀ hr]
    linarith

end ApicesCommonness.MainResults
