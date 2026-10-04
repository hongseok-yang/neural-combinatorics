import ApicesCommonness.Trees.Transfer
import ApicesCommonness.Trees.Finite.TwoColour

/-!
# Every independent apex of a tree is common

The headline theorems (TREES_VERIFICATION_PLAN.md §0, statement lock T-D5), for every graphon `W`
on every probability space `(Ω, μ)` and every tree `T` on `Fin n` (Mathlib's `IsTree`), with
`T^{+k} = apexGraph T k`, `K₂ = ⊤ : SimpleGraph (Fin 2)`, `P₃ = pathGraph 3`,
`K₃ = ⊤ : SimpleGraph (Fin 3)`, `t = homDensity`, `m = commonalityM`:

* **P1** `tree_apex_one_colour` (`thm:one-color`):
  `t(K₃)^{k(n−1)} ≤ t(T^{+k}) t(K₂)^{n+k−3} t(P₃)^{(k−1)(n−2)}` for `n ≥ 2`, `k ≥ 1`;
* **P2** `tree_apex_two_colour_polynomial` (`eq:two-color-polynomial`) and `tree_apex_two_colour`
  (`thm:two-color`): `m(K₃)^{k(n−1)} / m(P₃)^{(k−1)(n−2)} ≤ m(T^{+k})`;
* **P3** `half_le_commonalityM_path`, `goodman_identity` (`lem:goodman`);
* **P4** `tree_apex_common` (`thm:common`): `m(T^{+k}) ≥ 2^{1−e(T^{+k})} = 4 / 2^{(k+1)n}` for every
  tree (including the one-vertex tree) and every `k ≥ 1`.

Each is first proved for recursive trees (`treeGraph par m`) by transferring the host theorems of
`Finite/` with `le_of_hosts_cont`, then for every tree through `exists_recTree_iso` and
`homDensity_apexGraph_of_iso`.  `tree_apex_one_colour'`, `tree_apex_two_colour_polynomial'` restate
P1 and P2 without natural subtraction (`n = m + 2`, `k = j + 1`).
-/

open MeasureTheory SimpleGraph

namespace ApicesCommonness

open Foundation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ}

/-! ### Goodman (P3) -/

/-- **`lem:goodman`, first part**: `m(P₃, W) ≥ 1/2`. -/
theorem half_le_commonalityM_path (hW : IsGraphon W μ) :
    1 / 2 ≤ commonalityM (pathGraph 3) W μ :=
  le_of_hosts_cont (F := fun _ => 1 / 2) (G := fun V => commonalityM (pathGraph 3) V μ) hW
    (L1ContAt.const _ _) (commonalityM_cont _ hW) fun hσ M hsym h0 h1 _ hV => by
      rw [commonalityM_step hσ M hsym h0 h1 hV]
      exact ProbHost.host_half_le_sigma _

/-- **Goodman's identity** (`lem:goodman`): `m(K₃, W) = (3/2) m(P₃, W) − 1/2`. -/
theorem goodman_identity (hW : IsGraphon W μ) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ = 3 / 2 * commonalityM (pathGraph 3) W μ - 1 / 2 := by
  have hc : L1ContAt μ (fun V => 3 / 2 * commonalityM (pathGraph 3) V μ - 1 / 2) W :=
    (commonalityM_cont _ hW).comp (φ := fun t : ℝ => 3 / 2 * t - 1 / 2)
      (by fun_prop : Continuous fun t : ℝ => 3 / 2 * t - 1 / 2).continuousAt
  refine le_antisymm ?_ ?_
  · refine le_of_hosts_cont (F := fun V => commonalityM (⊤ : SimpleGraph (Fin 3)) V μ)
      (G := fun V => 3 / 2 * commonalityM (pathGraph 3) V μ - 1 / 2) hW
      (commonalityM_cont _ hW) hc fun hσ M hsym h0 h1 _ hV => ?_
    rw [commonalityM_step hσ M hsym h0 h1 hV, commonalityM_step hσ M hsym h0 h1 hV,
      ProbHost.host_goodman_identity]
  · refine le_of_hosts_cont (G := fun V => commonalityM (⊤ : SimpleGraph (Fin 3)) V μ)
      (F := fun V => 3 / 2 * commonalityM (pathGraph 3) V μ - 1 / 2) hW
      hc (commonalityM_cont _ hW) fun hσ M hsym h0 h1 _ hV => ?_
    rw [commonalityM_step hσ M hsym h0 h1 hV, commonalityM_step hσ M hsym h0 h1 hV,
      ProbHost.host_goodman_identity]

/-! ### Recursive trees -/

/-- P1 for the recursive tree `par` on `m + 1` vertices. -/
theorem treeGraph_apex_one_colour (hW : IsGraphon W μ) (par : ℕ → ℕ) {m k : ℕ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * m)
      ≤ homDensity (apexGraph (treeGraph par m) k) W μ
          * homDensity (⊤ : SimpleGraph (Fin 2)) W μ ^ (m + k - 2)
          * homDensity (pathGraph 3) W μ ^ ((k - 1) * (m - 1)) :=
  le_of_hosts_cont (F := fun V => homDensity (⊤ : SimpleGraph (Fin 3)) V μ ^ (k * m))
    (G := fun V => homDensity (apexGraph (treeGraph par m) k) V μ
      * homDensity (⊤ : SimpleGraph (Fin 2)) V μ ^ (m + k - 2)
      * homDensity (pathGraph 3) V μ ^ ((k - 1) * (m - 1))) hW
    ((homDensity_cont _ hW).pow _)
    (((homDensity_cont _ hW).mul ((homDensity_cont _ hW).pow _)).mul
      ((homDensity_cont _ hW).pow _))
    fun hσ M hsym h0 h1 _ hV => by
      simp only [homDensity_step hσ M hsym h0 h1 hV]
      rw [ProbHost.hostDens_K₃_eq, ProbHost.hostDens_K₂_eq, ProbHost.hostDens_P₃_eq]
      exact ProbHost.finite_counting_inequality _ par hm hk

/-- P2 (polynomial form) for the recursive tree `par` on `m + 2` vertices, `k = j + 1`. -/
theorem treeGraph_apex_two_colour_polynomial (hW : IsGraphon W μ) (par : ℕ → ℕ) (m j : ℕ) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ ^ ((j + 1) * (m + 1))
      ≤ commonalityM (apexGraph (treeGraph par (m + 1)) (j + 1)) W μ
          * commonalityM (pathGraph 3) W μ ^ (j * m) :=
  le_of_hosts_cont (F := fun V => commonalityM (⊤ : SimpleGraph (Fin 3)) V μ ^ ((j + 1) * (m + 1)))
    (G := fun V => commonalityM (apexGraph (treeGraph par (m + 1)) (j + 1)) V μ
      * commonalityM (pathGraph 3) V μ ^ (j * m)) hW
    ((commonalityM_cont _ hW).pow _) ((commonalityM_cont _ hW).mul ((commonalityM_cont _ hW).pow _))
    fun hσ M hsym h0 h1 _ hV => by
      simp only [commonalityM_step hσ M hsym h0 h1 hV]
      exact ProbHost.host_two_colour_polynomial _ par m j

/-- The star case for the recursive tree on one vertex, `k = j + 1`. -/
theorem treeGraph_star_common (hW : IsGraphon W μ) (par : ℕ → ℕ) (j : ℕ) :
    4 / 2 ^ ((j + 2) * 1) ≤ commonalityM (apexGraph (treeGraph par 0) (j + 1)) W μ :=
  le_of_hosts_cont (F := fun _ => 4 / 2 ^ ((j + 2) * 1))
    (G := fun V => commonalityM (apexGraph (treeGraph par 0) (j + 1)) V μ) hW
    (L1ContAt.const _ _) (commonalityM_cont _ hW) fun hσ M hsym h0 h1 _ hV => by
      rw [commonalityM_step hσ M hsym h0 h1 hV]
      exact ProbHost.host_star_commonness _ par j

/-! ### Every tree -/

variable {n k : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj]

/-- Relabelling invariance of `m(T^{+k}, W)`. -/
lemma commonalityM_apexGraph_of_iso {m : ℕ} {T : SimpleGraph (Fin (m + 1))} [DecidableRel T.Adj]
    {par : ℕ → ℕ} {e : Fin (m + 1) ≃ Fin (m + 1)} (h : T = (treeGraph par m).comap e)
    (hW : IsGraphon W μ) :
    commonalityM (apexGraph T k) W μ = commonalityM (apexGraph (treeGraph par m) k) W μ := by
  rw [commonalityM, commonalityM, homDensity_apexGraph_of_iso h hW.symm,
    homDensity_apexGraph_of_iso h (isGraphon_cmpl hW).symm]

/-- **P1, `thm:one-color`.**  For a tree `T` on `n ≥ 2` vertices and `k ≥ 1`,
`t(K₃)^{k(n−1)} ≤ t(T^{+k}) t(K₂)^{n+k−3} t(P₃)^{(k−1)(n−2)}`. -/
theorem tree_apex_one_colour (hW : IsGraphon W μ) (hT : T.IsTree) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
      ≤ homDensity (apexGraph T k) W μ
          * homDensity (⊤ : SimpleGraph (Fin 2)) W μ ^ (n + k - 3)
          * homDensity (pathGraph 3) W μ ^ ((k - 1) * (n - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨par, e, hTe⟩ := exists_recTree_iso hT
  rw [homDensity_apexGraph_of_iso hTe hW.symm, show m + 1 - 1 = m by omega,
    show m + 1 + k - 3 = m + k - 2 by omega, show m + 1 - 2 = m - 1 by omega]
  exact treeGraph_apex_one_colour hW par (by omega) hk

/-- **P2, `eq:two-color-polynomial`.**  `m(K₃)^{k(n−1)} ≤ m(T^{+k}) m(P₃)^{(k−1)(n−2)}`. -/
theorem tree_apex_two_colour_polynomial (hW : IsGraphon W μ) (hT : T.IsTree) (hn : 2 ≤ n)
    (hk : 1 ≤ k) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
      ≤ commonalityM (apexGraph T k) W μ * commonalityM (pathGraph 3) W μ ^ ((k - 1) * (n - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨par, e, hTe⟩ := exists_recTree_iso hT
  rw [commonalityM_apexGraph_of_iso hTe hW, show m + 2 - 1 = m + 1 by omega,
    show j + 1 - 1 = j by omega, show m + 2 - 2 = m by omega]
  exact treeGraph_apex_two_colour_polynomial hW par m j

/-- **P2, `thm:two-color`.**  `m(T^{+k}) ≥ m(K₃)^{k(n−1)} / m(P₃)^{(k−1)(n−2)}`. -/
theorem tree_apex_two_colour (hW : IsGraphon W μ) (hT : T.IsTree) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
        / commonalityM (pathGraph 3) W μ ^ ((k - 1) * (n - 2))
      ≤ commonalityM (apexGraph T k) W μ := by
  have hσ : 0 < commonalityM (pathGraph 3) W μ :=
    lt_of_lt_of_le (by norm_num) (half_le_commonalityM_path hW)
  rw [div_le_iff₀ (pow_pos hσ _)]
  exact tree_apex_two_colour_polynomial T hW hT hn hk

/-- **P4, `thm:common`.**  For every tree `T` on `n` vertices and every `k ≥ 1`,
`m(T^{+k}, W) ≥ 2^{1−e(T^{+k})} = 4 / 2^{(k+1) n}` (`apexGraph_edgeCount`: `e = (k+1)n − 1`). -/
theorem tree_apex_common (hW : IsGraphon W μ) (hT : T.IsTree) (hk : 1 ≤ k) :
    4 / 2 ^ ((k + 1) * n) ≤ homDensity (apexGraph T k) W μ + homDensity (apexGraph T k) (cmpl W) μ := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hT.connected.nonempty
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show 4 / 2 ^ ((j + 1 + 1) * n) ≤ commonalityM (apexGraph T (j + 1)) W μ
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- the one-vertex tree: `T^{+k}` is the star `K_{1,k}`
    obtain rfl : n = 1 := by omega
    obtain ⟨par, e, hTe⟩ := exists_recTree_iso (m := 0) hT
    rw [commonalityM_apexGraph_of_iso hTe hW]
    exact treeGraph_star_common hW par j
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h := tree_apex_two_colour_polynomial T hW hT h2 (by omega : 1 ≤ j + 1)
    rw [show j + 1 - 1 = j by omega, show m + 2 - 1 = m + 1 by omega,
      show m + 2 - 2 = m by omega] at h
    have hc := ProbHost.commonness_scalar m j (half_le_commonalityM_path hW) (goodman_identity hW) h
    rwa [show j + 1 + 1 = j + 2 by omega]

/-- **P1 without natural subtraction** (`n = m + 2`, `k = j + 1`):
`t(K₃)^{(j+1)(m+1)} ≤ t(T^{+k}) t(K₂)^{m+j} t(P₃)^{jm}`. -/
theorem tree_apex_one_colour' {m : ℕ} (T : SimpleGraph (Fin (m + 2))) [DecidableRel T.Adj]
    (hW : IsGraphon W μ) (hT : T.IsTree) (j : ℕ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W μ ^ ((j + 1) * (m + 1))
      ≤ homDensity (apexGraph T (j + 1)) W μ
          * homDensity (⊤ : SimpleGraph (Fin 2)) W μ ^ (m + j)
          * homDensity (pathGraph 3) W μ ^ (j * m) := by
  have h := tree_apex_one_colour T hW hT (by omega) (by omega : 1 ≤ j + 1)
  rwa [show m + 2 - 1 = m + 1 by omega, show m + 2 + (j + 1) - 3 = m + j by omega,
    show j + 1 - 1 = j by omega, show m + 2 - 2 = m by omega] at h

/-- **P2 without natural subtraction** (`n = m + 2`, `k = j + 1`):
`m(K₃)^{(j+1)(m+1)} ≤ m(T^{+k}) m(P₃)^{jm}`. -/
theorem tree_apex_two_colour_polynomial' {m : ℕ} (T : SimpleGraph (Fin (m + 2)))
    [DecidableRel T.Adj] (hW : IsGraphon W μ) (hT : T.IsTree) (j : ℕ) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ ^ ((j + 1) * (m + 1))
      ≤ commonalityM (apexGraph T (j + 1)) W μ * commonalityM (pathGraph 3) W μ ^ (j * m) := by
  have h := tree_apex_two_colour_polynomial T hW hT (by omega) (by omega : 1 ≤ j + 1)
  rwa [show m + 2 - 1 = m + 1 by omega, show j + 1 - 1 = j by omega,
    show m + 2 - 2 = m by omega] at h

end ApicesCommonness
