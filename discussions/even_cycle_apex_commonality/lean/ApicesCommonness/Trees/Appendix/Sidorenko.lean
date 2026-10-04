import ApicesCommonness.Trees.Main

/-!
# Appendix A: trees themselves (paper `prop:tree-sidorenko`)

Plan §2.8 (optional milestone T8).  The same machinery with no apices: on a host with `E > 0` the
uniform ordered edge becomes the symmetric law `Q(x, y) = w_x w_y M_xy / E` (a `SymLaw` over
`S = Unit`) with reference factors `ρ_S = 1`, `ν = w`, `η = M`; its tree weights are the weights
of `T` itself.

* `relEnt_edge`: `relEnt ρ_B Q = log E`;
* `edge_condRelEnt_ge`: `g ≥ log E` (here `g = ∑ μ(a) log deg(a)` and Gibbs against the law `w`);
* `host_tree_sidorenko`: `E^{n−1} ≤ t(T)` on hosts (Gibbs along the tree), then
  `host_tree_common`: `m(T) ≥ 4 / 2^n` (`add_pow_le` with `t(K₂, 1 − M) = 1 − E`);
* `tree_sidorenko`, `tree_common`: the graphon forms, for every Mathlib tree.
-/

open Finset MeasureTheory SimpleGraph

namespace ApicesCommonness

open Foundation

/-- The density of a recursive tree in any kernel. -/
theorem hostDens_treeGraph {V : Type*} [Fintype V] (w : V → ℝ) (L : V → V → ℝ) (par : ℕ → ℕ)
    (m : ℕ) :
    hostDens w (treeGraph par m) L
      = ∑ x : Fin (m + 1) → V, (∏ u, w (x u)) * ∏ i : Fin m, L (x (parV par i)) (x i.succ) := by
  unfold hostDens
  refine sum_congr rfl fun x _ => ?_
  rw [prod_edgePairs_treeGraph par m (fun a b => L (x a) (x b))]

namespace ProbHost

variable {V : Type*} [Fintype V] (K : ProbHost V)

/-- The uniform ordered edge: `Q(x, y) = w_x w_y M_xy / E`. -/
noncomputable def edgeLaw (hE : 0 < K.E) : SymLaw Unit V where
  Q _ x y := K.w x * K.w y * K.M x y / K.E
  nonneg _ x y := div_nonneg (mul_nonneg (mul_nonneg (K.w_nonneg x) (K.w_nonneg y))
    (K.M_nonneg x y)) K.E_nonneg
  sum_eq := by
    rw [Fintype.sum_unique]
    simp only [← sum_div]
    rw [← E_eq_sum, div_self hE.ne']
  symm _ x y := by rw [K.M_symm x y, mul_comm (K.w x)]

/-- Reference factors of the tree itself: `ρ_S = 1`, `ν = w`, `η = M`. -/
noncomputable def edgeRef (hE : 0 < K.E) : RefFactors (K.edgeLaw hE) where
  ρS _ := 1
  ν _ x := K.w x
  η := K.M
  ρS_nonneg _ := zero_le_one
  ν_nonneg _ := K.w_nonneg
  η_nonneg := K.M_nonneg
  supp _ x y h := by
    simp only [edgeLaw, div_ne_zero_iff, mul_ne_zero_iff] at h
    exact ⟨one_ne_zero, h.1.1.1, h.1.1.2, h.1.2⟩

lemma hostDens_treeGraph_eq_sum_treeWeight (hE : 0 < K.E) (par : ℕ → ℕ) (m : ℕ) :
    hostDens K.w (treeGraph par m) K.M = ∑ q, (K.edgeRef hE).treeWeight par m q := by
  rw [hostDens_treeGraph, Fintype.sum_prod_type]
  simp only [univ_unique, sum_singleton]
  refine sum_congr rfl fun x _ => ?_
  simp only [RefFactors.treeWeight, edgeRef, one_mul]

/-- `relEnt ρ_B Q = log E` for the edge law. -/
lemma relEnt_edge (hE : 0 < K.E) :
    relEnt (K.edgeRef hE).bookWeight (fun q : Unit × V × V => (K.edgeLaw hE).Q q.1 q.2.1 q.2.2)
      = Real.log K.E := by
  rw [relEnt_congr (fun _ => Real.log K.E) fun q hq => by
    have hn : K.w q.2.1 * K.w q.2.2 * K.M q.2.1 q.2.2 ≠ 0 := by
      intro h0; apply hq; simp [edgeLaw, h0]
    simp only [RefFactors.bookWeight, edgeRef, edgeLaw, one_mul]
    rw [div_div_cancel₀ hn]]
  rw [← sum_mul, show ∑ q : Unit × V × V, (K.edgeLaw hE).Q q.1 q.2.1 q.2.2 = 1 by
    rw [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_prod_type]
    simpa [Fintype.sum_unique] using (K.edgeLaw hE).sum_eq, one_mul]

lemma edgeLaw_Q (hE : 0 < K.E) (u : Unit) (x y : V) :
    (K.edgeLaw hE).Q u x y = K.w x * K.w y * K.M x y / K.E := rfl

lemma edgeLaw_marg (hE : 0 < K.E) (u : Unit) (a : V) :
    (K.edgeLaw hE).marg u a = K.w a * K.deg a / K.E := by
  simp only [SymLaw.marg, edgeLaw, ← sum_div, deg, mul_sum]
  exact congrArg (· / K.E) (sum_congr rfl fun y _ => by ring)

/-- `g ≥ log E` for the edge law (the weighted `H(Y | X) ≥ log E`). -/
lemma edge_condRelEnt_ge (hE : 0 < K.E) :
    Real.log K.E ≤ (K.edgeLaw hE).condRelEnt (K.edgeRef hE) := by
  -- `g = ∑ μ(a) log deg(a)`
  have hg : (K.edgeLaw hE).condRelEnt (K.edgeRef hE)
      = ∑ a, (K.edgeLaw hE).marg () a * Real.log (K.deg a) := by
    rw [SymLaw.condRelEnt, Fintype.sum_unique]
    refine sum_congr rfl fun a _ => ?_
    by_cases hm : (K.edgeLaw hE).marg () a = 0
    · rw [hm, zero_mul, zero_mul]
    congr 1
    rw [relEnt_congr (fun _ => Real.log (K.deg a)) fun y hy => by
      have hQ := (K.edgeLaw hE).Q_ne_zero_of_kern hy
      have hn : K.w a * K.w y * K.M a y ≠ 0 := by
        intro h0; apply hQ; simp [edgeLaw, h0]
      have hw : K.w a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hn)
      have hwy : K.w y ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hn)
      have hM : K.M a y ≠ 0 := right_ne_zero_of_mul hn
      have hd : K.deg a ≠ 0 := by
        intro h0; apply hm; rw [edgeLaw_marg, h0, mul_zero, zero_div]
      have hν : ∀ u : Unit, (K.edgeRef hE).ν u y * (K.edgeRef hE).η a y = K.w y * K.M a y :=
        fun _ => rfl
      rw [hν, SymLaw.kern, edgeLaw_marg, edgeLaw_Q,
        show K.w y * K.M a y / (K.w a * K.w y * K.M a y / K.E / (K.w a * K.deg a / K.E))
          = K.deg a by field_simp]]
    rw [← sum_mul, (K.edgeLaw hE).sum_kern hm, one_mul]
  rw [hg]
  -- Gibbs: `∑ μ log (w / μ) ≤ log ∑ w = 0`
  have hG := relEnt_le_log_sum (ρ := K.w) (p := fun a => (K.edgeLaw hE).marg () a)
    (fun a => (K.edgeLaw hE).marg_nonneg () a)
    (by simpa [Fintype.sum_unique] using (K.edgeLaw hE).sum_marg) K.w_nonneg
    (fun a ha => by
      rw [edgeLaw_marg] at ha
      exact left_ne_zero_of_mul (div_ne_zero_iff.mp ha).1)
  rw [K.w_sum, Real.log_one, relEnt_congr (fun a => Real.log K.E - Real.log (K.deg a))
    fun a ha => by
      have h' := ha
      rw [edgeLaw_marg] at h'
      obtain ⟨⟨hw, hd⟩, -⟩ := (div_ne_zero_iff.mp h').imp_left mul_ne_zero_iff.mp
      rw [edgeLaw_marg, show K.w a / (K.w a * K.deg a / K.E) = K.E / K.deg a by field_simp,
        Real.log_div hE.ne' hd]] at hG
  simp only [mul_sub, sum_sub_distrib, ← sum_mul] at hG
  rw [show ∑ a, (K.edgeLaw hE).marg () a = 1 by
    simpa [Fintype.sum_unique] using (K.edgeLaw hE).sum_marg, one_mul] at hG
  linarith

/-- **`prop:tree-sidorenko`, host form** (`n = m + 2`): `E^{m+1} ≤ t(T)`. -/
theorem host_tree_sidorenko' (par : ℕ → ℕ) (m : ℕ) :
    K.E ^ (m + 1) ≤ hostDens K.w (treeGraph par (m + 1)) K.M := by
  rcases K.E_nonneg.lt_or_eq with hE | hE
  swap
  · rw [← hE, zero_pow (Nat.succ_ne_zero m)]
    exact hostDens_nonneg K.w_nonneg _ K.M_nonneg
  have ht := (K.edgeLaw hE).sum_treeWeight_pos (K.edgeRef hE) par (m + 1)
  rw [← K.hostDens_treeGraph_eq_sum_treeWeight hE] at ht
  have hlog := (K.edgeLaw hE).relEnt_book_add_le_log (K.edgeRef hE) par m
  rw [K.relEnt_edge hE, ← K.hostDens_treeGraph_eq_sum_treeWeight hE] at hlog
  have hg := mul_le_mul_of_nonneg_left (K.edge_condRelEnt_ge hE) (Nat.cast_nonneg (α := ℝ) m)
  rw [← Real.log_le_log_iff (by positivity) ht, Real.log_pow]
  push_cast
  linarith

/-- The one-vertex tree has density `1` in every kernel. -/
lemma hostDens_treeGraph_zero (L : V → V → ℝ) (par : ℕ → ℕ) :
    hostDens K.w (treeGraph par 0) L = 1 := by
  rw [hostDens_treeGraph]
  simp only [univ_eq_empty, prod_empty, mul_one]
  rw [sum_pages_prod, K.w_sum, one_pow]

lemma E_le_one : K.E ≤ 1 := by
  calc K.E ≤ ∑ x, K.w x :=
        sum_le_sum fun x _ => mul_le_of_le_one_right (K.w_nonneg x) (K.deg_le_one x)
    _ = 1 := K.w_sum

/-- **Commonness of trees on hosts** (`n = m + 1`): `m(T) ≥ 4 / 2^n`. -/
theorem host_tree_common (par : ℕ → ℕ) (m : ℕ) :
    4 / 2 ^ (m + 1) ≤ K.Mh (treeGraph par m) := by
  rcases m with _ | m
  · rw [Mh, K.hostDens_treeGraph_zero, K.hostDens_treeGraph_zero]
    norm_num
  have hEc : K.compl.E = 1 - K.E := by
    have h := K.Mh_K₂
    rw [Mh, K.hostDens_K₂_eq, show hostDens K.w (⊤ : SimpleGraph (Fin 2)) K.Mc = K.compl.E from
      K.compl.hostDens_K₂_eq] at h
    linarith
  have h1 := K.host_tree_sidorenko' par m
  have h2 := K.compl.host_tree_sidorenko' par m
  rw [hEc] at h2
  have h3 := add_pow_le K.E_nonneg (by linarith [K.E_le_one] : 0 ≤ 1 - K.E) (m + 1)
  rw [add_sub_cancel, one_pow, Nat.add_sub_cancel] at h3
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  rw [Mh]
  calc 4 / 2 ^ (m + 1 + 1) = 1 / 2 ^ m := by
        rw [div_eq_div_iff (by positivity) hpos.ne']; ring
    _ ≤ K.E ^ (m + 1) + (1 - K.E) ^ (m + 1) := by rw [div_le_iff₀ hpos]; linarith
    _ ≤ _ := add_le_add h1 h2

end ProbHost

/-! ### Graphon forms -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ} {n : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj]

/-- **`prop:tree-sidorenko`.**  For a tree `T` on `n ≥ 2` vertices, `t(T, W) ≥ t(K₂, W)^{n−1}`. -/
theorem tree_sidorenko (hW : IsGraphon W μ) (hT : T.IsTree) (hn : 2 ≤ n) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W μ ^ (n - 1) ≤ homDensity T W μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨par, e, hTe⟩ := exists_recTree_iso hT
  rw [homDensity_tree_of_iso hTe hW.symm, show m + 2 - 1 = m + 1 by omega]
  exact le_of_hosts_cont (F := fun V => homDensity (⊤ : SimpleGraph (Fin 2)) V μ ^ (m + 1))
    (G := fun V => homDensity (treeGraph par (m + 1)) V μ) hW ((homDensity_cont _ hW).pow _)
    (homDensity_cont _ hW) fun hσ M hsym h0 h1 _ hV => by
      simp only [homDensity_step hσ M hsym h0 h1 hV]
      rw [ProbHost.hostDens_K₂_eq]
      exact ProbHost.host_tree_sidorenko' _ par m

/-- **Every tree is common** (paper appendix A): `m(T, W) ≥ 2^{1−e(T)} = 4 / 2^n`. -/
theorem tree_common (hW : IsGraphon W μ) (hT : T.IsTree) :
    4 / 2 ^ n ≤ homDensity T W μ + homDensity T (cmpl W) μ := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hT.connected.nonempty
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨par, e, hTe⟩ := exists_recTree_iso hT
  rw [homDensity_tree_of_iso hTe hW.symm, homDensity_tree_of_iso hTe (isGraphon_cmpl hW).symm]
  exact le_of_hosts_cont (F := fun _ => 4 / 2 ^ (m + 1))
    (G := fun V => commonalityM (treeGraph par m) V μ) hW (L1ContAt.const _ _)
    (commonalityM_cont _ hW) fun hσ M hsym h0 h1 _ hV => by
      rw [commonalityM_step hσ M hsym h0 h1 hV]
      exact ProbHost.host_tree_common _ par m

end ApicesCommonness
