import OddCycleBound.Fisher.DependencePolynomial

/-!
# Module 4 — Smallest positive root and induced-subgraph monotonicity

Corresponds to `fisher.tex`, Lemma `lem:smallest-positive-zero`, Definition
(growth factor), Lemma `lem:induced-monotonicity`; Module 4 of the blueprint.

* `beta G` = the smallest positive zero of `D_G` (radius of convergence of
  `1/D_G`, via Pringsheim on the nonnegative coefficients `a_k`).
* `D_G(x) > 0` for `0 ≤ x < beta G`.
* Induced-subgraph monotonicity: `H ⊆ᵢ G ⇒ beta G ≤ beta H`, hence
  `D_H ≥ 0` on `[0, beta G]`.

Uses Module 2 (dependence polynomial) and Module 3 (nonnegative trace counts).
-/

namespace Fisher

open SimpleGraph Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The finite set of positive real zeros of the dependence polynomial. -/
noncomputable def positiveRoots (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℝ :=
  ((Polynomial.rootSet_finite (depPoly G) ℝ).toFinset).filter (0 < ·)

/-- The smallest positive zero of the dependence polynomial, with the harmless
default value `1` when the graph has no vertices. -/
noncomputable def beta (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if h : (positiveRoots G).Nonempty then (positiveRoots G).min' h else 1

theorem positiveRoots_iso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (f : G ≃g H) :
    positiveRoots G = positiveRoots H := by
  simp only [positiveRoots, depPoly_iso G f]

theorem beta_iso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (f : G ≃g H) :
    beta G = beta H := by
  rw [beta, beta, positiveRoots_iso G f]

/-- `beta G > 0`. -/
theorem beta_pos : 0 < beta G := by
  rw [beta]
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.min'_mem (positiveRoots G) h)).2
  · norm_num

private theorem depPoly_ne_zero : depPoly G ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  rw [depPoly_coeff_zero] at hcoeff
  norm_num at hcoeff

private theorem depPoly_eval_beta_of_nonempty
    (hnonempty : (positiveRoots G).Nonempty) :
    (depPoly G).eval (beta G) = 0 := by
  have hmem : beta G ∈ positiveRoots G := by
    rw [beta, dif_pos hnonempty]
    exact Finset.min'_mem _ _
  have hroot : beta G ∈ (depPoly G).rootSet ℝ := by
    apply (Polynomial.rootSet_finite (depPoly G) ℝ).mem_toFinset.mp
    exact (Finset.mem_filter.mp hmem).1
  have heval := (Polynomial.mem_rootSet_of_ne (depPoly_ne_zero G)).mp hroot
  simpa [aeval_def] using heval

/-- `D_G` is positive strictly below its first positive zero. -/
theorem depPoly_pos_below_beta {x : ℝ} (hx0 : 0 ≤ x) (hx : x < beta G) :
    0 < (depPoly G).eval x := by
  by_contra hpos
  have hxle : (depPoly G).eval x ≤ 0 := le_of_not_gt hpos
  have hcont : Continuous (fun y : ℝ => (depPoly G).eval y) :=
    (depPoly G).differentiable.continuous
  have hzero :
      (0 : ℝ) ∈ Set.Icc ((depPoly G).eval x) ((depPoly G).eval 0) := by
    rw [depPoly_eval_zero]
    exact ⟨hxle, by norm_num⟩
  obtain ⟨y, hy, hyeval⟩ := Set.mem_image _ _ _ |>.mp
    (intermediate_value_Icc' hx0 hcont.continuousOn hzero)
  have hypos : 0 < y := by
    apply lt_of_le_of_ne hy.1
    intro hy0
    subst y
    rw [depPoly_eval_zero] at hyeval
    norm_num at hyeval
  have hyroot : y ∈ (depPoly G).rootSet ℝ := by
    apply (Polynomial.mem_rootSet_of_ne (depPoly_ne_zero G)).mpr
    simpa [aeval_def] using hyeval
  have hymem : y ∈ positiveRoots G := by
    rw [positiveRoots, Finset.mem_filter]
    exact ⟨(Polynomial.rootSet_finite (depPoly G) ℝ).mem_toFinset.mpr hyroot, hypos⟩
  have hbeta_le : beta G ≤ y := by
    have hn : (positiveRoots G).Nonempty := ⟨y, hymem⟩
    rw [beta, dif_pos hn]
    exact Finset.min'_le _ y hymem
  linarith [hy.2]

private theorem positiveRoots_nonempty_and_beta_le_of_eval_nonpos
    {b : ℝ} (hb : 0 < b) (heval : (depPoly G).eval b ≤ 0) :
    (positiveRoots G).Nonempty ∧ beta G ≤ b := by
  have hcont : Continuous (fun y : ℝ => (depPoly G).eval y) :=
    (depPoly G).differentiable.continuous
  have hzero :
      (0 : ℝ) ∈ Set.Icc ((depPoly G).eval b) ((depPoly G).eval 0) := by
    rw [depPoly_eval_zero]
    exact ⟨heval, by norm_num⟩
  obtain ⟨y, hy, hyeval⟩ := Set.mem_image _ _ _ |>.mp
    (intermediate_value_Icc' hb.le hcont.continuousOn hzero)
  have hypos : 0 < y := by
    apply lt_of_le_of_ne hy.1
    intro hy0
    subst y
    rw [depPoly_eval_zero] at hyeval
    norm_num at hyeval
  have hyroot : y ∈ (depPoly G).rootSet ℝ := by
    apply (Polynomial.mem_rootSet_of_ne (depPoly_ne_zero G)).mpr
    simpa [aeval_def] using hyeval
  have hymem : y ∈ positiveRoots G := by
    rw [positiveRoots, Finset.mem_filter]
    exact ⟨(Polynomial.rootSet_finite (depPoly G) ℝ).mem_toFinset.mpr hyroot, hypos⟩
  have hn : (positiveRoots G).Nonempty := ⟨y, hymem⟩
  refine ⟨hn, ?_⟩
  rw [beta, dif_pos hn]
  exact (Finset.min'_le _ y hymem).trans hy.2

private def induceFinsetUnivIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    G.induce (↑(Finset.univ : Finset V) : Set V) ≃g G where
  toEquiv :=
    ({ toFun := fun x : (↑(Finset.univ : Finset V) : Set V) => x.1
       invFun := fun x : V => ⟨x, Finset.mem_univ x⟩
       left_inv := fun x => Subtype.ext (by rfl)
       right_inv := fun _ => rfl } :
      (↑(Finset.univ : Finset V) : Set V) ≃ V)
  map_rel_iff' := Iff.rfl

private theorem rootAndMono
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 < Fintype.card V → (positiveRoots G).Nonempty) ∧
      ∀ S : Finset V, beta G ≤ beta (G.induce (↑S : Set V)) := by
  classical
  have deletionStep (v : V) :
      (positiveRoots G).Nonempty ∧
        beta G ≤ beta (G.induce (↑(Finset.univ.erase v) : Set V)) := by
    let D : Finset V := Finset.univ.erase v
    let H := G.induce (↑D : Set V)
    let T : Finset V := commonNbhd G {v}
    let K := G.induce (↑T : Set V)
    have hDcard : D.card < Fintype.card V := by
      simpa [D] using
        (Finset.card_erase_lt_of_mem (s := (Finset.univ : Finset V))
          (Finset.mem_univ v))
    have ihH := rootAndMono H
    have hTS : T ⊆ D := by
      intro x hx
      change x ∈ commonNbhd G {v} at hx
      rw [commonNbhd, Finset.mem_filter] at hx
      change x ∈ Finset.univ.erase v
      rw [Finset.mem_erase]
      exact ⟨by simpa using hx.2.1, Finset.mem_univ x⟩
    let T' : Finset (↑D : Set V) := T.subtype fun x => x ∈ D
    let K' := H.induce (↑T' : Set (↑D : Set V))
    let e : K ≃g K' := induceSubsetIso G hTS
    have hK'lt : Fintype.card (↑T' : Set (↑D : Set V)) < Fintype.card V := by
      have hle : T'.card ≤ Fintype.card (↑D : Set V) := Finset.card_le_univ T'
      simpa using hle.trans_lt (by simpa using hDcard)
    have hbetaK : beta H ≤ beta K := by
      have hnested := ihH.2 T'
      exact hnested.trans_eq (beta_iso K e).symm
    have hKnonneg : 0 ≤ (depPoly K).eval (beta H) := by
      rcases hbetaK.lt_or_eq with hlt | heq
      · exact (depPoly_pos_below_beta K (beta_pos H).le hlt).le
      · by_cases hKcard : 0 < Fintype.card (↑T : Set V)
        · have hK'card : 0 < Fintype.card (↑T' : Set (↑D : Set V)) := by
            rw [Fintype.card_congr e.toEquiv.symm]
            exact hKcard
          have hK'roots := (rootAndMono K').1 hK'card
          have hKroots : (positiveRoots K).Nonempty := by
            rw [positiveRoots_iso K e]
            exact hK'roots
          rw [heq, depPoly_eval_beta_of_nonempty K hKroots]
        · have hTcard : T.card = 0 := by
            have : Fintype.card (↑T : Set V) = 0 := Nat.eq_zero_of_not_pos hKcard
            simpa using this
          simp [K, depPoly, hTcard, cliqueCount_zero]
    have hGnonpos : (depPoly G).eval (beta H) ≤ 0 := by
      have hrec := congrArg (fun p : ℝ[X] => p.eval (beta H))
        (depPoly_delete_vertex G v)
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at hrec
      change (depPoly G).eval (beta H) =
        (depPoly H).eval (beta H) - beta H * (depPoly K).eval (beta H) at hrec
      by_cases hHcard : 0 < Fintype.card (↑D : Set V)
      · have hHroots := ihH.1 hHcard
        rw [depPoly_eval_beta_of_nonempty H hHroots] at hrec
        rw [hrec]
        exact sub_nonpos.mpr (mul_nonneg (beta_pos H).le hKnonneg)
      · have hDcard0 : D.card = 0 := by
          have : Fintype.card (↑D : Set V) = 0 := Nat.eq_zero_of_not_pos hHcard
          simpa using this
        have hTcard0 : T.card = 0 := Nat.eq_zero_of_le_zero
          ((Finset.card_le_card hTS).trans_eq hDcard0)
        have hbetaH : beta H = 1 := by
          simp [H, beta, positiveRoots, depPoly, hDcard0, cliqueCount_zero]
        have hHeval : (depPoly H).eval (beta H) = 1 := by
          simp [H, depPoly, hDcard0, cliqueCount_zero]
        have hKeval : (depPoly K).eval (beta H) = 1 := by
          simp [K, depPoly, hTcard0, cliqueCount_zero]
        rw [hrec, hHeval, hKeval, hbetaH]
        norm_num
    simpa [H, D] using
      (positiveRoots_nonempty_and_beta_le_of_eval_nonpos G (beta_pos H) hGnonpos)
  constructor
  · intro hV
    let v : V := Classical.choice (Fintype.card_pos_iff.mp hV)
    exact (deletionStep v).1
  · intro S
    by_cases hS : S = Finset.univ
    · subst S
      exact (beta_iso (G.induce (↑(Finset.univ : Finset V) : Set V))
        (induceFinsetUnivIso G)).symm.le
    · obtain ⟨v, hv⟩ : ∃ v : V, v ∉ S := by
        simpa [Finset.eq_univ_iff_forall] using hS
      let D : Finset V := Finset.univ.erase v
      let H := G.induce (↑D : Set V)
      have hSD : S ⊆ D := by
        intro x hx
        change x ∈ Finset.univ.erase v
        rw [Finset.mem_erase]
        exact ⟨fun hxv => hv (hxv ▸ hx), Finset.mem_univ x⟩
      let S' : Finset (↑D : Set V) := S.subtype fun x => x ∈ D
      let e : G.induce (↑S : Set V) ≃g
          H.induce (↑S' : Set (↑D : Set V)) := induceSubsetIso G hSD
      have hdel := (deletionStep v).2
      have hDcard : D.card < Fintype.card V := by
        simpa [D] using
          (Finset.card_erase_lt_of_mem (s := (Finset.univ : Finset V))
            (Finset.mem_univ v))
      have ihH := rootAndMono H
      have hmono := ihH.2 S'
      exact hdel.trans (hmono.trans_eq (beta_iso (G.induce (↑S : Set V)) e).symm)
termination_by Fintype.card V
decreasing_by
  · simpa [H, D] using hDcard
  · exact hK'lt
  · simpa [H, D] using hDcard

/-- A nonempty finite graph has a positive real zero of its dependence
polynomial. -/
theorem positiveRoots_nonempty (hV : 0 < Fintype.card V) :
    (positiveRoots G).Nonempty :=
  (rootAndMono G).1 hV

/-- `D_G(beta G) = 0`. -/
theorem depPoly_eval_beta (hV : 0 < Fintype.card V) :
    (depPoly G).eval (beta G) = 0 :=
  depPoly_eval_beta_of_nonempty G (positiveRoots_nonempty G hV)

/-- **Induced-subgraph monotonicity of `D` on `[0, beta G]`** (`lem:induced-monotonicity`).
For any induced subgraph `H` of `G`, `D_H ≥ 0` throughout `[0, beta G]`.  This is
the exact positivity fact consumed by the fourth-derivative estimate in Module 5.

Stated here for the induced common-neighbourhood subgraphs of Module 1; the
general induced-subgraph version follows the same trace-injection argument. -/
theorem beta_le_beta_induce (S : Finset V) :
    beta G ≤ beta (G.induce (↑S : Set V)) := by
  exact (rootAndMono G).2 S

theorem depPoly_induced_nonneg_on_Icc
    (S : Finset V) {x : ℝ} (hx0 : 0 ≤ x) (hxb : x ≤ beta G) :
    0 ≤ (depPoly (G.induce (↑S : Set V))).eval x := by
  let H := G.induce (↑S : Set V)
  have hxbet : x ≤ beta H := hxb.trans (beta_le_beta_induce G S)
  rcases hxbet.lt_or_eq with hlt | heq
  · exact (depPoly_pos_below_beta H hx0 hlt).le
  · by_cases hcard : 0 < Fintype.card (↑S : Set V)
    · rw [heq, depPoly_eval_beta H hcard]
    · have hcard0 : Fintype.card (↑S : Set V) = 0 := by omega
      have hScard : S.card = 0 := by simpa using hcard0
      simp [depPoly, hScard, cliqueCount_zero]

/-- On the interval before the first positive root, deleting vertices can only
increase the dependence polynomial.  This is the finite monotonicity form
needed for the spectral supersolution argument. -/
theorem depPoly_eval_induce_anti
    (S T : Finset V) (hST : S ⊆ T) {x : ℝ}
    (hx0 : 0 ≤ x) (hxb : x ≤ beta G) :
    (depPoly (G.induce (↑T : Set V))).eval x ≤
      (depPoly (G.induce (↑S : Set V))).eval x := by
  classical
  by_cases hEq : S = T
  · subst T
    exact le_rfl
  · obtain ⟨v, hvT, hvS⟩ : ∃ v, v ∈ T ∧ v ∉ S := by
      have hstrict : S ⊂ T :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hST, hEq⟩
      obtain ⟨v, hvT, hsub⟩ :=
        Finset.ssubset_iff_exists_subset_erase.mp hstrict
      exact ⟨v, hvT, fun hvS =>
        (Finset.mem_erase.mp (hsub hvS)).1 rfl⟩
    let H := G.induce (↑T : Set V)
    let vT : (↑T : Set V) := ⟨v, hvT⟩
    let T' : Finset (↑T : Set V) :=
      (T.erase v).subtype (fun w => w ∈ T)
    have hT' : T' = Finset.univ.erase vT := by
      ext w
      simp [T', vT, Subtype.ext_iff]
    have hxbH : x ≤ beta H :=
      hxb.trans (beta_le_beta_induce G T)
    have hlink : 0 ≤
        (depPoly (H.induce
          (↑(commonNbhd H {vT}) : Set (↑T : Set V)))).eval x :=
      depPoly_induced_nonneg_on_Icc H (commonNbhd H {vT}) hx0 hxbH
    have hdelete :
        (depPoly H).eval x ≤
          (depPoly (H.induce (↑T' : Set (↑T : Set V)))).eval x := by
      have hrec := congrArg (fun p : ℝ[X] => p.eval x)
        (depPoly_delete_vertex H vT)
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at hrec
      rw [← hT'] at hrec
      rw [hrec]
      exact sub_le_self _ (mul_nonneg hx0 hlink)
    let e : G.induce (↑(T.erase v) : Set V) ≃g
        H.induce (↑T' : Set (↑T : Set V)) :=
      induceSubsetIso G (Finset.erase_subset v T)
    have hdelete' :
        (depPoly (G.induce (↑T : Set V))).eval x ≤
          (depPoly (G.induce (↑(T.erase v) : Set V))).eval x := by
      calc
        (depPoly (G.induce (↑T : Set V))).eval x = (depPoly H).eval x := rfl
        _ ≤ (depPoly (H.induce (↑T' : Set (↑T : Set V)))).eval x := hdelete
        _ = (depPoly (G.induce (↑(T.erase v) : Set V))).eval x := by
          rw [depPoly_iso (G.induce (↑(T.erase v) : Set V)) e]
    have hSerase : S ⊆ T.erase v := by
      intro w hw
      exact Finset.mem_erase.mpr ⟨fun hwv => hvS (hwv ▸ hw), hST hw⟩
    exact hdelete'.trans
      (depPoly_eval_induce_anti S (T.erase v) hSerase hx0 hxb)
termination_by T.card
decreasing_by
  exact Finset.card_erase_lt_of_mem hvT

/-- A quantitative form of deletion monotonicity.  The loss in `D` from
adding the vertices in `T \ S` dominates the sum of their ambient link
polynomials. -/
theorem mul_sum_depPoly_neighbor_le_sub
    (S T : Finset V) (hST : S ⊆ T) {x : ℝ}
    (hx0 : 0 ≤ x) (hxb : x ≤ beta G) :
    x * ∑ v ∈ T \ S,
        (depPoly (G.induce (↑(G.neighborFinset v) : Set V))).eval x ≤
      (depPoly (G.induce (↑S : Set V))).eval x -
        (depPoly (G.induce (↑T : Set V))).eval x := by
  classical
  by_cases hEq : S = T
  · subst T
    simp
  · have hnon : (T \ S).Nonempty := Finset.sdiff_nonempty.mpr (by
      intro hTS
      apply hEq
      ext w
      exact ⟨fun hw => hST hw, fun hw => hTS hw⟩)
    obtain ⟨v, hv⟩ := hnon
    have hvT : v ∈ T := (Finset.mem_sdiff.mp hv).1
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    let H := G.induce (↑T : Set V)
    let vT : (↑T : Set V) := ⟨v, hvT⟩
    let T' : Finset (↑T : Set V) :=
      (T.erase v).subtype (fun w => w ∈ T)
    have hT' : T' = Finset.univ.erase vT := by
      ext w
      simp [T', vT, Subtype.ext_iff]
    let U : Finset V := G.neighborFinset v ∩ T.erase v
    let U' : Finset (↑T : Set V) := U.subtype (fun w => w ∈ T)
    have hU' : U' = commonNbhd H {vT} := by
      ext w
      simp [U', U, H, vT, commonNbhd, SimpleGraph.mem_neighborFinset,
        SimpleGraph.adj_comm]
      constructor
      · rintro ⟨ha, hne⟩
        exact ⟨fun h => hne (congrArg Subtype.val h), ha⟩
      · rintro ⟨hne, ha⟩
        exact ⟨ha, fun h => G.loopless.irrefl v (h ▸ ha)⟩
    let eU : G.induce (↑U : Set V) ≃g H.induce (↑U' : Set (↑T : Set V)) :=
      induceSubsetIso G (by
        intro w hw
        exact (Finset.mem_erase.mp (Finset.mem_inter.mp hw).2).2)
    have hUsub : U ⊆ G.neighborFinset v := Finset.inter_subset_left
    have hlinkcompare :
        (depPoly (G.induce (↑(G.neighborFinset v) : Set V))).eval x ≤
          (depPoly (H.induce
            (↑(commonNbhd H {vT}) : Set (↑T : Set V)))).eval x := by
      have hmono := depPoly_eval_induce_anti (G := G) U
        (G.neighborFinset v) hUsub hx0 hxb
      rw [← hU']
      calc
        (depPoly (G.induce (↑(G.neighborFinset v) : Set V))).eval x ≤
            (depPoly (G.induce (↑U : Set V))).eval x := hmono
        _ = (depPoly (H.induce (↑U' : Set (↑T : Set V)))).eval x := by
          rw [← depPoly_iso (G.induce (↑U : Set V)) eU]
    have hrec :
        (depPoly (G.induce (↑T : Set V))).eval x =
          (depPoly (G.induce (↑(T.erase v) : Set V))).eval x -
            x * (depPoly (H.induce
              (↑(commonNbhd H {vT}) : Set (↑T : Set V)))).eval x := by
      have h := congrArg (fun p : ℝ[X] => p.eval x)
        (depPoly_delete_vertex H vT)
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
      rw [← hT'] at h
      let eT : G.induce (↑(T.erase v) : Set V) ≃g
          H.induce (↑T' : Set (↑T : Set V)) :=
        induceSubsetIso G (Finset.erase_subset v T)
      calc
        (depPoly (G.induce (↑T : Set V))).eval x = (depPoly H).eval x := rfl
        _ = (depPoly (H.induce (↑T' : Set (↑T : Set V)))).eval x -
            x * (depPoly (H.induce
              (↑(commonNbhd H {vT}) : Set (↑T : Set V)))).eval x := h
        _ = _ := by rw [← depPoly_iso (G.induce (↑(T.erase v) : Set V)) eT]
    have hSerase : S ⊆ T.erase v := by
      intro w hw
      exact Finset.mem_erase.mpr ⟨fun hwv => hvS (hwv ▸ hw), hST hw⟩
    have ih := mul_sum_depPoly_neighbor_le_sub
      S (T.erase v) hSerase hx0 hxb
    have hsdiff : (T.erase v) \ S = (T \ S).erase v := by
      ext w
      simp [and_assoc, and_left_comm]
    have hvDiff : v ∈ T \ S := Finset.mem_sdiff.mpr ⟨hvT, hvS⟩
    rw [hsdiff] at ih
    have hsum :
        (∑ w ∈ T \ S,
          (depPoly (G.induce (↑(G.neighborFinset w) : Set V))).eval x) =
        (∑ w ∈ (T \ S).erase v,
          (depPoly (G.induce (↑(G.neighborFinset w) : Set V))).eval x) +
          (depPoly (G.induce (↑(G.neighborFinset v) : Set V))).eval x := by
      symm
      exact Finset.sum_erase_add _ _ hvDiff
    rw [hrec, hsum]
    nlinarith [mul_le_mul_of_nonneg_left hlinkcompare hx0]
termination_by T.card
decreasing_by
  exact Finset.card_erase_lt_of_mem hvT

end Fisher
