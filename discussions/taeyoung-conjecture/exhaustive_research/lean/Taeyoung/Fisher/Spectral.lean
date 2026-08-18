-- Vendored from `discussions/goodman-style-bound/fisher_lean`
-- (`OddCycleBound/Fisher/Spectral.lean`), Lean v4.31.0, Mathlib rev fabf563a.
-- Only the `import` lines differ from the upstream file; see
-- `Taeyoung/Fisher.lean` for why the copy exists.
import Taeyoung.Fisher.ThirdTruncation
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Module 6 — Fisher's spectral lower bound on `r(G)`

Corresponds to `fisher.tex`, Lemma `lem:spectral-growth-bound` and Lemma
`lem:average-degree-spectral`; Module 6 of the blueprint.

* `r(G) ≥ 1 + λ(Ḡ)`, where `λ(Ḡ)` is the largest eigenvalue of the adjacency
  matrix of the complement (walks in the looped complement inject into trace
  classes).
* Rayleigh quotient on the all-ones vector: `λ(Ḡ) ≥ 2·|E(Ḡ)| / n`, hence
  `r(G) ≥ n - 2e/n`.

Analytic content: Perron–Frobenius / largest eigenvalue of a symmetric
nonnegative matrix, and `Matrix.IsHermitian` Rayleigh bounds from Mathlib.
-/

namespace Fisher

open SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The largest Rayleigh quotient of the adjacency matrix of the complement
graph `Gᶜ`.  This is the Perron (largest) eigenvalue; using the Rayleigh
description directly avoids needing a separate Perron--Frobenius API. -/
noncomputable def complSpectralRadius (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ⨆ x : {x : EuclideanSpace ℝ V // x ≠ 0},
    RCLike.re (inner ℝ
      (Matrix.toEuclideanLin ((Gᶜ).adjMatrix ℝ) x) x) /
        ‖(x : EuclideanSpace ℝ V)‖ ^ 2

private lemma card_compl_edges_add_edges :
    (Gᶜ).edgeFinset.card + G.edgeFinset.card = (Fintype.card V).choose 2 := by
  calc
    (Gᶜ).edgeFinset.card + G.edgeFinset.card =
        ((Gᶜ).edgeFinset ∪ G.edgeFinset).card := by
          rw [Finset.card_union_of_disjoint]
          simpa only [SimpleGraph.disjoint_edgeFinset] using
            (disjoint_compl_left : Disjoint Gᶜ G)
    _ = (⊤ : SimpleGraph V).edgeFinset.card := by
      congr 1
      ext e
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
      rw [← Set.mem_union, ← SimpleGraph.edgeSet_sup]
      rw [show Gᶜ ⊔ G = ⊤ by simp]
    _ = (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two

private lemma twice_card_compl_edges_real :
    2 * (((Gᶜ).edgeFinset.card : ℕ) : ℝ) =
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) -
        2 * ((G.edgeFinset.card : ℕ) : ℝ) := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (card_compl_edges_add_edges G)
  rw [Nat.cast_add, Nat.cast_choose_two] at h
  linarith

/-- Rayleigh's bound at the all-ones vector: the complement adjacency
operator norm is at least the average complement degree. -/
private theorem complSpectralRadius_ge_average (hV : 0 < Fintype.card V) :
    2 * (((Gᶜ).edgeFinset.card : ℕ) : ℝ) / (Fintype.card V : ℝ) ≤
      complSpectralRadius G := by
  let A : Matrix V V ℝ := (Gᶜ).adjMatrix ℝ
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  let one : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hone : one ≠ 0 := by
    intro h
    have v : V := Classical.choice (Fintype.card_pos_iff.mp hV)
    have hv := congrArg (fun x : EuclideanSpace ℝ V => WithLp.ofLp x v) h
    simpa [one] using hv
  have hbdd : BddAbove (Set.range fun x : {x : EuclideanSpace ℝ V // x ≠ 0} =>
      T.rayleighQuotient x) := by
    refine ⟨‖T‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (T.rayleighQuotient_le_norm x)
  have hray : T.rayleighQuotient one ≤ complSpectralRadius G := by
    simpa [complSpectralRadius, T, A, ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using
      (le_ciSup (f := fun x : {x : EuclideanSpace ℝ V // x ≠ 0} =>
        T.rayleighQuotient x) hbdd ⟨one, hone⟩)
  have hinner : inner ℝ (T one) one =
      2 * (((Gᶜ).edgeFinset.card : ℕ) : ℝ) := by
    change inner ℝ (WithLp.toLp 2 (A *ᵥ (fun _ => (1 : ℝ))))
      (WithLp.toLp 2 (fun _ => (1 : ℝ))) = _
    rw [EuclideanSpace.inner_toLp_toLp]
    change (fun _ : V => (1 : ℝ)) ⬝ᵥ (A *ᵥ (fun _ => (1 : ℝ))) = _
    rw [dotProduct_comm]
    dsimp [A]
    calc
      ((Gᶜ).adjMatrix ℝ *ᵥ (fun _ => (1 : ℝ))) ⬝ᵥ (fun _ => (1 : ℝ)) =
          (Fintype.card (Gᶜ).Dart : ℝ) := by
            have hdart :=
              SimpleGraph.natCast_card_dart_eq_dotProduct (Gᶜ) (α := ℝ)
            change (Fintype.card (Gᶜ).Dart : ℝ) =
              ((Gᶜ).adjMatrix ℝ *ᵥ (fun _ => (1 : ℝ))) ⬝ᵥ
                (fun _ => (1 : ℝ)) at hdart
            exact hdart.symm
      _ = 2 * (((Gᶜ).edgeFinset.card : ℕ) : ℝ) := by
        rw [SimpleGraph.dart_card_eq_twice_card_edges]
        norm_num
  have hnorm : ‖one‖ ^ 2 = (Fintype.card V : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [one]
  have hray_eq : T.rayleighQuotient one =
      2 * (((Gᶜ).edgeFinset.card : ℕ) : ℝ) / (Fintype.card V : ℝ) := by
    rw [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, hinner, hnorm]
    simp
  rw [hray_eq] at hray
  exact hray

/-- A positive componentwise supersolution bounds the largest Rayleigh
quotient of the complement adjacency matrix. -/
private theorem complSpectralRadius_le_of_supersolution
    [Nonempty V] {y : V → ℝ} {c : ℝ}
    (hy : ∀ v, 0 < y v)
    (hsuper : ∀ v,
      ∑ u ∈ (Gᶜ).neighborFinset v, y u ≤ c * y v) :
    complSpectralRadius G ≤ c := by
  let A : Matrix V V ℝ := (Gᶜ).adjMatrix ℝ
  let L := Matrix.toEuclideanLin A
  have hsym : L.IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      ((Gᶜ).isHermitian_adjMatrix (R := ℝ))
  have heigen0 :=
    LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional
      (𝕜 := ℝ) (E := EuclideanSpace ℝ V) (T := L) hsym
  obtain ⟨z, hz⟩ := heigen0.exists_hasEigenvector
  change z ∈ Module.End.eigenspace L (complSpectralRadius G) ∧ z ≠ 0 at hz
  rcases hz with ⟨hzmem, hz_ne⟩
  let zc : V → ℝ := WithLp.ofLp z
  have hzcoord (v : V) :
      ∑ u ∈ (Gᶜ).neighborFinset v, zc u =
        complSpectralRadius G * zc v := by
    have heq := Module.End.mem_eigenspace_iff.mp hzmem
    have := congrArg (fun w : EuclideanSpace ℝ V => WithLp.ofLp w v) heq
    simpa [L, A, zc, Matrix.toEuclideanLin_apply,
      SimpleGraph.adjMatrix_mulVec_apply, complSpectralRadius,
      ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using this
  obtain ⟨v, -, hvmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V)
      (fun w => |zc w| / y w) Finset.univ_nonempty
  have hcoord : ∃ w, zc w ≠ 0 := by
    by_contra h
    push_neg at h
    apply hz_ne
    ext w
    simpa [zc] using h w
  obtain ⟨w, hw⟩ := hcoord
  have hvratio_pos : 0 < |zc v| / y v := by
    have hwpos : 0 < |zc w| / y w := div_pos (abs_pos.mpr hw) (hy w)
    exact hwpos.trans_le (hvmax w (Finset.mem_univ w))
  have hzv : zc v ≠ 0 := by
    intro hzv
    simp [hzv] at hvratio_pos
  have habsv : 0 < |zc v| := abs_pos.mpr hzv
  have hzu (u : V) : |zc u| ≤ (|zc v| / y v) * y u := by
    have hrat := hvmax u (Finset.mem_univ u)
    exact (div_le_iff₀ (hy u)).mp hrat
  have hsumabs :
      ∑ u ∈ (Gᶜ).neighborFinset v, |zc u| ≤
        (|zc v| / y v) *
          ∑ u ∈ (Gᶜ).neighborFinset v, y u := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u _ => hzu u
  have habseig :
      |complSpectralRadius G| * |zc v| ≤
        (|zc v| / y v) *
          ∑ u ∈ (Gᶜ).neighborFinset v, y u := by
    calc
      |complSpectralRadius G| * |zc v| =
          |∑ u ∈ (Gᶜ).neighborFinset v, zc u| := by
            rw [hzcoord v, abs_mul]
      _ ≤ ∑ u ∈ (Gᶜ).neighborFinset v, |zc u| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := hsumabs
  have hc : 0 ≤ c := by
    have hnonneg : 0 ≤ ∑ u ∈ (Gᶜ).neighborFinset v, y u :=
      Finset.sum_nonneg fun u _ => (hy u).le
    have : 0 ≤ c * y v := hnonneg.trans (hsuper v)
    nlinarith [hy v]
  have habseig' : |complSpectralRadius G| ≤ c := by
    have hfinal : |complSpectralRadius G| * |zc v| ≤ c * |zc v| := calc
      |complSpectralRadius G| * |zc v| ≤
          (|zc v| / y v) *
            ∑ u ∈ (Gᶜ).neighborFinset v, y u := habseig
      _ ≤ (|zc v| / y v) * (c * y v) := by
        exact mul_le_mul_of_nonneg_left (hsuper v)
          (div_nonneg (abs_nonneg _) (hy v).le)
      _ = c * |zc v| := by field_simp [(hy v).ne']
    nlinarith
  exact (le_abs_self _).trans habseig'

/-- **Spectral growth bound** (`lem:spectral-growth-bound`):
`r(G) ≥ 1 + λ(Ḡ)`. -/
theorem growth_ge_one_add_lambda :
    growthFactor G ≥ 1 + complSpectralRadius G := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
      letI := hV
      have hcard : Fintype.card V = 0 := Fintype.card_eq_zero
      letI : IsEmpty {z : EuclideanSpace ℝ V // z ≠ 0} :=
        ⟨fun z => z.2 (Subsingleton.elim z.1 0)⟩
      have hbeta : beta G = 1 := by
        rw [beta]
        simp [positiveRoots, depPoly, hcard, cliqueCount_zero]
      have hcompl : complSpectralRadius G = 0 := by
        simp [complSpectralRadius]
      simp [growthFactor, hbeta, hcompl]
  | inr hV =>
      letI := hV
      have hbound {x : ℝ} (hx0 : 0 < x) (hxb : x < beta G) :
          complSpectralRadius G ≤ 1 / x - 1 := by
        let y : V → ℝ := fun v =>
          (depPoly (G.induce (↑(G.neighborFinset v) : Set V))).eval x
        have hy (v : V) : 0 < y v := by
          apply depPoly_pos_below_beta
          · exact hx0.le
          · exact hxb.trans_le (beta_le_beta_induce G (G.neighborFinset v))
        apply complSpectralRadius_le_of_supersolution G hy
        intro v
        have htel := mul_sum_depPoly_neighbor_le_sub (G := G)
          (G.neighborFinset v) Finset.univ (Finset.subset_univ _)
          hx0.le hxb.le
        have hnonneg : 0 ≤
            (depPoly (G.induce (↑(Finset.univ : Finset V) : Set V))).eval x :=
          depPoly_induced_nonneg_on_Icc G Finset.univ hx0.le hxb.le
        have hpart :
            Finset.univ \ G.neighborFinset v =
              insert v ((Gᶜ).neighborFinset v) := by
          rw [SimpleGraph.neighborFinset_compl]
          ext w
          by_cases hwv : w = v
          · subst w
            simp
          · simp [hwv]
        have htotal :
            x * (y v + ∑ u ∈ (Gᶜ).neighborFinset v, y u) ≤ y v := by
          have h := htel.trans (sub_le_self _ hnonneg)
          rw [hpart] at h
          simpa [y, SimpleGraph.notMem_neighborFinset_self] using h
        have hscaled :
          x * (∑ u ∈ (Gᶜ).neighborFinset v, y u) ≤
            (1 - x) * y v := by nlinarith
        calc
          ∑ u ∈ (Gᶜ).neighborFinset v, y u ≤
              ((1 - x) * y v) / x := (le_div_iff₀ hx0).mpr (by
                simpa [mul_comm] using hscaled)
          _ = (1 / x - 1) * y v := by
            field_simp [hx0.ne']
      by_contra hgoal
      have hlt : growthFactor G < 1 + complSpectralRadius G :=
        lt_of_not_ge hgoal
      have hgrowth : 0 < growthFactor G := by
        exact one_div_pos.mpr (beta_pos G)
      have hc : 0 < 1 + complSpectralRadius G := hgrowth.trans hlt
      have hprod : 1 < beta G * (1 + complSpectralRadius G) := by
        rw [growthFactor] at hlt
        simpa [mul_comm] using (div_lt_iff₀ (beta_pos G)).mp hlt
      let x : ℝ := (1 / (1 + complSpectralRadius G) + beta G) / 2
      have hinvlt : 1 / (1 + complSpectralRadius G) < beta G := by
        exact (div_lt_iff₀ hc).mpr (by simpa [mul_comm] using hprod)
      have hx0 : 0 < x := by
        dsimp [x]
        have : 0 < 1 / (1 + complSpectralRadius G) := div_pos one_pos hc
        linarith
      have hxb : x < beta G := by
        dsimp [x]
        linarith
      have hxinvlower : 1 / (1 + complSpectralRadius G) < x := by
        dsimp [x]
        linarith
      have hone_lt : 1 < (1 + complSpectralRadius G) * x :=
        by simpa [mul_comm] using (div_lt_iff₀ hc).mp hxinvlower
      have hinvupper : 1 / x < 1 + complSpectralRadius G :=
        (div_lt_iff₀ hx0).mpr hone_lt
      have hb := hbound hx0 hxb
      linarith

/-- **Average-degree spectral bound** (`lem:average-degree-spectral`), density
form: `r(G) ≥ n - 2e/n`. -/
theorem growth_ge_avg_degree :
    growthFactor G ≥ nR G - 2 * eR G / nR G := by
  by_cases hV : 0 < Fintype.card V
  · have hn : nR G = (Fintype.card V : ℝ) := by
      simp [nR, cliqueCount_one]
    have he : eR G = (G.edgeFinset.card : ℝ) := by
      simp [eR, cliqueCount_two]
    have hden : (Fintype.card V : ℝ) ≠ 0 := by positivity
    have havg := complSpectralRadius_ge_average G hV
    have hrearrange :
        1 + 2 * (((Gᶜ).edgeFinset.card : ℕ) : ℝ) /
              (Fintype.card V : ℝ) =
          (Fintype.card V : ℝ) -
            2 * ((G.edgeFinset.card : ℕ) : ℝ) /
              (Fintype.card V : ℝ) := by
      rw [twice_card_compl_edges_real G]
      field_simp [hden]
      ring
    calc
      nR G - 2 * eR G / nR G =
          1 + 2 * (((Gᶜ).edgeFinset.card : ℕ) : ℝ) /
            (Fintype.card V : ℝ) := by rw [hn, he, hrearrange]
      _ ≤ 1 + complSpectralRadius G := by linarith
      _ ≤ growthFactor G := growth_ge_one_add_lambda G
  · have hcard : Fintype.card V = 0 := Nat.eq_zero_of_not_pos hV
    have hrhs : nR G - 2 * eR G / nR G = 0 := by
      simp [nR, eR, cliqueCount_one, cliqueCount_two, hcard]
    rw [hrhs]
    exact (one_div_pos.mpr (beta_pos G)).le

end Fisher
