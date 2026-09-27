import EvenCycleApex.Equality.Main

/-!
# The blueprint's declaration names

Plan §6 lists the declarations that `CheckAxioms.lean` must audit, under the blueprint's
`\lean{...}` names.  Where the development states a result in a different form or split into
several lemmas, this file restates it under the blueprint's name (no new mathematics):

* `FiniteKernel.spectral_trace_bounds` — `lem:finite-spectral`, the three trace bounds;
* `apex_number_moment_lifting` — `lem:apex-lifting` (`FiniteKernel.apex_number_moment_lifting`);
* `positive_diagonal_factorization_sound` — `lem:ldl-soundness` (`factorOK_sound`);
* `graph_normalization_sound` — `lem:normalform-soundness`: relabelling preserves densities
  (`evalMask_relabel`), and equal orbit-wise coefficients give equal evaluations
  (`list_sum_eq_of_packed`, DEVIATIONS X3);
* `rooted_quadratic_expansion` — `lem:rooted-expansion`: the signed sum of the skeleton densities
  over the root types is `∑_z ∏ w · ∏_{e ∈ R} (1 ± U_e) · Φ_a Φ_b`;
* `all_certificate_checks` — `prop:checked-data`: every kernel-checked fact of the three
  certificates.
-/

open Finset Matrix

namespace EvenCycleApex

namespace FiniteKernel

/-- **`lem:finite-spectral`.**  For a real symmetric matrix `B`, a unit vector `g` and even
`n ≥ 4`: `Tr B^{2m} ≥ ‖Bg‖^{2m}`, `Tr Bⁿ ≥ ⟨g, Bg⟩ⁿ` and `Tr Bⁿ ≤ (Tr B⁴)^{n/4}`. -/
theorem spectral_trace_bounds {d : ℕ} {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.IsHermitian)
    {g : Fin d → ℝ} (hg : g ⬝ᵥ g = 1) {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) :
    (∀ m : ℕ, ((B *ᵥ g) ⬝ᵥ (B *ᵥ g)) ^ m ≤ trace (B ^ (2 * m))) ∧
      (g ⬝ᵥ (B *ᵥ g)) ^ n ≤ trace (B ^ n) ∧ trace (B ^ n) ≤ trace (B ^ 4) ^ ((n : ℝ) / 4) :=
  ⟨normSq_pow_le_trace_pow hB hg, rayleigh_pow_le_trace_pow hB hg hn,
    trace_pow_le_trace_four_rpow hB hn h4⟩

end FiniteKernel

/-- **`lem:apex-lifting`.**  `A_{n/2,k} ≥ A_{n/2,s}^{k/s} / R_n^{k/s − 1}` on every finite host. -/
theorem apex_number_moment_lifting {d : ℕ} (K : FiniteKernel d) {n s k : ℕ} (hs : 1 ≤ s)
    (hsk : s ≤ k) (hR : 0 < K.R n) :
    K.A n s ^ ((k : ℝ) / s) / K.R n ^ ((k : ℝ) / s - 1) ≤ K.A n k :=
  K.apex_number_moment_lifting hs hsk hR

/-- **`lem:ldl-soundness`.**  A checked rational `LDLᵀ` factorization makes the matrix positive
semidefinite. -/
theorem positive_diagonal_factorization_sound {A : List (List ℤ)}
    {strict : List (List (ℤ × ℕ))} {diag : List (ℤ × ℕ)} (h : factorOK A strict diag = true)
    (x : ℕ → ℝ) :
    0 ≤ ∑ a ∈ range A.length, ∑ b ∈ range A.length,
      x a * (((A.getD a []).getD b 0 : ℤ) : ℝ) * x b :=
  factorOK_sound h x

/-- **`lem:normalform-soundness`.**  A checked permutation code preserves the density of a mask, and
two item lists with equal orbit-wise coefficient sums (equal packed values, total mass `< 2^128`)
have equal evaluations for every choice of orbit representatives. -/
theorem graph_normalization_sound {d : ℕ} (K : FiniteKernel d) :
    (∀ g code : ℕ, isPerm code = true → evalMask K (relabel g code) = evalMask K g) ∧
      ∀ (rep : ℕ → ℕ) {I J : List (ℕ × ℤ)}, packed I = packed J → massOf I + massOf J < 2 ^ 128 →
        itemSum K rep I = itemSum K rep J :=
  ⟨fun g _ hc => evalMask_relabel K g hc, fun rep _ _ hsum hmass =>
    list_sum_eq_of_packed hsum hmass fun o => evalMask K (rep o)⟩

/-- **`lem:rooted-expansion`.**  For a block of shape `(r, k, p)` (block swap `σ`, root mask `R`
of root pairs, features with no root–root edge), the signed sum of the skeleton densities over the
submasks of `R` is `∑_z ∏ w(zᵢ) · ∏_{e ∈ R}(1 ± U_e) · Φ_a(z) Φ_b(z)`. -/
theorem rooted_quadratic_expansion {d r k p : ℕ} (h6 : r + (k + (k + p)) = 6)
    (K : FiniteKernel d) {code : ℕ} (hc : isPerm code = true)
    (hσ : ∀ v : Fin (r + k), Fin.cast h6 (emb2 r k p v) = permOf hc (Fin.cast h6 (emb1 r k p v)))
    {R : ℕ} (hR : ∀ q ∈ maskEdges R, (q.2 : ℕ) < r) (t : ℕ) {fa fb : ℕ}
    (hfa : ∀ q ∈ maskEdges fa, (q.2 : ℕ) < r + k) (hfa' : ∀ q ∈ maskEdges fa, r ≤ (q.2 : ℕ))
    (hfb : ∀ q ∈ maskEdges fb, (q.2 : ℕ) < r + k) (hfb' : ∀ q ∈ maskEdges fb, r ≤ (q.2 : ℕ)) :
    ((subMasks R 15).map fun h => sgnR t h * evalMask K (h ||| fa ||| relabel fb code)).sum
      = ∑ z : Fin r → Fin d, (∏ i, K.w (z i)) * typeFactor K.U z R t *
          featDensity K.w K.U (pull h6 (emb1 r k p) fa) z *
          featDensity K.w K.U (pull h6 (emb1 r k p) fb) z := by
  rw [List.map_congr_left fun h hh => by
    rw [evalMask_skeleton h6 K hc hσ (subMasks_roots hR hh) hfa hfa' hfb hfb', mul_sum]]
  rw [list_sum_finset_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [← typeFactor_expand h6 K.U z hR t]
  have hl : ∀ l : List ℕ, (l.map fun h => sgnR t h * ((∏ i, K.w (z i)) *
        (∏ e ∈ pull h6 (rootV r k p) h, K.U (z e.1) (z e.2)) *
        featDensity K.w K.U (pull h6 (emb1 r k p) fa) z *
        featDensity K.w K.U (pull h6 (emb1 r k p) fb) z)).sum
      = (∏ i, K.w (z i)) * (l.map fun h =>
        sgnR t h * ∏ e ∈ pull h6 (rootV r k p) h, K.U (z e.1) (z e.2)).sum *
        featDensity K.w K.U (pull h6 (emb1 r k p) fa) z *
        featDensity K.w K.U (pull h6 (emb1 r k p) fb) z := by
    intro l
    induction l with
    | nil => simp
    | cons h l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  exact hl _

/-- **`prop:checked-data`.**  The kernel-checked facts of the three certificates on the proof path
(`P_mean,3`, `P₋`, `P₊`; `P_mean,2` is excluded by plan D10): every group of every certificate
is valid (schema, skeleton witnesses, 57 `LDLᵀ` factorizations), the group totals are the claimed
ones, every target chunk checks, and the weighted totals agree (identity (C) with mass `< 2^128`). -/
theorem all_certificate_checks :
    ((∀ G ∈ meanThreeGroups, G.valid Certificate.Data.rep) ∧
        List.Forall₂ GroupCert.Totals meanThreeGroups Checks.meanThreeClaims ∧
        (∀ k < Certificate.Data.MeanThree.WtChunks.length,
          tchunk Certificate.Data.rep 1024 targetMeanThree k
            (Certificate.Data.MeanThree.WtChunks.getD k [])
            (Certificate.Data.MeanThree.claimsT.getD k (0, 0, 0)) = true) ∧
        totalsOK certScale (sum3 Certificate.Data.MeanThree.claimsT) Checks.meanThreeClaims = true) ∧
      ((∀ G ∈ negGroups, G.valid Certificate.Data.rep) ∧
        List.Forall₂ GroupCert.Totals negGroups Checks.negClaims ∧
        (∀ k < Certificate.Data.Neg.WtChunks.length,
          tchunk Certificate.Data.rep 1024 targetNeg k (Certificate.Data.Neg.WtChunks.getD k [])
            (Certificate.Data.Neg.claimsT.getD k (0, 0, 0)) = true) ∧
        totalsOK certScale (sum3 Certificate.Data.Neg.claimsT) Checks.negClaims = true) ∧
      ((∀ G ∈ posGroups, G.valid Certificate.Data.rep) ∧
        List.Forall₂ GroupCert.Totals posGroups Checks.posClaims ∧
        (∀ k < Certificate.Data.Pos.WtChunks.length,
          tchunk Certificate.Data.rep 1024 targetPos k (Certificate.Data.Pos.WtChunks.getD k [])
            (Certificate.Data.Pos.claimsT.getD k (0, 0, 0)) = true) ∧
        totalsOK certScale (sum3 Certificate.Data.Pos.claimsT) Checks.posClaims = true) :=
  ⟨⟨Checks.meanThree_valid, Checks.meanThree_totals, Checks.meanThree_chunks, Checks.meanThree_fin⟩,
    ⟨Checks.neg_valid, Checks.neg_totals, Checks.neg_chunks, Checks.neg_fin⟩,
    ⟨Checks.pos_valid, Checks.pos_totals, Checks.pos_chunks, Checks.pos_fin⟩⟩

end EvenCycleApex
