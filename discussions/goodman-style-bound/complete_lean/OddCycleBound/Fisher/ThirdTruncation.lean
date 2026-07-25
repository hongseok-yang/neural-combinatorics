import OddCycleBound.Fisher.SmallestRoot
import Mathlib.Analysis.Calculus.Taylor

/-!
# Module 5 — Fisher's third-order truncation (Taylor + 4th-derivative positivity)

Corresponds to `fisher.tex`, Lemma `lem:third-truncation` and Lemma
`lem:cubic-root-consequence`; Module 5 of the blueprint.

Using Taylor's theorem with integral remainder at order 3 together with the
derivative identity (Module 2) and induced-subgraph positivity (Module 4):

* `1 - n·β + e·β² - T·β³ ≤ 0`, equivalently `r³ - n r² + e r - T ≤ 0` with
  `r = r(G) = 1/β`.
* Cubic-root consequence: there is `R ≥ r(G)` with `T = φ(R)`, `φ(x) = x³ - n x² + e x`.

Analytic content: `Polynomial.taylor` / `taylor_mean_remainder` (integral form)
and nonnegativity of `D_G^{(4)}` on `[0, β]`.
-/

namespace Fisher

open SimpleGraph Polynomial Set

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Growth factor `r(G) = 1 / beta G`. -/
noncomputable def growthFactor : ℝ := 1 / beta G

/-- Abbreviations for the low-order clique counts as reals. -/
noncomputable def nR : ℝ := (cliqueCount G 1 : ℝ)
noncomputable def eR : ℝ := (cliqueCount G 2 : ℝ)
noncomputable def TR : ℝ := (cliqueCount G 3 : ℝ)

private lemma polynomial_contDiff (p : ℝ[X]) :
    ContDiff ℝ ⊤ (fun x => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a =>
      simp only [eval_monomial]
      fun_prop

private lemma iteratedDeriv_polynomial_eval (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) =
      fun x => (Polynomial.derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simp [Function.iterate_succ_apply']

private lemma taylorWithinEval_polynomial_eq_sum
    (p : ℝ[X]) (b : ℝ) (hb : 0 < b) :
    taylorWithinEval (fun x => p.eval x) 3 (uIcc 0 b) 0 b =
      ∑ k ∈ Finset.range 4,
        ((k.factorial : ℝ)⁻¹ * b ^ k) *
          (Polynomial.derivative^[k] p).eval 0 := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hwithin :
      iteratedDerivWithin k (fun x => p.eval x) (uIcc 0 b) 0 =
        iteratedDeriv k (fun x => p.eval x) 0 := by
    apply iteratedDerivWithin_eq_iteratedDeriv
    · rw [uIcc_of_le hb.le]
      exact uniqueDiffOn_Icc (by grind)
    · exact (polynomial_contDiff p).contDiffAt.of_le (by simp)
    · simp [hb.le]
  rw [hwithin, congrFun (iteratedDeriv_polynomial_eval p k) 0]
  simp

private lemma taylorWithinEval_polynomial_three
    (p : ℝ[X]) (b : ℝ) (hb : 0 < b) :
    taylorWithinEval (fun x => p.eval x) 3 (uIcc 0 b) 0 b =
      p.coeff 0 + p.coeff 1 * b + p.coeff 2 * b ^ 2 + p.coeff 3 * b ^ 3 := by
  rw [taylorWithinEval_polynomial_eq_sum p b hb]
  norm_num [Finset.sum_range_succ]
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  norm_num
  ring

/-- **Third-order truncation** (`lem:third-truncation`):
`1 - n·β + e·β² - T·β³ ≤ 0`. -/
theorem third_truncation (hV : 0 < nR G) :
    1 - nR G * beta G + eR G * (beta G) ^ 2 - TR G * (beta G) ^ 3 ≤ 0 := by
  classical
  have hb : 0 < beta G := beta_pos G
  have hcard : 0 < Fintype.card V := by
    simpa [nR, cliqueCount_one] using hV
  let f : ℝ → ℝ := fun x => (depPoly G).eval x
  obtain ⟨x, hx, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := f) (x₀ := 0) (x := beta G) (n := 3) hb.ne
      ((polynomial_contDiff (depPoly G)).of_le (by norm_num)).contDiffOn
  have hx' : x ∈ Ioo (0 : ℝ) (beta G) := by
    simpa [uIoo_of_le hb.le] using hx
  have hsum :
      0 ≤ ∑ S ∈ G.cliqueFinset 4,
        (depPoly (G.induce (↑(commonNbhd G S) : Set V))).eval x := by
    apply Finset.sum_nonneg
    intro S hS
    exact depPoly_induced_nonneg_on_Icc G (commonNbhd G S) hx'.1.le hx'.2.le
  have hpoly4 :
      0 ≤ (Polynomial.derivative^[4] (depPoly G)).eval x := by
    have hid := congrArg (fun p : ℝ[X] => p.eval x)
      (depPoly_derivative_identity (G := G) 4)
    norm_num at hid
    change 0 ≤ (depPoly G).derivative.derivative.derivative.derivative.eval x
    rw [hid]
    simp only [Polynomial.eval_finsetSum]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) hsum
  have hderiv4 : 0 ≤ iteratedDeriv 4 f x := by
    change 0 ≤ iteratedDeriv 4 (fun y => (depPoly G).eval y) x
    rw [congrFun (iteratedDeriv_polynomial_eval (depPoly G) 4) x]
    exact hpoly4
  have hremainder_nonneg :
      0 ≤ iteratedDeriv 4 f x * (beta G - 0) ^ 4 / (4 : ℕ).factorial := by
    exact div_nonneg (mul_nonneg hderiv4 (by positivity)) (by positivity)
  have htaylor : taylorWithinEval f 3 (uIcc 0 (beta G)) 0 (beta G) ≤ 0 := by
    have hroot : f (beta G) = 0 := by
      exact depPoly_eval_beta G hcard
    rw [hroot, zero_sub] at hrem
    linarith
  rw [show taylorWithinEval f 3 (uIcc 0 (beta G)) 0 (beta G) =
      (depPoly G).coeff 0 + (depPoly G).coeff 1 * beta G +
        (depPoly G).coeff 2 * (beta G) ^ 2 +
        (depPoly G).coeff 3 * (beta G) ^ 3 by
      exact taylorWithinEval_polynomial_three (depPoly G) (beta G) hb] at htaylor
  rw [depPoly_coeff_zero, depPoly_coeff_one, depPoly_coeff_two,
    depPoly_coeff_three] at htaylor
  dsimp [nR, eR, TR]
  linarith

/-- Fisher's cubic in the growth factor: `r³ - n r² + e r - T ≤ 0`. -/
theorem cubic_growth_nonpos (hV : 0 < nR G) :
    (growthFactor G) ^ 3 - nR G * (growthFactor G) ^ 2
        + eR G * growthFactor G - TR G ≤ 0 := by
  have hb : 0 < beta G := beta_pos G
  have hb3 : 0 ≤ (beta G) ^ 3 := (pow_pos hb 3).le
  have hscaled := div_nonpos_of_nonpos_of_nonneg (third_truncation G hV) hb3
  have heq :
      (growthFactor G) ^ 3 - nR G * (growthFactor G) ^ 2
          + eR G * growthFactor G - TR G =
        (1 - nR G * beta G + eR G * (beta G) ^ 2 - TR G * (beta G) ^ 3) /
          (beta G) ^ 3 := by
    dsimp [growthFactor]
    field_simp [hb.ne']
  rw [heq]
  exact hscaled

/-- The cubic `φ(x) = x³ - n x² + e x`. -/
noncomputable def phi (x : ℝ) : ℝ := x ^ 3 - nR G * x ^ 2 + eR G * x

/-- **Cubic-root consequence** (`lem:cubic-root-consequence`): there exists
`R ≥ r(G)` with `T = φ(R)` (intermediate value theorem on `P = φ - T`). -/
theorem exists_root_ge_growth (hV : 0 < nR G) :
    ∃ R : ℝ, growthFactor G ≤ R ∧ TR G = phi G R := by
  let B : ℝ := nR G + eR G + TR G + 1
  let R : ℝ := max (growthFactor G) B
  have hn0 : 0 ≤ nR G := by simp [nR]
  have he0 : 0 ≤ eR G := by simp [eR]
  have hT0 : 0 ≤ TR G := by simp [TR]
  have hgR : growthFactor G ≤ R := by exact le_max_left _ _
  have hBR : B ≤ R := by exact le_max_right _ _
  have hR0 : 0 ≤ R := by
    dsimp [B] at hBR
    linarith
  have hnR : nR G + 1 ≤ R := by
    dsimp [B] at hBR
    linarith
  have hTR : TR G + 1 ≤ R := by
    dsimp [B] at hBR
    linarith
  have hRsq : R ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hlead : R ^ 2 ≤ R ^ 3 - nR G * R ^ 2 := by
    have hgap : 1 ≤ R - nR G := by linarith
    have hmul := mul_le_mul_of_nonneg_left hgap (sq_nonneg R)
    nlinarith
  have heR : 0 ≤ eR G * R := mul_nonneg he0 hR0
  have htop : 0 ≤ phi G R - TR G := by
    dsimp [phi]
    nlinarith
  have hbot : phi G (growthFactor G) - TR G ≤ 0 := by
    simpa [phi] using cubic_growth_nonpos G hV
  have hcont : Continuous (fun x : ℝ ↦ phi G x - TR G) := by
    dsimp [phi]
    fun_prop
  have hzero :
      (0 : ℝ) ∈ Set.Icc (phi G (growthFactor G) - TR G) (phi G R - TR G) :=
    ⟨hbot, htop⟩
  obtain ⟨x, hx, hxeq⟩ := Set.mem_image _ _ _ |>.mp
    (intermediate_value_Icc hgR hcont.continuousOn hzero)
  refine ⟨x, hx.1, ?_⟩
  linarith

end Fisher
