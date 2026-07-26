import PureChordal.ChromaticFactorization

/-!
# The pure-chordal graphon inequalities

The two user-facing results for a chordal graph all of whose maximal cliques
have size `r`: the chromatic-polynomial lower bound
(`pureChordal_chromaticPolynomial_lower_bound`) and, at edge density `1 - 1/k`,
the minimality of the balanced complete `k`-partite graphon
(`pureChordal_balancedMultipartite_minimal`).
-/

namespace PureChordal

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} {r : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A chordal graph whose maximal cliques all have size `r` satisfies the
Goodman-style chromatic-polynomial graphon bound.  (Connectivity is not needed:
the certificate factors over connected components.) -/
theorem pureChordal_chromaticPolynomial_lower_bound
    [DecidableRel H.Adj]
    (W : Graphon Ω μ)
    (hchordal : IsChordal H)
    (hpure : HasPureMaximalCliques H r)
    (hr : 3 ≤ r)
    (hp :
      1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W)
    (hne : cliqueDensity 2 W ≠ 1) :
    (1 - cliqueDensity 2 W) ^ Fintype.card V *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (hchordal.pureDecomp hpure).chromaticPolynomial ≤
      homDensity H W := by
  rw [← (hchordal.pureDecomp hpure).certificateBound_eq_eval_chromaticPolynomial
    hne]
  exact (hchordal.pureDecomp hpure).certificateBound_le_homDensity W hr hp

/-- At edge density `1 - 1/k`, the balanced complete `k`-partite graphon is a
minimizer for every certified pure chordal graph whose clique size is at most
`k`. -/
theorem pureChordal_balancedMultipartite_minimal
    [DecidableRel H.Adj]
    (k : ℕ) [NeZero k]
    (W : Graphon Ω μ)
    (hchordal : IsChordal H)
    (hpure : HasPureMaximalCliques H r)
    (hr : 3 ≤ r)
    (hrk : r ≤ k)
    (hedge :
      cliqueDensity 2 W = 1 - 1 / (k : ℝ)) :
    homDensity H (balancedMultipartiteGraphon k) ≤ homDensity H W := by
  let D := hchordal.pureDecomp hpure
  have hrsPos : 0 < (((r - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < r - 1 by omega)
  have hrsLeK : ((r - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (show r - 1 ≤ k by omega)
  have hinv :
      1 / (k : ℝ) ≤ 1 / (((r - 1 : ℕ) : ℝ)) :=
    one_div_le_one_div_of_le hrsPos hrsLeK
  have hthreshold :
      1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W := by
    rw [hedge]
    linarith
  calc
    homDensity H (balancedMultipartiteGraphon k) =
        D.certificateBound
          (cliqueDensity 2 (balancedMultipartiteGraphon k)) :=
      (D.certificateBound_balancedMultipartite k).symm
    _ = D.certificateBound (cliqueDensity 2 W) := by
      rw [edgeDensity_balancedMultipartite, hedge]
    _ ≤ homDensity H W :=
      D.certificateBound_le_homDensity W hr hthreshold

end PureChordal
