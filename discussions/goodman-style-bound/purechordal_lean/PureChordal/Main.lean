import PureChordal.ChromaticFactorization

namespace PureChordal

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} {r : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A connected chordal graph whose maximal cliques all have size `r`
satisfies the Goodman-style chromatic-polynomial graphon bound. -/
theorem pureChordal_chromaticPolynomial_lower_bound
    [DecidableRel H.Adj]
    (W : Graphon Ω μ)
    (hconnected : H.Connected)
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

end PureChordal
