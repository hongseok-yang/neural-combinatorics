import Taeyoung.Methods.PureChordal.EntropyGluing
import Taeyoung.Methods.PureChordal.CliquePolynomialBound

/-!
# Polynomial lower bound from a pure clique-tree certificate

This file combines the graphon clique-tree gluing inequality with the
Moon--Moser clique-polynomial bounds.  It is the complete analytic theorem:
the remaining wrapper only has to construct a certificate from a pure chordal
graph and identify the explicit product with its chromatic polynomial.
-/

namespace Taeyoung.Methods.PureChordal

open MeasureTheory
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} {r m : ℕ}
variable (D : PureCliqueTreeDecomp H r m)
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

namespace PureCliqueTreeDecomp

/-- The tail of the clique polynomial from size `s` to size `r`. -/
def cliquePolyTail (s r : ℕ) (p : ℝ) : ℝ :=
  ∏ j ∈ Finset.Ico s r, (1 - (j : ℝ) * (1 - p))

/-- Denominator-free polynomial attached to a rooted pure clique tree.
The root contributes `A_r`; every other bag contributes the tail from its
separator size to `r`. -/
def certificateBound (p : ℝ) : ℝ :=
  ∏ i : Fin m,
    if i = D.root then cliquePoly r p
    else cliquePolyTail (D.separator i).card r p

lemma cliquePoly_mul_tail_eq
    {s : ℕ} (hs : s ≤ r) (p : ℝ) :
    cliquePoly s p * cliquePolyTail s r p = cliquePoly r p := by
  rw [cliquePolyTail, cliquePoly_mul_tail s r hs p]

lemma separatorPoly_mul_certificateFactor
    (p : ℝ) (i : Fin m) :
    cliquePoly (D.separator i).card p *
        (if i = D.root then cliquePoly r p
          else cliquePolyTail (D.separator i).card r p) =
      cliquePoly r p := by
  by_cases hi : i = D.root
  · subst i
    simp
  · simp only [hi, ↓reduceIte]
    exact cliquePoly_mul_tail_eq (D.sepCard_le i) p

lemma separatorPolyProduct_mul_certificateBound
    (p : ℝ) :
    (∏ i : Fin m, cliquePoly (D.separator i).card p) *
        D.certificateBound p =
      (cliquePoly r p) ^ m := by
  rw [certificateBound, ← Finset.prod_mul_distrib]
  calc
    ∏ i : Fin m,
        (cliquePoly (D.separator i).card p *
          if i = D.root then cliquePoly r p
          else cliquePolyTail (D.separator i).card r p) =
        ∏ _i : Fin m, cliquePoly r p := by
      apply Finset.prod_congr rfl
      intro i hi
      exact D.separatorPoly_mul_certificateFactor p i
    _ = (cliquePoly r p) ^ m := by simp

lemma separatorCliquePoly_pos
    (hr : 3 ≤ r) {p : ℝ}
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ p)
    (i : Fin m) :
    0 < cliquePoly (D.separator i).card p := by
  by_cases hi : i = D.root
  · subst i
    simp
  · exact cliquePoly_pos_of_lt_threshold hr (D.sepCard_lt hi) hp

lemma separatorCliqueDensity_pos
    (W : Graphon Ω μ) (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W)
    (i : Fin m) :
    0 < cliqueDensity (D.separator i).card W := by
  exact lt_of_lt_of_le
    (D.separatorCliquePoly_pos hr hp i)
    (cliqueDensity_ge_cliquePoly W hr hp (D.sepCard_le i))

/-- Product of the iterated clique-ratio inequalities over every separator. -/
theorem separatorDensity_mul_cliquePoly_pow_le
    (W : Graphon Ω μ) (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W) :
    (∏ i : Fin m, cliqueDensity (D.separator i).card W) *
        (cliquePoly r (cliqueDensity 2 W)) ^ m ≤
      (cliqueDensity r W) ^ m *
        ∏ i : Fin m,
          cliquePoly (D.separator i).card (cliqueDensity 2 W) := by
  have hprod :
      (∏ i : Fin m,
          cliqueDensity (D.separator i).card W *
            cliquePoly r (cliqueDensity 2 W)) ≤
        ∏ i : Fin m,
          cliqueDensity r W *
            cliquePoly (D.separator i).card (cliqueDensity 2 W) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact mul_nonneg
        (cliqueDensity_nonneg _ W)
        (cliquePoly_nonneg_of_threshold hr le_rfl hp)
    · intro i hi
      exact cliqueDensity_mul_cliquePoly_le W hr hp
        (D.sepCard_le i) le_rfl
  simpa [Finset.prod_mul_distrib] using hprod

/-- Cross-multiplied certificate form of the pure-chordal polynomial bound. -/
theorem cliquePoly_pow_le_homDensity_mul_separatorPoly
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W) :
    (cliquePoly r (cliqueDensity 2 W)) ^ m ≤
      homDensity H W *
        ∏ i : Fin m,
          cliquePoly (D.separator i).card (cliqueDensity 2 W) := by
  let S : ℝ :=
    ∏ i : Fin m, cliqueDensity (D.separator i).card W
  let A : ℝ :=
    ∏ i : Fin m,
      cliquePoly (D.separator i).card (cliqueDensity 2 W)
  have hSpos : 0 < S := by
    dsimp [S]
    exact Finset.prod_pos fun i _ =>
      D.separatorCliqueDensity_pos W hr hp i
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.prod_nonneg fun i _ =>
      cliquePoly_nonneg_of_threshold hr (D.sepCard_le i) hp
  have hratio :
      S * (cliquePoly r (cliqueDensity 2 W)) ^ m ≤
        (cliqueDensity r W) ^ m * A := by
    simpa [S, A] using
      D.separatorDensity_mul_cliquePoly_pow_le W hr hp
  have hglue :
      (cliqueDensity r W) ^ m ≤ homDensity H W * S := by
    simpa [S] using D.homDensity_mul_sep_ge_cliqueDensity_pow W
  have hmul :
      S * (cliquePoly r (cliqueDensity 2 W)) ^ m ≤
        S * (homDensity H W * A) := by
    calc
      S * (cliquePoly r (cliqueDensity 2 W)) ^ m
          ≤ (cliqueDensity r W) ^ m * A := hratio
      _ ≤ (homDensity H W * S) * A :=
        mul_le_mul_of_nonneg_right hglue hA0
      _ = S * (homDensity H W * A) := by ring
  exact le_of_mul_le_mul_left hmul hSpos

/-- The requested polynomial lower bound in a form with no division. -/
theorem certificateBound_le_homDensity
    [DecidableRel H.Adj]
    (W : Graphon Ω μ) (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W) :
    D.certificateBound (cliqueDensity 2 W) ≤ homDensity H W := by
  let A : ℝ :=
    ∏ i : Fin m,
      cliquePoly (D.separator i).card (cliqueDensity 2 W)
  have hApos : 0 < A := by
    dsimp [A]
    exact Finset.prod_pos fun i _ => D.separatorCliquePoly_pos hr hp i
  have hcross :=
    D.cliquePoly_pow_le_homDensity_mul_separatorPoly W hr hp
  have hid :=
    D.separatorPolyProduct_mul_certificateBound (cliqueDensity 2 W)
  have hmul :
      A * D.certificateBound (cliqueDensity 2 W) ≤
        A * homDensity H W := by
    rw [hid]
    simpa [A, mul_comm] using hcross
  exact le_of_mul_le_mul_left hmul hApos

end PureCliqueTreeDecomp

end Taeyoung.Methods.PureChordal
