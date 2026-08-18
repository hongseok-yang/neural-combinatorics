import Taeyoung.Foundation.HomDensity
import Taeyoung.Foundation.ChromaticTarget

/-!
# Common status predicates

Every methodology exports one of these propositions.  The chromatic
polynomial and chromatic number are characterized extensionally, so the
statement is independent of any particular construction of them.
-/

namespace Taeyoung

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge density in the common homomorphism-density normalization. -/
noncomputable def edgeDensity
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) : ℝ :=
  cliqueDensity 2 W

/-- The density interval required for a graph of chromatic number `r`. -/
def admissibleDensity (r : ℕ) (p : ℝ) : Prop :=
  1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ p

/-- The conjectured lower bound, quantified over the unique polynomial and
chromatic number through their defining specifications. -/
def SatisfiesLowerBound
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∀ (P : Polynomial ℝ) (r : ℕ),
    IsChromaticPolynomial H P →
    IsChromaticNumber H r →
    ∀ {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
      [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ),
      admissibleDensity r (edgeDensity W) →
      chromaticTarget (V := V) P (edgeDensity W) ≤ homDensity H W

/-- A negative classification means the common positive statement is false.
Method directories may prove this by packaging an explicit graphon witness. -/
def ViolatesLowerBound
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ¬ SatisfiesLowerBound H

/-- What an open Atlas module is allowed to assert: only excluded middle. -/
theorem status_excludedMiddle
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    SatisfiesLowerBound H ∨ ViolatesLowerBound H :=
  Classical.em _

inductive CatalogueStatus where
  | positive
  | negative
  | open
  deriving DecidableEq, Repr

inductive FormalizationState where
  | verified
  | believed
  | unresolved
  deriving DecidableEq, Repr

end Taeyoung
