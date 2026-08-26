import Taeyoung.Methods.RootedSOS.FlagEvaluation
import Taeyoung.Methods.RootedSOS.QuadraticExpansion

/-!
# Linear combinations of rooted flags

S4 symmetry and the stored Gram factors are ordinary finite linear maps on
the raw rooted-flag vector.  These lemmas expand those maps before applying
the generic shared-Bernoulli gluing identity.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

open Taeyoung

variable {k : ℕ}
variable {A I : Type*} [Fintype A] [Fintype I]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Raw rooted-flag vector attached to finite certificate data. -/
noncomputable def rawFlagVector
    (labelGraph : A → SimpleGraph (Fin k))
    [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (W : Graphon Ω μ) (x : Fin k → Ω)
    (bits : Finset (Sym2 (Fin k))) (a : A) : ℝ :=
  rootedFlagValue W x bits (labelGraph a) (neighbors a)

/-- A finite linear slice of the raw flag vector. -/
noncomputable def flagLinearCombination
    (T : A → I → ℝ) (v : A → ℝ) (i : I) : ℝ :=
  ∑ a, T a i * v a

/-- Polynomial extension of a flag slice by monomials `1,s,...`. -/
noncomputable def monomialFlagExtension {order : ℕ}
    (s : ℝ) (v : I → ℝ) (ui : Fin order × I) : ℝ :=
  s ^ ui.1.1 * v ui.2

lemma bernoulli_rawFlagVector_product
    (labelGraph : A → SimpleGraph (Fin k))
    [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (W : Graphon Ω μ) (x : Fin k → Ω) (a b : A) :
    (∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
      bernoulliWeight (fun e => edgeValue W x e) bits *
        rawFlagVector labelGraph neighbors W x bits a *
        rawFlagVector labelGraph neighbors W x bits b) =
      gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
        (neighbors a) (neighbors b) := by
  simpa only [rawFlagVector] using
    bernoulli_rootedFlag_product W x (labelGraph a) (labelGraph b)
      (neighbors a) (neighbors b)

/-- Bernoulli average of two linear flag slices, expanded into raw glued
flag kernels. -/
lemma bernoulli_flagLinearCombination_product
    (labelGraph : A → SimpleGraph (Fin k))
    [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (T : A → I → ℝ) (W : Graphon Ω μ) (x : Fin k → Ω) (i j : I) :
    (∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
      bernoulliWeight (fun e => edgeValue W x e) bits *
        flagLinearCombination T
          (rawFlagVector labelGraph neighbors W x bits) i *
        flagLinearCombination T
          (rawFlagVector labelGraph neighbors W x bits) j) =
      ∑ a, ∑ b, T a i * T b j *
        gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
          (neighbors a) (neighbors b) := by
  unfold flagLinearCombination
  calc
    (∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
      bernoulliWeight (fun e => edgeValue W x e) bits *
        (∑ a, T a i * rawFlagVector labelGraph neighbors W x bits a) *
        (∑ b, T b j * rawFlagVector labelGraph neighbors W x bits b)) =
        ∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
          ∑ b, ∑ a,
            bernoulliWeight (fun e => edgeValue W x e) bits *
              (T a i * rawFlagVector labelGraph neighbors W x bits a) *
              (T b j * rawFlagVector labelGraph neighbors W x bits b) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ a, ∑ b,
          ∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
            bernoulliWeight (fun e => edgeValue W x e) bits *
              (T a i * rawFlagVector labelGraph neighbors W x bits a) *
              (T b j * rawFlagVector labelGraph neighbors W x bits b) :=
      sum_comm_three (fun bits b a =>
        bernoulliWeight (fun e => edgeValue W x e) bits *
          (T a i * rawFlagVector labelGraph neighbors W x bits a) *
          (T b j * rawFlagVector labelGraph neighbors W x bits b))
    _ = ∑ a, ∑ b, T a i * T b j *
          (∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
            bernoulliWeight (fun e => edgeValue W x e) bits *
              rawFlagVector labelGraph neighbors W x bits a *
              rawFlagVector labelGraph neighbors W x bits b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro bits _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [bernoulli_rawFlagVector_product labelGraph neighbors W x a b]

/-- The same expansion after adding polynomial monomial coordinates. -/
lemma bernoulli_monomialFlagExtension_product {order : ℕ}
    (labelGraph : A → SimpleGraph (Fin k))
    [∀ a, DecidableRel (labelGraph a).Adj]
    (neighbors : A → Finset (Fin k))
    (T : A → I → ℝ) (W : Graphon Ω μ) (x : Fin k → Ω) (s : ℝ)
    (ui vj : Fin order × I) :
    (∑ bits ∈ (univ : Finset (Sym2 (Fin k))).powerset,
      bernoulliWeight (fun e => edgeValue W x e) bits *
        monomialFlagExtension s
          (flagLinearCombination T
            (rawFlagVector labelGraph neighbors W x bits)) ui *
        monomialFlagExtension s
          (flagLinearCombination T
            (rawFlagVector labelGraph neighbors W x bits)) vj) =
      s ^ (ui.1.1 + vj.1.1) *
        ∑ a, ∑ b, T a ui.2 * T b vj.2 *
          gluedRootedFlagKernel W x (labelGraph a) (labelGraph b)
            (neighbors a) (neighbors b) := by
  simp only [monomialFlagExtension, pow_add]
  rw [← bernoulli_flagLinearCombination_product
    labelGraph neighbors T W x ui.2 vj.2]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bits _
  ring

end Taeyoung.Methods.RootedSOS
