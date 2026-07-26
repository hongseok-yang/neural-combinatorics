import PureChordal.CliqueMarginals
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Algebra for finite-coordinate marginals

These lemmas package the elementary operations used in the junction-tree
density: pulling a factor independent of the integrated coordinates through a
marginal, and normalizing a density by its marginal.
-/

namespace PureChordal

open MeasureTheory
open scoped ENNReal

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A function is unchanged when the coordinates in `T` are overwritten. -/
def UpdateInvariant (T : Finset I) (f : (I → Ω) → ℝ≥0∞) : Prop :=
  ∀ x (y : T → Ω), f (Function.updateFinset x T y) = f x

/-- A function only uses coordinates belonging to `A`. -/
def FinsetDependsOn (A : Finset I) (f : (I → Ω) → ℝ≥0∞) : Prop :=
  ∀ ⦃x y⦄, (∀ i ∈ A, x i = y i) → f x = f y

lemma FinsetDependsOn.const (A : Finset I) (c : ℝ≥0∞) :
    FinsetDependsOn A (fun _ : I → Ω => c) := by
  intro x y h
  rfl

lemma FinsetDependsOn.mono {A B : Finset I} {f : (I → Ω) → ℝ≥0∞}
    (hf : FinsetDependsOn A f) (hAB : A ⊆ B) :
    FinsetDependsOn B f := by
  intro x y hxy
  exact hf fun i hi => hxy i (hAB hi)

lemma FinsetDependsOn.mul {A : Finset I} {f g : (I → Ω) → ℝ≥0∞}
    (hf : FinsetDependsOn A f) (hg : FinsetDependsOn A g) :
    FinsetDependsOn A (fun x => f x * g x) := by
  intro x y hxy
  change f x * g x = f y * g y
  rw [hf hxy, hg hxy]

lemma FinsetDependsOn.inv {A : Finset I} {f : (I → Ω) → ℝ≥0∞}
    (hf : FinsetDependsOn A f) :
    FinsetDependsOn A (fun x => (f x)⁻¹) := by
  intro x y hxy
  change (f x)⁻¹ = (f y)⁻¹
  rw [hf hxy]

lemma FinsetDependsOn.updateInvariant_of_disjoint
    {A T : Finset I} {f : (I → Ω) → ℝ≥0∞}
    (hf : FinsetDependsOn A f) (hTA : Disjoint T A) :
    UpdateInvariant T f := by
  intro x y
  apply hf
  intro i hiA
  have hiT : i ∉ T := fun hiT =>
    Finset.disjoint_left.mp hTA hiT hiA
  simp [Function.updateFinset, hiT]

lemma FinsetDependsOn.lmarginal
    {A T : Finset I} {f : (I → Ω) → ℝ≥0∞}
    (hf : FinsetDependsOn A f) :
    FinsetDependsOn (A \ T)
      (lmarginal (fun _ : I => μ) T f) := by
  intro x y hxy
  unfold MeasureTheory.lmarginal
  apply lintegral_congr
  intro z
  apply hf
  intro i hiA
  by_cases hiT : i ∈ T
  · simp [Function.updateFinset, hiT]
  · simp only [Function.updateFinset, hiT, dite_false]
    exact hxy i (Finset.mem_sdiff.mpr ⟨hiA, hiT⟩)

lemma FinsetDependsOn.lmarginal_eq_self_of_disjoint
    {A T : Finset I} {f : (I → Ω) → ℝ≥0∞}
    (hf : FinsetDependsOn A f) (hTA : Disjoint T A) :
    MeasureTheory.lmarginal (fun _ : I => μ) T f = f := by
  funext x
  unfold MeasureTheory.lmarginal
  have hinv := hf.updateInvariant_of_disjoint hTA
  simp_rw [hinv x]
  simp

/-- Marginalizing from an ambient set down to a subset can be done in two
stages: first integrate outside the ambient set, then inside it but outside the
subset. -/
lemma lmarginal_compl_subset
    {S A : Finset I} (hSA : S ⊆ A) {f : (I → Ω) → ℝ≥0∞}
    (hf : Measurable f) :
    MeasureTheory.lmarginal (fun _ : I => μ) (Finset.univ \ S) f =
      MeasureTheory.lmarginal (fun _ : I => μ) (A \ S)
        (MeasureTheory.lmarginal (fun _ : I => μ)
          (Finset.univ \ A) f) := by
  have hunion :
      Finset.univ \ S = (A \ S) ∪ (Finset.univ \ A) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hiS
      by_cases hiA : i ∈ A
      · exact Or.inl ⟨hiA, hiS⟩
      · exact Or.inr hiA
    · rintro (hi | hi)
      · exact hi.2
      · exact fun hiS => hi (hSA hiS)
  have hdisj : Disjoint (A \ S) (Finset.univ \ A) := by
    exact (Finset.disjoint_sdiff (s := A) (t := Finset.univ)).mono
      Finset.sdiff_subset (by rfl)
  rw [hunion, lmarginal_union (fun _ : I => μ) f hf hdisj]

/-- If a function is supported on `P` and `P ∩ B = S`, integrating outside
`B` is the same as integrating outside `S`. -/
lemma FinsetDependsOn.lmarginal_compl_eq_of_inter
    {P B S : Finset I} {f : (I → Ω) → ℝ≥0∞}
    (hfdep : FinsetDependsOn P f) (hfmeas : Measurable f)
    (hSB : S ⊆ B) (hinter : P ∩ B = S) :
    MeasureTheory.lmarginal (fun _ : I => μ) (Finset.univ \ B) f =
      MeasureTheory.lmarginal (fun _ : I => μ) (Finset.univ \ S) f := by
  have hunion :
      Finset.univ \ S = (Finset.univ \ B) ∪ (B \ S) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hiS
      by_cases hiB : i ∈ B
      · exact Or.inr ⟨hiB, hiS⟩
      · exact Or.inl hiB
    · rintro (hi | hi)
      · exact fun hiS => hi (hSB hiS)
      · exact hi.2
  have hdisjUnion : Disjoint (Finset.univ \ B) (B \ S) := by
    exact (Finset.disjoint_sdiff (s := B) (t := Finset.univ)).symm.mono
      (by rfl) Finset.sdiff_subset
  have hdisjSupport : Disjoint (B \ S) P := by
    rw [Finset.disjoint_left]
    intro i hiBS hiP
    have hiBS' := Finset.mem_sdiff.mp hiBS
    have hiS : i ∈ S := by
      rw [← hinter]
      exact Finset.mem_inter.mpr ⟨hiP, hiBS'.1⟩
    exact hiBS'.2 hiS
  rw [hunion, lmarginal_union (fun _ : I => μ) f hfmeas hdisjUnion,
    FinsetDependsOn.lmarginal_eq_self_of_disjoint
      (μ := μ) hfdep hdisjSupport]

lemma updateInvariant_lmarginal
    (T : Finset I) (f : (I → Ω) → ℝ≥0∞) :
    UpdateInvariant T (lmarginal (fun _ : I => μ) T f) := by
  intro x y
  apply lmarginal_congr
  intro i hi
  simp [Function.updateFinset, hi]

lemma lmarginal_mul_of_left_updateInvariant
    (T : Finset I) {f g : (I → Ω) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfinv : UpdateInvariant T f) :
    lmarginal (fun _ : I => μ) T (fun x => f x * g x) =
      fun x => f x * lmarginal (fun _ : I => μ) T g x := by
  funext x
  unfold lmarginal
  simp_rw [hfinv x]
  exact MeasureTheory.lintegral_const_mul
    (μ := Measure.pi fun _ : T => μ) (f x)
    (hg.comp measurable_updateFinset)

lemma lmarginal_mul_of_right_updateInvariant
    (T : Finset I) {f g : (I → Ω) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hginv : UpdateInvariant T g) :
    lmarginal (fun _ : I => μ) T (fun x => f x * g x) =
      fun x => lmarginal (fun _ : I => μ) T f x * g x := by
  calc
    lmarginal (fun _ : I => μ) T (fun x => f x * g x) =
        lmarginal (fun _ : I => μ) T (fun x => g x * f x) := by
      congr 2
      funext x
      exact mul_comm _ _
    _ = (fun x => g x * lmarginal (fun _ : I => μ) T f x) :=
      lmarginal_mul_of_left_updateInvariant T hg hf hginv
    _ = (fun x => lmarginal (fun _ : I => μ) T f x * g x) := by
      funext x
      exact mul_comm _ _

/-- Divide a nonnegative density by its own marginal.  Integrating the
result over the divided-out coordinates gives one pointwise. -/
theorem lmarginal_inv_marginal_mul_eq_one
    (T : Finset I) {f : (I → Ω) → ℝ≥0∞}
    (hf : Measurable f)
    (hq0 : ∀ x, lmarginal (fun _ : I => μ) T f x ≠ 0)
    (hqtop : ∀ x, lmarginal (fun _ : I => μ) T f x ≠ ∞) :
    lmarginal (fun _ : I => μ) T
        (fun x => (lmarginal (fun _ : I => μ) T f x)⁻¹ * f x) =
      fun _ => 1 := by
  funext x
  have hqinv := updateInvariant_lmarginal
    (μ := μ) T f
  change (∫⁻ y : T → Ω,
      (lmarginal (fun _ : I => μ) T f
          (Function.updateFinset x T y))⁻¹ *
        f (Function.updateFinset x T y)
      ∂Measure.pi fun _ : T => μ) = 1
  simp_rw [hqinv x]
  calc
    (∫⁻ y : T → Ω,
        (lmarginal (fun _ : I => μ) T f x)⁻¹ *
          f (Function.updateFinset x T y)
        ∂Measure.pi fun _ : T => μ) =
        (lmarginal (fun _ : I => μ) T f x)⁻¹ *
          (∫⁻ y : T → Ω, f (Function.updateFinset x T y)
            ∂Measure.pi fun _ : T => μ) :=
      MeasureTheory.lintegral_const_mul
        (μ := Measure.pi fun _ : T => μ)
        (lmarginal (fun _ : I => μ) T f x)⁻¹
        (hf.comp measurable_updateFinset)
    _ = (lmarginal (fun _ : I => μ) T f x)⁻¹ *
          lmarginal (fun _ : I => μ) T f x := rfl
    _ = 1 := ENNReal.inv_mul_cancel (hq0 x) (hqtop x)

/-- Extending a density by a conditionally normalized factor on fresh
coordinates preserves every marginal supported on the old coordinates. -/
theorem lmarginal_mul_preserve_of_fresh
    {P A N : Finset I} {f k : (I → Ω) → ℝ≥0∞}
    (hfmeas : Measurable f) (hkmeas : Measurable k)
    (hfdep : FinsetDependsOn P f) (hAP : A ⊆ P)
    (hNP : Disjoint N P)
    (hkone : lmarginal (fun _ : I => μ) N k = fun _ => 1) :
    lmarginal (fun _ : I => μ) (Finset.univ \ A)
        (fun x => f x * k x) =
      lmarginal (fun _ : I => μ) (Finset.univ \ A) f := by
  have hNA : Disjoint N A := hNP.mono (by rfl) hAP
  have hNcomp : N ⊆ Finset.univ \ A := by
    intro i hiN
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hiA => Finset.disjoint_left.mp hNA hiN hiA⟩
  let R := (Finset.univ \ A) \ N
  have hunion : Finset.univ \ A = R ∪ N := by
    ext i
    simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hiA
      by_cases hiN : i ∈ N
      · exact Or.inr hiN
      · exact Or.inl ⟨hiA, hiN⟩
    · rintro (hi | hi)
      · exact hi.1
      · exact (Finset.mem_sdiff.mp (hNcomp hi)).2
  have hRN : Disjoint R N := by
    dsimp [R]
    exact (Finset.disjoint_sdiff (s := N)
      (t := Finset.univ \ A)).symm
  have hfinv : UpdateInvariant N f :=
    hfdep.updateInvariant_of_disjoint hNP
  have hmargProd :
      lmarginal (fun _ : I => μ) N (fun x => f x * k x) = f := by
    rw [lmarginal_mul_of_left_updateInvariant N hfmeas hkmeas hfinv,
      hkone]
    funext x
    simp
  have hmargF :
      lmarginal (fun _ : I => μ) N f = f :=
    hfdep.lmarginal_eq_self_of_disjoint hNP
  rw [hunion,
    lmarginal_union (fun _ : I => μ) (fun x => f x * k x)
      (hfmeas.mul hkmeas) hRN,
    hmargProd,
    lmarginal_union (fun _ : I => μ) f hfmeas hRN,
    hmargF]

/-- Equal marginals give equal expectations against every nonnegative
measurable test function supported on the retained coordinates. -/
theorem lintegral_mul_eq_of_lmarginal_eq
    {A : Finset I} {f g k : (I → Ω) → ℝ≥0∞}
    (x₀ : I → Ω)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hkmeas : Measurable k) (hkdep : FinsetDependsOn A k)
    (hmarg :
      lmarginal (fun _ : I => μ) (Finset.univ \ A) f =
        lmarginal (fun _ : I => μ) (Finset.univ \ A) g) :
    ∫⁻ x, f x * k x ∂Measure.pi (fun _ : I => μ) =
      ∫⁻ x, g x * k x ∂Measure.pi (fun _ : I => μ) := by
  let T := Finset.univ \ A
  have hAT : Disjoint A T := by
    dsimp [T]
    exact Finset.disjoint_sdiff
  have hATuniv : A ∪ T = Finset.univ := by
    ext i
    simp [T]
  have hkinv : UpdateInvariant T k :=
    hkdep.updateInvariant_of_disjoint hAT.symm
  have hfull :
      lmarginal (fun _ : I => μ) Finset.univ
          (fun x => f x * k x) =
        lmarginal (fun _ : I => μ) Finset.univ
          (fun x => g x * k x) := by
    rw [← hATuniv,
      lmarginal_union (fun _ : I => μ) (fun x => f x * k x)
        (hfmeas.mul hkmeas) hAT,
      lmarginal_union (fun _ : I => μ) (fun x => g x * k x)
        (hgmeas.mul hkmeas) hAT,
      lmarginal_mul_of_right_updateInvariant T hfmeas hkmeas hkinv,
      lmarginal_mul_of_right_updateInvariant T hgmeas hkmeas hkinv,
      hmarg]
  have hconstants :
      (fun _ : I → Ω =>
        ∫⁻ x, f x * k x ∂Measure.pi (fun _ : I => μ)) =
      (fun _ : I → Ω =>
        ∫⁻ x, g x * k x ∂Measure.pi (fun _ : I => μ)) := by
    simpa only [lmarginal_univ] using hfull
  exact congrFun hconstants x₀

end PureChordal
