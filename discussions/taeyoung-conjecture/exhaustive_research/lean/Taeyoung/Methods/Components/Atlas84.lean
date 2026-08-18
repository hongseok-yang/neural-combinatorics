import Taeyoung.Methods.Link.Cone
import Taeyoung.Methods.PureChordal.CliquePolynomialBound
import Taeyoung.Methods.RootedTriangleTree.Paw
import Taeyoung.Foundation.DisjointUnion
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Multiplicativity over components: Atlas 84 = `K₃ ⊔ P₃`

Atlas 84 is a triangle and a two-edge path, disjointly.  Nothing beyond
`Foundation/DisjointUnion.lean` is needed: the density and the chromatic
polynomial both factor, the triangle factor is the pure-chordal clique bound,
and the path factor is `t(P₃,W) = ∫d² ≥ p²`, which is Jensen.

The path is presented as the star `K_{1,n}` — the cone over `n` isolated
vertices — so that `Methods/Link/Cone.lean` supplies its density for free:
the rooted density of the empty graph is `d(x)ⁿ`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.Components

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Stars -/

/-- The star `K_{1,n}`: the cone over `n` isolated vertices. -/
abbrev starTree (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  coneGraph (⊥ : SimpleGraph (Fin n))

omit [IsProbabilityMeasure μ] in
lemma graphWeight_bot (W : Graphon Ω μ) (n : ℕ) (y : Fin n → Ω) :
    graphWeight (⊥ : SimpleGraph (Fin n)) W y = 1 := by
  rw [graphWeight]
  refine Finset.prod_eq_one fun e he ↦ ?_
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot,
    Set.mem_empty_iff_false] at he

lemma rootedDensity_bot (W : Graphon Ω μ) (n : ℕ) (a : Ω) :
    rootedDensity (⊥ : SimpleGraph (Fin n)) W a = degree W a ^ n := by
  rw [rootedDensity]
  simp only [graphWeight_bot, mul_one]
  rw [assignmentMeasure]
  simpa [degree] using integral_fintype_prod_eq_pow (ι := Fin n) (μ := μ) fun y ↦ W a y

/-- **The star's density is a degree moment.** -/
theorem homDensity_starTree (W : Graphon Ω μ) (n : ℕ) :
    homDensity (starTree n) W = moment W n := by
  rw [homDensity_coneGraph (⊥ : SimpleGraph (Fin n)) W]
  simp only [rootedDensity_bot]
  rfl

/-! ### Chromatic data for the two components -/

lemma singleton_isClique₁ :
    (⊤ : SimpleGraph (Fin 1)).IsClique ((({0} : Finset (Fin 1))) : Set (Fin 1)) := by
  intro u hu w hw huw
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hw
  exact absurd (hu.trans hw.symm) huw

/-- The two-edge path, built as `K₁` with two leaves. -/
abbrev pathTower : SimpleGraph (Option (Option (Fin 1))) :=
  attachVertex (attachVertex (⊤ : SimpleGraph (Fin 1)) {0}) {some 0}

lemma singleton_isClique_attach :
    (attachVertex (⊤ : SimpleGraph (Fin 1)) {0}).IsClique
      ((({some 0} : Finset (Option (Fin 1)))) : Set (Option (Fin 1))) := by
  intro u hu w hw huw
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hw
  exact absurd (hu.trans hw.symm) huw

def pathEquiv : Option (Option (Fin 1)) ≃ Fin 3 where
  toFun a := match a with
    | none => 2
    | some none => 1
    | some (some i) => ![0] i
  invFun j := ![some (some 0), some none, none] j
  left_inv := by decide
  right_inv := by decide

def pathIso : pathTower ≃g starTree 2 where
  toEquiv := pathEquiv
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem path_chrom : IsChromaticPolynomial (starTree 2) ((X : ℝ[X]) * (X - C 1) ^ 2) := by
  have h := isChromaticPolynomial_of_attachIso pathIso singleton_isClique_attach
    (isChromaticPolynomial_attachVertex singleton_isClique₁
      (isChromaticPolynomial_top 1))
  simp only [Finset.card_singleton, Nat.cast_one] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ 2 =
      (X - C 1) * ((X - C 1) * ∏ i ∈ range 1, (X - C (i : ℝ))) := by
    rw [Finset.prod_range_one]
    simp
    ring
  rw [hpoly]
  exact h

theorem path_count (k : ℕ) :
    properAssignmentCount (starTree 2) k = (k - 1) * ((k - 1) * k.descFactorial 1) := by
  rw [properAssignmentCount_of_attachIso pathIso singleton_isClique_attach k,
    properAssignmentCount_attachVertex singleton_isClique₁, properAssignmentCount_top]
  simp

theorem path_num : IsChromaticNumber (starTree 2) 2 where
  positive := by rw [path_count]; decide
  zero_below k hk := by
    interval_cases k <;> simp [path_count]

/-! ### Atlas 84 -/

theorem isChromaticNumber_top₃ : IsChromaticNumber (⊤ : SimpleGraph (Fin 3)) 3 where
  positive := by rw [properAssignmentCount_top]; decide
  zero_below k hk := by
    rw [properAssignmentCount_top]
    simpa using Nat.descFactorial_eq_zero_iff_lt.mpr hk

/-- Atlas 84 on its certificate labelling: a triangle and a two-edge path. -/
abbrev atlas84 : SimpleGraph (Fin (3 + 3)) :=
  disjointUnion (⊤ : SimpleGraph (Fin 3)) (starTree 2)

lemma chromaticTarget_top₃ {p : ℝ} (hp : p ≠ 1) :
    chromaticTarget (V := Fin 3) (∏ i ∈ range 3, (X - C (i : ℝ))) p = cliquePoly 3 p := by
  have hq : (1 : ℝ) - p ≠ 0 := fun h ↦ hp (by linarith)
  rw [chromaticTarget_of_ne_one _ hp]
  simp only [Fintype.card_fin, eval_prod, eval_sub, eval_X, eval_C]
  have e1 : ∀ i ∈ range 3,
      (1 / (1 - p) - (i : ℝ)) = (1 - (i : ℝ) * (1 - p)) / (1 - p) := by
    intro i _
    field_simp
  rw [Finset.prod_congr rfl e1, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_range, ← cliquePoly]
  field_simp

lemma chromaticTarget_path {p : ℝ} (hp : p ≠ 1) :
    chromaticTarget (V := Fin 3) ((X : ℝ[X]) * (X - C 1) ^ 2) p = p ^ 2 := by
  have hq : (1 : ℝ) - p ≠ 0 := fun h ↦ hp (by linarith)
  rw [chromaticTarget_of_ne_one _ hp]
  simp only [Fintype.card_fin, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  have e2 : (1 / (1 - p) - 1) = p / (1 - p) := by
    field_simp
    ring
  rw [e2, div_pow]
  field_simp

/-- **Atlas 84 satisfies the catalogue proposition.** -/
theorem atlas84_satisfiesLowerBound : Taeyoung.SatisfiesLowerBound atlas84 := by
  refine satisfiesLowerBound_disjointUnion (P₁ := ∏ i ∈ range 3, (X - C (i : ℝ)))
    (P₂ := (X : ℝ[X]) * (X - C 1) ^ 2) (r₁ := 3) (r₂ := 2)
    (⊤ : SimpleGraph (Fin 3)) (starTree 2)
    (isChromaticPolynomial_top 3) isChromaticNumber_top₃
    path_chrom path_num ?_ ?_
  · intro Ω _ ν _ W hadm
    have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
      have h := hadm
      norm_num [admissibleDensity, edgeDensity] at h
      linarith
    have hthr : 1 - 1 / (((3 - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W := by norm_num; linarith
    have hbound : cliquePoly 3 (cliqueDensity 2 W) ≤ cliqueDensity 3 W :=
      cliqueDensity_ge_cliquePoly W (by norm_num) hthr le_rfl
    have hnn : 0 ≤ cliquePoly 3 (cliqueDensity 2 W) :=
      cliquePoly_nonneg_of_threshold (r := 3) (by norm_num) le_rfl hthr
    by_cases hone : edgeDensity W = 1
    · rw [hone, chromaticTarget_at_one]
      refine ⟨zero_le_one, ?_⟩
      have : cliquePoly 3 (cliqueDensity 2 W) = 1 := by
        simp [cliquePoly, show cliqueDensity 2 W = 1 from hone]
      exact this ▸ hbound
    · rw [chromaticTarget_top₃ hone]
      exact ⟨hnn, hbound⟩
  · intro Ω _ ν _ W hadm
    by_cases hone : edgeDensity W = 1
    · rw [hone, chromaticTarget_at_one]
      refine ⟨zero_le_one, ?_⟩
      rw [homDensity_starTree]
      have := RootedTriangleTree.pow_le_moment W 2
      rw [show cliqueDensity 2 W = 1 from hone] at this
      simpa using this
    · rw [chromaticTarget_path hone, homDensity_starTree]
      exact ⟨sq_nonneg _, RootedTriangleTree.pow_le_moment W 2⟩

end Taeyoung.Methods.Components
