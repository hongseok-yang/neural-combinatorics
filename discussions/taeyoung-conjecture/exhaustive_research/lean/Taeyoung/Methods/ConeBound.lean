import Taeyoung.Methods.CliqueLeaf.Density

/-!
# The conditional cone lemma

`clique_common_leaf_extensions` proved its density bound by a chain that never
used anything about the clique polynomial beyond four facts: it vanishes at the
threshold, it has a nonnegative slope, its tangent line at `c` lies under it on
`[a,1]`, and it bounds the base density above the threshold.  This file states
that chain once, with the polynomial and the base graph abstract.

`six_verified_base_cones` calls exactly this "a conditional cone lemma"; it is
also what `paw_triangle_edge_cones` and the `K₁ ∨ C₅` row need.  The base is
indexed as `Fin (h + 2)`, so that `weighted_rootedTriangle h` supplies the
correction term with no arithmetic on the exponent.

Two lemmas first proved for the clique common-leaf family are reused verbatim:
`rootedTriangle_le_degree` (which makes the degenerate set harmless) and
`rootedDensity_top_two` (which identifies `d²·z_x` with `τ(x)`).
-/

open MeasureTheory

namespace Taeyoung.Methods

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.CliqueLeaf

-- `Ω` is fixed at universe `0`: that is the universe the shared
-- `SatisfiesLowerBound` socket quantifies over, and Lean has no
-- universe-polymorphic hypotheses, so the base-bound hypothesis below
-- must live in the same universe as the link it is applied to.
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The pointwise cone bound.**  Valid at every root, including where the
degree vanishes. -/
theorem rootedDensity_ge_tangent {h : ℕ} (B : SimpleGraph (Fin (h + 2)))
    [DecidableRel B.Adj] (W : Graphon Ω μ) {φ : ℝ → ℝ} {a c lam : ℝ}
    (hφa : φ a = 0) (hlam : 0 ≤ lam)
    (htangent : ∀ w, a ≤ w → w ≤ 1 → φ c + lam * (w - c) ≤ φ w)
    (ha1 : a ≤ 1)
    (hbase : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      a ≤ cliqueDensity 2 V → φ (cliqueDensity 2 V) ≤ homDensity B V)
    (_hφc : 0 ≤ φ c) (x : Ω) :
    degree W x ^ (h + 2) * φ c +
        lam * (degree W x ^ h * rootedTriangle W x -
          c * degree W x ^ (h + 2)) ≤ rootedDensity B W x := by
  rcases eq_or_lt_of_le (degree_nonneg W x) with hd0 | hdpos
  · have hz : degree W x = 0 := hd0.symm
    have hτ : rootedTriangle W x = 0 :=
      le_antisymm (by rw [← hz]; exact rootedTriangle_le_degree W x)
        (rootedTriangle_nonneg W x)
    rw [hz, hτ, zero_pow (by omega : h + 2 ≠ 0)]
    simpa using rootedDensity_nonneg B W x
  · haveI := isProbabilityMeasure_linkMeasure W hdpos
    have htan : φ c + lam * (cliqueDensity 2 (linkGraphon W x) - c) ≤
        homDensity B (linkGraphon W x) :=
      tangent_of_convex (φ := φ) (a := a) (c := c) (s := lam)
        (z := cliqueDensity 2 (linkGraphon W x))
        (t := homDensity B (linkGraphon W x))
        hφa hlam htangent ha1 (cliqueDensity_le_one 2 (linkGraphon W x))
        (homDensity_nonneg B (linkGraphon W x))
        fun hle ↦ hbase (linkGraphon W x) hle
    have hsplit : degree W x ^ (h + 2) = degree W x ^ h * degree W x ^ 2 := by
      rw [← pow_add]
    have hτeq : degree W x ^ 2 * cliqueDensity 2 (linkGraphon W x) =
        rootedTriangle W x := by
      rw [← rootedDensity_top_two W x, cliqueDensity,
        rootedDensity_eq (⊤ : SimpleGraph (Fin 2)) W hdpos]
    have hcone : rootedDensity B W x =
        degree W x ^ (h + 2) * homDensity B (linkGraphon W x) :=
      rootedDensity_eq B W hdpos
    have hpow : (0 : ℝ) ≤ degree W x ^ (h + 2) := pow_nonneg (degree_nonneg W x) _
    have hmul := mul_le_mul_of_nonneg_left htan hpow
    have hz : degree W x ^ (h + 2) * cliqueDensity 2 (linkGraphon W x) =
        degree W x ^ h * rootedTriangle W x := by
      rw [hsplit, mul_assoc, hτeq]
    rw [hcone]
    nlinarith [hmul, hz]

/-- **The conditional cone lemma.**  A base bound above a threshold, plus the
weighted rooted-triangle correction, gives the cone bound `M_N · φ(c)`. -/
theorem coneGraph_bound {h : ℕ} (B : SimpleGraph (Fin (h + 2)))
    [DecidableRel B.Adj] (W : Graphon Ω μ) {φ : ℝ → ℝ} {a c lam : ℝ}
    (hφa : φ a = 0) (hlam : 0 ≤ lam)
    (htangent : ∀ w, a ≤ w → w ≤ 1 → φ c + lam * (w - c) ≤ φ w)
    (ha1 : a ≤ 1)
    (hbase : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      a ≤ cliqueDensity 2 V → φ (cliqueDensity 2 V) ≤ homDensity B V)
    (hφc : 0 ≤ φ c)
    (hcorr : c * moment W (h + 2) ≤
      ∫ x, degree W x ^ h * rootedTriangle W x ∂μ) :
    moment W (h + 2) * φ c ≤ homDensity (coneGraph B) W := by
  have hdint : Integrable (fun x ↦ degree W x ^ (h + 2)) μ :=
    integrable_of_bdd ((measurable_degree W).pow_const _) fun x ↦ by
      rw [abs_of_nonneg (pow_nonneg (degree_nonneg W x) _)]
      exact pow_le_one₀ (degree_nonneg W x) (degree_le_one W x)
  have htint : Integrable (fun x ↦ degree W x ^ h * rootedTriangle W x) μ :=
    integrable_of_bdd (((measurable_degree W).pow_const _).mul
      (measurable_rootedTriangle W)) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (degree_nonneg W x) _)
          (rootedTriangle_nonneg W x))]
        exact mul_le_one₀ (pow_le_one₀ (degree_nonneg W x) (degree_le_one W x))
          (rootedTriangle_nonneg W x) (rootedTriangle_le_one W x)
  have hg : Integrable (fun x ↦ (φ c - lam * c) * degree W x ^ (h + 2) +
      lam * (degree W x ^ h * rootedTriangle W x)) μ :=
    (hdint.const_mul _).add (htint.const_mul _)
  have hmono : ∫ x, ((φ c - lam * c) * degree W x ^ (h + 2) +
      lam * (degree W x ^ h * rootedTriangle W x)) ∂μ ≤
      ∫ x, rootedDensity B W x ∂μ := by
    refine integral_mono hg (integrable_rootedDensity B W) fun x ↦ ?_
    have hb := rootedDensity_ge_tangent B W hφa hlam htangent ha1 hbase hφc x
    have heq : (φ c - lam * c) * degree W x ^ (h + 2) +
        lam * (degree W x ^ h * rootedTriangle W x) =
          degree W x ^ (h + 2) * φ c +
          lam * (degree W x ^ h * rootedTriangle W x -
            c * degree W x ^ (h + 2)) := by ring
    rw [heq]
    exact hb
  rw [homDensity_coneGraph]
  refine le_trans ?_ hmono
  rw [integral_add (hdint.const_mul _) (htint.const_mul _), integral_const_mul,
    integral_const_mul, ← moment]
  have hstep := mul_le_mul_of_nonneg_left hcorr hlam
  linarith

end Taeyoung.Methods
