import Taeyoung.Methods.ConeBound

/-!
# Cones over the paw and over the triangle–edge product: the shared half

`notes/paw_triangle_edge_cones.tex` treats two base families,

```
B_s^P = P ⊔ K̄ₛ        B_s^R = (K₃ ⊔ K₂) ⊔ K̄ₛ
```

through one observation: both have the *same* target

```
φ(z) = z²(2z - 1),
```

and both are already known to dominate it above `z = 1/2`.  Everything after
that is independent of which base is used, so it is proved here once, against
an abstract base graph `B` supplying only that bound.

`φ` is a cubic, so the tangent inequality the conditional cone lemma wants is
the identity

```
φ(w) - φ(c) - φ'(c)(w - c) = (w - c)²·(2w + 4c - 1),
```

whose right-hand side is nonnegative as soon as `w, c ≥ 1/2`.  No convexity
theory is needed: `nlinarith` verifies the identity's consequence directly.

The cone is taken at the tangent point `c = 2 - 1/p`, which is where
`weighted_rootedTriangle` makes the correction term of `coneGraph_bound`
vanish; the resulting bound is `p^m(2p-1)²(3p-2)` for a base on `m + 3`
vertices, which is exactly the catalogue target of `K₁ ∨ B`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.PawCone

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link

-- As in `Methods/ConeBound.lean`, `Ω` is fixed at universe `0`: the base bound
-- is a hypothesis quantified over graphons, and Lean has no
-- universe-polymorphic hypotheses.
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The common base target -/

/-- The target shared by `P ⊔ K̄ₛ` and `(K₃ ⊔ K₂) ⊔ K̄ₛ`. -/
def baseTarget (z : ℝ) : ℝ := z ^ 2 * (2 * z - 1)

/-- Its derivative, `φ'(z) = 2z(3z - 1)`. -/
def baseTargetDeriv (z : ℝ) : ℝ := 2 * z * (3 * z - 1)

@[simp] lemma baseTarget_one : baseTarget 1 = 1 := by norm_num [baseTarget]

lemma baseTarget_half : baseTarget (1 / 2) = 0 := by norm_num [baseTarget]

lemma baseTargetDeriv_nonneg {c : ℝ} (hc : 1 / 2 ≤ c) : 0 ≤ baseTargetDeriv c := by
  rw [baseTargetDeriv]; nlinarith

lemma baseTarget_nonneg {c : ℝ} (hc : 1 / 2 ≤ c) : 0 ≤ baseTarget c := by
  rw [baseTarget]; nlinarith [sq_nonneg c]

/-- **The affine minorant of `φ`.**  The cubic remainder factors as
`(w - c)²(2w + 4c - 1)`, and the second factor is positive on `[1/2, ∞)`. -/
lemma baseTarget_tangent {c : ℝ} (hc : 1 / 2 ≤ c) (w : ℝ) (hw : 1 / 2 ≤ w)
    (_hw1 : w ≤ 1) :
    baseTarget c + baseTargetDeriv c * (w - c) ≤ baseTarget w := by
  rw [baseTarget, baseTarget, baseTargetDeriv]
  nlinarith [mul_nonneg (sq_nonneg (w - c))
    (show (0 : ℝ) ≤ 2 * w + 4 * c - 1 by linarith)]

/-! ### The cone bound -/

/-- **The density bound for `K₁ ∨ B`.**  A base on `m + 3` vertices dominating
`φ` above `1/2` yields the cone bound `p^m(2p-1)²(3p-2)` on `p ≥ 2/3`. -/
theorem coneGraph_baseTarget_bound {m : ℕ} (B : SimpleGraph (Fin (m + 1 + 2)))
    [DecidableRel B.Adj]
    (hbase : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      1 / 2 ≤ cliqueDensity 2 V → baseTarget (cliqueDensity 2 V) ≤ homDensity B V)
    (W : Graphon Ω μ) (hp : 2 / 3 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ m * (2 * cliqueDensity 2 W - 1) ^ 2 *
        (3 * cliqueDensity 2 W - 2) ≤ homDensity (coneGraph B) W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  have hpne : p ≠ 0 := ne_of_gt hppos
  have hinv : 1 / p ≤ 3 / 2 := by rw [div_le_iff₀ hppos]; linarith
  have hc : (1 : ℝ) / 2 ≤ 2 - 1 / p := by linarith
  -- the correction term of the conditional cone lemma vanishes at `c = 2 - 1/p`
  have hcorr : (2 - 1 / p) * moment W (m + 1 + 2) ≤
      ∫ x, degree W x ^ (m + 1) * rootedTriangle W x ∂μ := by
    have hwrt := weighted_rootedTriangle (W := W) (m + 1)
    rw [← hpdef] at hwrt
    rw [show (2 : ℝ) - 1 / p = (2 * p - 1) / p by field_simp,
      div_mul_eq_mul_div, div_le_iff₀ hppos]
    nlinarith [hwrt]
  have hmain := coneGraph_bound (h := m + 1) B W (φ := baseTarget) (a := 1 / 2)
    (c := 2 - 1 / p) (lam := baseTargetDeriv (2 - 1 / p)) baseTarget_half
    (baseTargetDeriv_nonneg hc) (baseTarget_tangent hc) (by norm_num) hbase
    (baseTarget_nonneg hc) hcorr
  have hmom : p ^ (m + 1 + 2) ≤ moment W (m + 1 + 2) := by
    have := RootedTriangleTree.pow_le_moment W (m + 1 + 2)
    rwa [← hpdef] at this
  have hφ : 0 ≤ baseTarget (2 - 1 / p) := baseTarget_nonneg hc
  have hid : p ^ (m + 1 + 2) * baseTarget (2 - 1 / p) =
      p ^ m * (2 * p - 1) ^ 2 * (3 * p - 2) := by
    rw [baseTarget, show m + 1 + 2 = m + 3 from rfl, pow_add]
    field_simp
    ring
  calc p ^ m * (2 * p - 1) ^ 2 * (3 * p - 2)
      = p ^ (m + 1 + 2) * baseTarget (2 - 1 / p) := hid.symm
    _ ≤ moment W (m + 1 + 2) * baseTarget (2 - 1 / p) :=
        mul_le_mul_of_nonneg_right hmom hφ
    _ ≤ homDensity (coneGraph B) W := hmain

/-! ### The catalogue target -/

/-- **The catalogue target of `K₁ ∨ B`.**  Both base families give the cone the
chromatic polynomial `x(x-1)^m(x-2)²(x-3)`. -/
lemma chromaticTarget_pawCone (m : ℕ) {p : ℝ} (hp : p ≠ 1) :
    chromaticTarget (V := Fin (m + 1 + 2 + 1))
        ((X : ℝ[X]) * (X - C 1) ^ m * (X - C 2) ^ 2 * (X - C 3)) p =
      p ^ m * (2 * p - 1) ^ 2 * (3 * p - 2) := by
  have hq : (1 : ℝ) - p ≠ 0 := fun h ↦ hp (by linarith)
  rw [chromaticTarget_of_ne_one _ hp]
  simp only [Fintype.card_fin, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  have e1 : 1 / (1 - p) - 1 = p / (1 - p) := by field_simp; ring
  have e2 : 1 / (1 - p) - 2 = (2 * p - 1) / (1 - p) := by field_simp; ring
  have e3 : 1 / (1 - p) - 3 = (3 * p - 2) / (1 - p) := by field_simp; ring
  rw [e1, e2, e3, div_pow, div_pow, show m + 1 + 2 + 1 = m + 4 from rfl, pow_add]
  field_simp

/-- **The paw / triangle–edge cone family, packaged for an Atlas module.** -/
theorem satisfiesLowerBound_of_pawCone {m : ℕ} (B : SimpleGraph (Fin (m + 1 + 2)))
    [DecidableRel B.Adj]
    (hchrom : IsChromaticPolynomial (coneGraph B)
      ((X : ℝ[X]) * (X - C 1) ^ m * (X - C 2) ^ 2 * (X - C 3)))
    (hnum : IsChromaticNumber (coneGraph B) 4)
    (hbase : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      1 / 2 ≤ cliqueDensity 2 V → baseTarget (cliqueDensity 2 V) ≤ homDensity B V) :
    Taeyoung.SatisfiesLowerBound (coneGraph B) := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (X : ℝ[X]) * (X - C 1) ^ m * (X - C 2) ^ 2 * (X - C 3) :=
    IsChromaticPolynomial.unique (H := coneGraph B) hP hchrom
  have hreq : r = 4 := IsChromaticNumber.unique (H := coneGraph B) hr hnum
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := coneGraph_baseTarget_bound B hbase W hp
  change chromaticTarget (V := Fin (m + 1 + 2 + 1)) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_pawCone m hone]
    exact hkey

end Taeyoung.Methods.PawCone
