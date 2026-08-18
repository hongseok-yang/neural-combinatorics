import Taeyoung.Methods.ConeBound
import Taeyoung.Methods.AffineProduct

/-!
# Cones over a base with a verified affine-product target

`notes/six_verified_base_cones.tex` states a conditional cone lemma and applies
it to six five-vertex bases.  Its hypotheses on the base target — nonnegative,
nondecreasing, convex on `[a,1]`, vanishing at `a` — are exactly what holds for
a product of affine factors with nonnegative slopes, which is what every one of
those targets is.  So the lemma is stated here in that form, and the six
applications reduce to naming a list of slopes.

Two theorems:

* `coneGraph_pow_bound` — the note's Lemma, with the target still abstract.  It
  is `coneGraph_bound` specialised to the tangent point `c = 2 - 1/p`, which is
  where `weighted_rootedTriangle` makes the correction term nonnegative.
* `satisfiesLowerBound_of_baseCone` — the packaged form.  Given the base bound
  `t(B,V) ≥ ∏(1 - kᵢ(1-z))` above `1 - 1/kmax`, the cone satisfies the
  catalogue proposition on its own full interval, because
  `pow_mul_affineProd_shift` identifies `p^{v(B)}·φ(2 - 1/p)` with the *cone's*
  target rather than merely bounding it.
-/

open MeasureTheory Polynomial

namespace Taeyoung.Methods.BaseCone

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link

-- `Ω` is fixed at universe `0`, as in `Methods/ConeBound.lean`.
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The conditional cone bound at the tangent point.**  The correction term of
`coneGraph_bound` vanishes at `c = 2 - 1/p`, so all that survives is Jensen. -/
theorem coneGraph_pow_bound {h : ℕ} (B : SimpleGraph (Fin (h + 2)))
    [DecidableRel B.Adj] (W : Graphon Ω μ) {φ : ℝ → ℝ} {a lam : ℝ}
    (hφa : φ a = 0) (hlam : 0 ≤ lam) (ha1 : a ≤ 1)
    (hppos : 0 < cliqueDensity 2 W)
    (htangent : ∀ w, a ≤ w → w ≤ 1 →
      φ (2 - 1 / cliqueDensity 2 W) +
        lam * (w - (2 - 1 / cliqueDensity 2 W)) ≤ φ w)
    (hφc : 0 ≤ φ (2 - 1 / cliqueDensity 2 W))
    (hbase : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      a ≤ cliqueDensity 2 V → φ (cliqueDensity 2 V) ≤ homDensity B V) :
    cliqueDensity 2 W ^ (h + 2) * φ (2 - 1 / cliqueDensity 2 W) ≤
      homDensity (coneGraph B) W := by
  set p := cliqueDensity 2 W with hpdef
  have hcorr : (2 - 1 / p) * moment W (h + 2) ≤
      ∫ x, degree W x ^ h * rootedTriangle W x ∂μ := by
    have hwrt := weighted_rootedTriangle (W := W) h
    rw [← hpdef] at hwrt
    rw [show (2 : ℝ) - 1 / p = (2 * p - 1) / p by field_simp,
      div_mul_eq_mul_div, div_le_iff₀ hppos]
    nlinarith [hwrt]
  have hmain := coneGraph_bound (h := h) B W (φ := φ) (a := a) (c := 2 - 1 / p)
    (lam := lam) hφa hlam htangent ha1 hbase hφc hcorr
  have hmom : p ^ (h + 2) ≤ moment W (h + 2) := by
    have := RootedTriangleTree.pow_le_moment W (h + 2)
    rwa [← hpdef] at this
  exact le_trans (mul_le_mul_of_nonneg_right hmom hφc) hmain

/-- **The verified-base cone density bound.**  `ks` lists the roots of `χ_B`
with multiplicity and `kmax` is the largest, so the base bound is assumed on
`[1 - 1/kmax, 1]`.  The cone's bound holds on `[1 - 1/(kmax+1), 1]`, and its own
root list is `ks` shifted by one. -/
theorem coneGraph_affineProd_bound {h : ℕ} (B : SimpleGraph (Fin (h + 2)))
    [DecidableRel B.Adj] (ks : List ℝ) {kmax : ℝ}
    (hlen : ks.length = h + 2) (hkpos : 0 < kmax)
    (hk0 : ∀ k ∈ ks, 0 ≤ k) (hkle : ∀ k ∈ ks, k ≤ kmax) (hmem : kmax ∈ ks)
    (hbase : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      1 - 1 / kmax ≤ cliqueDensity 2 V →
        affineProd ks (cliqueDensity 2 V) ≤ homDensity B V)
    (W : Graphon Ω μ) (hp : 1 - 1 / (kmax + 1) ≤ cliqueDensity 2 W) :
    affineProd (ks.map (· + 1)) (cliqueDensity 2 W) ≤
      homDensity (coneGraph B) W := by
  have hk1 : (0 : ℝ) < kmax + 1 := by linarith
  have hppos : (0 : ℝ) < cliqueDensity 2 W := by
    have : 1 / (kmax + 1) < 1 := by rw [div_lt_one hk1]; linarith
    linarith
  have hpne : cliqueDensity 2 W ≠ 0 := ne_of_gt hppos
  -- the tangent point lies above the base threshold
  have hc : 1 - 1 / kmax ≤ 2 - 1 / cliqueDensity 2 W := by
    have hinv : 1 / cliqueDensity 2 W ≤ 1 + 1 / kmax := by
      have hkey : (1 : ℝ) ≤ (1 + 1 / kmax) * cliqueDensity 2 W := by
        have hid : (1 + 1 / kmax) * (1 - 1 / (kmax + 1)) = 1 := by
          field_simp
          ring
        have hpos : (0 : ℝ) < 1 + 1 / kmax := by positivity
        calc (1 : ℝ) = (1 + 1 / kmax) * (1 - 1 / (kmax + 1)) := hid.symm
          _ ≤ (1 + 1 / kmax) * cliqueDensity 2 W :=
              mul_le_mul_of_nonneg_left hp hpos.le
      rw [div_le_iff₀ hppos]
      linarith
    linarith
  have ha1 : 1 - 1 / kmax ≤ 1 := by
    have : (0 : ℝ) < 1 / kmax := by positivity
    linarith
  have hfacC := affineProd_factor_nonneg hkpos hk0 hkle hc
  have hkey := coneGraph_pow_bound B W
    (φ := affineProd ks) (a := 1 - 1 / kmax)
    (lam := affineProdDeriv ks (2 - 1 / cliqueDensity 2 W))
    (affineProd_threshold hkpos hmem) (affineProdDeriv_nonneg hk0 hfacC) ha1
    hppos
    (fun w hw _ ↦ affineProd_tangent hk0 hfacC
      (affineProd_factor_nonneg hkpos hk0 hkle hw))
    (affineProd_nonneg hfacC) hbase
  rwa [show cliqueDensity 2 W ^ (h + 2) = cliqueDensity 2 W ^ ks.length from
      by rw [hlen],
    pow_mul_affineProd_shift ks hpne] at hkey

/-- **The verified-base cone theorem.**  The cone's interval
`[1 - 1/(kmax+1), 1]` is exactly its admissible interval when
`χ(K₁ ∨ B) = kmax + 2`, so the bound covers the whole required range. -/
theorem satisfiesLowerBound_of_baseCone {h : ℕ} (B : SimpleGraph (Fin (h + 2)))
    [DecidableRel B.Adj] (ks : List ℝ) {kmax : ℝ} {r : ℕ}
    (hlen : ks.length = h + 2) (hkpos : 0 < kmax)
    (hk0 : ∀ k ∈ ks, 0 ≤ k) (hkle : ∀ k ∈ ks, k ≤ kmax) (hmem : kmax ∈ ks)
    (hchrom : IsChromaticPolynomial (coneGraph B)
      (((0 :: ks.map (· + 1)).map fun k ↦ (X : ℝ[X]) - C k).prod))
    (hnum : IsChromaticNumber (coneGraph B) r)
    (hr : ((r - 1 : ℕ) : ℝ) = kmax + 1)
    (hbase : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      1 - 1 / kmax ≤ cliqueDensity 2 V →
        affineProd ks (cliqueDensity 2 V) ≤ homDensity B V) :
    Taeyoung.SatisfiesLowerBound (coneGraph B) := by
  intro P s hP hs Ω instM μ instP W hadm
  have hPeq : P = ((0 :: ks.map (· + 1)).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := coneGraph B) hP hchrom
  have hseq : s = r := IsChromaticNumber.unique (H := coneGraph B) hs hnum
  subst hPeq
  subst hseq
  have hp : 1 - 1 / (kmax + 1) ≤ cliqueDensity 2 W := by
    have h := hadm
    rw [admissibleDensity, hr] at h
    exact h
  have hkey := coneGraph_affineProd_bound B ks hlen hkpos hk0 hkle hmem hbase W hp
  change Taeyoung.chromaticTarget (V := Fin (h + 2 + 1)) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone, affineProd_at_one] at hkey
    exact hkey
  · rw [chromaticTarget_affineProd (0 :: ks.map (· + 1))
      (by simp [hlen]) hone, affineProd_cons]
    simpa using hkey

/-! ### The conditional forest form -/

/-- **If a forest satisfies Sidorenko, its cone satisfies the catalogue
proposition.**

For a forest `F` with `c` components and `e ≥ 1` edges, `χ_F(x) = x^c(x-1)^e`,
so the root list is `c` zeros followed by `e` ones and `affineProd` of it is
`z^e` — the Sidorenko bound itself.  The largest slope is `1`, so the base bound
is required on all of `[0,1]`, and the cone's interval is `[1/2,1]`, which is
its full admissible interval since `χ(K₁ ∨ F) = 3`.

This is the honest shape of the cones-over-forests methodology: the Sidorenko
input is a hypothesis, not something proved here.  A row whose forest is a union
of stars and single edges discharges it by Jensen and multiplicativity; a row
whose forest contains `P₄` discharges it only once path Sidorenko is available. -/
theorem satisfiesLowerBound_coneGraph_of_sidorenko {h : ℕ}
    (F : SimpleGraph (Fin (h + 2))) [DecidableRel F.Adj] {c e : ℕ}
    (hlen : c + e = h + 2) (he : 0 < e)
    (hchrom : IsChromaticPolynomial (coneGraph F)
      ((((0 : ℝ) :: (List.replicate c (0 : ℝ) ++ List.replicate e 1).map (· + 1)).map
        fun k ↦ (X : ℝ[X]) - C k).prod))
    (hnum : IsChromaticNumber (coneGraph F) 3)
    (hSidorenko : ∀ {Ω' : Type} [MeasurableSpace Ω'] {ν : Measure Ω'}
      [IsProbabilityMeasure ν] (V : Graphon Ω' ν),
      cliqueDensity 2 V ^ e ≤ homDensity F V) :
    Taeyoung.SatisfiesLowerBound (coneGraph F) := by
  refine satisfiesLowerBound_of_baseCone F
    (List.replicate c (0 : ℝ) ++ List.replicate e 1) (kmax := 1) (r := 3)
    (by rw [List.length_append, List.length_replicate, List.length_replicate]; omega)
    one_pos ?_ ?_ ?_ hchrom hnum (by norm_num) ?_
  · intro k hk
    rcases List.mem_append.mp hk with h | h
    · rw [List.eq_of_mem_replicate h]
    · rw [List.eq_of_mem_replicate h]; norm_num
  · intro k hk
    rcases List.mem_append.mp hk with h | h
    · rw [List.eq_of_mem_replicate h]; norm_num
    · rw [List.eq_of_mem_replicate h]
  · exact List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩)
  · intro Ω' _ ν _ V _
    rw [affineProd_forestRoots]
    exact hSidorenko V

end Taeyoung.Methods.BaseCone
