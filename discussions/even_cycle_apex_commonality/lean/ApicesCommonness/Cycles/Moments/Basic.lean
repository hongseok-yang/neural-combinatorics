import ApicesCommonness.Cycles.Host.Spectral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Moment inequalities on finite probability spaces

Blueprint `lem:moment-basics`, `lem:pair-majorization`, `lem:length-lifting`, for weights `p`
on a finset (`pᵢ ≥ 0`, `∑ pᵢ = 1`).  All exponents here are real (plan D8); `X ^ q` is `Real.rpow`
of a nonnegative base.

* `moment_monotone`: `(E X^p)^{q/p} ≤ E X^q` for `X ≥ 0` and `1 ≤ p ≤ q` (Jensen for `y ↦ y^{q/p}`).
  Cauchy–Schwarz is Mathlib's `sum_sq_le_sum_mul_sum_of_sq_le_mul`, and `∑ xᵢ^s ≤ (∑ xᵢ)^s` is
  `sum_rpow_le_rpow_sum` (`Host/Spectral.lean`).
* `convex_two_point`: for convex `f` and `a ≤ b ≤ c ≤ e` with `a + e = b + c`,
  `f b + f c ≤ f a + f e` — the two-point case of Karamata, from the definition of convexity.
* `two_coordinate_power_comparison` (**`lem:pair-majorization`**): if `L₁ + L₂ ≥ r₁ + r₂` and
  `max L ≥ max r` (all `≥ 0`), then `L₁^s + L₂^s ≥ r₁^s + r₂^s` for real `s ≥ 1`.
* `length_lifting_two_fourth_moments` (**`lem:length-lifting`**): from `E V⁴ ≥ (r₊ + r₋)/2` and
  `E ω V⁴ ≥ max(r₊, r₋)` for a density `0 ≤ ω ≤ 2`, `E ω = 1`, deduce
  `E V^q ≥ (r₊^{q/4} + r₋^{q/4}) / 2` for real `q ≥ 4`.  The measures `ω · p` and `(2 − ω) · p` have
  mass one; nothing is divided by a weighted moment.
-/

open Finset

namespace ApicesCommonness

variable {ι : Type*}

/-- **`lem:moment-basics`, Jensen.**  `(E X^p)^{q/p} ≤ E X^q` for `X ≥ 0` and `1 ≤ p ≤ q`. -/
theorem moment_monotone (s : Finset ι) (w X : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (hX : ∀ i ∈ s, 0 ≤ X i) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    (∑ i ∈ s, w i * X i ^ p) ^ (q / p) ≤ ∑ i ∈ s, w i * X i ^ q := by
  have hp0 : 0 < p := by linarith
  have h := Real.rpow_arith_mean_le_arith_mean_rpow s w (fun i => X i ^ p) hw hw1
    (fun i hi => Real.rpow_nonneg (hX i hi) p) ((one_le_div hp0).mpr hpq)
  refine h.trans (le_of_eq (sum_congr rfl fun i hi => ?_))
  rw [← Real.rpow_mul (hX i hi), mul_div_cancel₀ q hp0.ne']

/-- **Two-point Karamata.**  For convex `f`, `a ≤ b ≤ c ≤ e` and `a + e = b + c`,
`f b + f c ≤ f a + f e`. -/
theorem convex_two_point {S : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ S f) {a b c e : ℝ}
    (ha : a ∈ S) (he : e ∈ S) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hsum : a + e = b + c) :
    f b + f c ≤ f a + f e := by
  rcases (hab.trans (hbc.trans hce)).eq_or_lt with hae | hae
  · -- degenerate: all four points coincide
    have hb : b = a := le_antisymm (by linarith) hab
    have hc : c = a := le_antisymm (by linarith) (hab.trans hbc)
    rw [hb, hc, ← hae]
  · set t : ℝ := (e - b) / (e - a) with ht
    have hea : 0 < e - a := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hea.le
    have ht1 : t ≤ 1 := (div_le_one hea).mpr (by linarith)
    have hb : b = t * a + (1 - t) * e := by
      rw [ht]; field_simp; ring
    have hc : c = (1 - t) * a + t * e := by
      rw [ht, show c = a + e - b by linarith]; field_simp; ring
    have h1 := hf.2 ha he ht0 (by linarith : 0 ≤ 1 - t) (by ring)
    have h2 := hf.2 ha he (by linarith : 0 ≤ 1 - t) ht0 (by ring)
    simp only [smul_eq_mul] at h1 h2
    rw [hb, hc]
    linarith

/-- **`lem:pair-majorization`.**  For `L₁, L₂, r₁, r₂ ≥ 0` with `L₁ + L₂ ≥ r₁ + r₂` and
`max L₁ L₂ ≥ max r₁ r₂`, `L₁^s + L₂^s ≥ r₁^s + r₂^s` for every real `s ≥ 1`. -/
theorem two_coordinate_power_comparison {L₁ L₂ r₁ r₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hsum : r₁ + r₂ ≤ L₁ + L₂) (hmax : max r₁ r₂ ≤ max L₁ L₂)
    {s : ℝ} (hs : 1 ≤ s) : r₁ ^ s + r₂ ^ s ≤ L₁ ^ s + L₂ ^ s := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun x : ℝ => x ^ s := convexOn_rpow hs
  have hmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → x ^ s ≤ y ^ s := fun hx hxy =>
    Real.rpow_le_rpow hx hxy (by linarith)
  -- the sorted version: `rl ≤ rh`, `Ll ≤ Lh`
  have key : ∀ {rh rl Lh Ll : ℝ}, 0 ≤ rl → rl ≤ rh → 0 ≤ Ll → Ll ≤ Lh → rh ≤ Lh →
      rh + rl ≤ Lh + Ll → rh ^ s + rl ^ s ≤ Lh ^ s + Ll ^ s := by
    intro rh rl Lh Ll hrl hrlh hLl hLlh hrhL hs'
    rcases le_or_gt rl Ll with h | h
    · exact add_le_add (hmono (hrl.trans hrlh) hrhL) (hmono hrl h)
    · -- `d = rl − Ll > 0`: move mass `d` from `rl` to `rh`, then increase `rh + d` to `Lh`
      have hstep : rl ^ s + rh ^ s ≤ Ll ^ s + (rh + (rl - Ll)) ^ s :=
        convex_two_point hconv (Set.mem_Ici.mpr hLl) (Set.mem_Ici.mpr (by linarith)) h.le hrlh
          (by linarith) (by ring)
      have hup : (rh + (rl - Ll)) ^ s ≤ Lh ^ s := hmono (by linarith) (by linarith)
      linarith
  rcases le_total r₂ r₁ with hr | hr <;> rcases le_total L₂ L₁ with hL | hL
  · rw [max_eq_left hr, max_eq_left hL] at hmax
    exact key hr₂ hr hL₂ hL hmax (by linarith)
  · rw [max_eq_left hr, max_eq_right hL] at hmax
    have := key hr₂ hr hL₁ hL hmax (by linarith)
    linarith
  · rw [max_eq_right hr, max_eq_left hL] at hmax
    have := key hr₁ hr hL₂ hL hmax (by linarith)
    linarith
  · rw [max_eq_right hr, max_eq_right hL] at hmax
    have := key hr₁ hr hL₁ hL hmax (by linarith)
    linarith

/-- **`lem:length-lifting`.**  Let `V ≥ 0`, `r₊, r₋ ≥ 0`, and `ω` a density with `0 ≤ ω ≤ 2`,
`E ω = 1`.  If `E V⁴ ≥ (r₊ + r₋)/2` and `E ω V⁴ ≥ max(r₊, r₋)`, then for every real `q ≥ 4`,
`E V^q ≥ (r₊^{q/4} + r₋^{q/4}) / 2`. -/
theorem length_lifting_two_fourth_moments (s : Finset ι) (p V ω : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) (hV : ∀ i ∈ s, 0 ≤ V i)
    (hω0 : ∀ i ∈ s, 0 ≤ ω i) (hω2 : ∀ i ∈ s, ω i ≤ 2) (hω1 : ∑ i ∈ s, p i * ω i = 1)
    {rp rm : ℝ} (hrp : 0 ≤ rp) (hrm : 0 ≤ rm)
    (hmean : (rp + rm) / 2 ≤ ∑ i ∈ s, p i * V i ^ (4 : ℝ))
    (hweight : max rp rm ≤ ∑ i ∈ s, p i * ω i * V i ^ (4 : ℝ)) {q : ℝ} (hq : 4 ≤ q) :
    (rp ^ (q / 4) + rm ^ (q / 4)) / 2 ≤ ∑ i ∈ s, p i * V i ^ q := by
  set t : ℝ := q / 4 with htdef
  have ht : 1 ≤ t := by rw [htdef, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]; linarith
  set Lp := ∑ i ∈ s, p i * ω i * V i ^ (4 : ℝ) with hLp
  set Lm := ∑ i ∈ s, p i * (2 - ω i) * V i ^ (4 : ℝ) with hLm
  have hV4 : ∀ i ∈ s, 0 ≤ V i ^ (4 : ℝ) := fun i hi => Real.rpow_nonneg (hV i hi) _
  have hLp0 : 0 ≤ Lp := sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (hp i hi) (hω0 i hi)) (hV4 i hi)
  have hLm0 : 0 ≤ Lm := sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (hp i hi) (by linarith [hω2 i hi])) (hV4 i hi)
  have hLsum : Lp + Lm = 2 * ∑ i ∈ s, p i * V i ^ (4 : ℝ) := by
    rw [hLp, hLm, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => by ring
  -- pair majorization at exponent `t`
  have hpair : rp ^ t + rm ^ t ≤ Lp ^ t + Lm ^ t :=
    two_coordinate_power_comparison hLp0 hLm0 hrp hrm (by linarith)
      (hweight.trans (le_max_left _ _)) ht
  -- Jensen under the two probability measures `ω p` and `(2 − ω) p`
  have hpow : ∀ i ∈ s, (V i ^ (4 : ℝ)) ^ t = V i ^ q := fun i hi => by
    rw [← Real.rpow_mul (hV i hi), htdef, mul_div_cancel₀ q (by norm_num)]
  have hJp : Lp ^ t ≤ ∑ i ∈ s, p i * ω i * V i ^ q := by
    have h := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => p i * ω i)
      (fun i => V i ^ (4 : ℝ)) (fun i hi => mul_nonneg (hp i hi) (hω0 i hi)) hω1 hV4 ht
    refine h.trans (le_of_eq (sum_congr rfl fun i hi => by rw [hpow i hi]))
  have hm1 : ∑ i ∈ s, p i * (2 - ω i) = 1 := by
    rw [show ∑ i ∈ s, p i * (2 - ω i) = 2 * ∑ i ∈ s, p i - ∑ i ∈ s, p i * ω i by
      rw [mul_sum, ← sum_sub_distrib]; refine sum_congr rfl fun i _ => by ring, hp1, hω1]
    norm_num
  have hJm : Lm ^ t ≤ ∑ i ∈ s, p i * (2 - ω i) * V i ^ q := by
    have h := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => p i * (2 - ω i))
      (fun i => V i ^ (4 : ℝ)) (fun i hi => mul_nonneg (hp i hi) (by linarith [hω2 i hi])) hm1
      hV4 ht
    refine h.trans (le_of_eq (sum_congr rfl fun i hi => by rw [hpow i hi]))
  have hsplit : ∑ i ∈ s, p i * ω i * V i ^ q + ∑ i ∈ s, p i * (2 - ω i) * V i ^ q
      = 2 * ∑ i ∈ s, p i * V i ^ q := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => by ring
  linarith

end ApicesCommonness
