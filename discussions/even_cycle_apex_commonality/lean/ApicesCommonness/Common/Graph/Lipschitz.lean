import ApicesCommonness.Common.Graph.PairMarginal
import ApicesCommonness.Common.Foundation.Continuity

/-!
# Homomorphism densities are `L¹`-Lipschitz

Blueprint `lem:L1-counting`.  If `|L|, |L'| ≤ B` with `B ≥ 1`, and `F` has `e` edges, then

```
  |t(F, L) − t(F, L')| ≤ e · B^{e−1} · ‖L − L'‖₁,        ‖D‖₁ = ∫∫ |D(x, y)| dμ dμ.
```

The proof telescopes the edge product (`abs_prod_sub_prod_le`); each edge contributes the integral
of `|L − L'|` at its two endpoints, which is `‖L − L'‖₁` by the pair marginal (`integral_pair`) and
Fubini.  The norm `l1norm` is the one of the copied `Foundation/Continuity.lean`.
-/

open MeasureTheory Finset

namespace ApicesCommonness

/-- **Telescoping.**  If all factors are bounded by `B ≥ 1`, then
`|∏ f − ∏ g| ≤ B^{|s|−1} ∑ |f − g|`. -/
lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ B ^ (s.card - 1) * ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    have hf' : ∀ i ∈ s, |f i| ≤ B := fun i hi => hf i (mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, |g i| ≤ B := fun i hi => hg i (mem_insert_of_mem hi)
    have hPf : |∏ i ∈ s, f i| ≤ B ^ s.card := by
      rw [abs_prod]
      calc ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, B := prod_le_prod (fun _ _ => abs_nonneg _) hf'
        _ = B ^ s.card := prod_const B
    have hga : |g a| ≤ B := hg a (mem_insert_self a s)
    have hsum : 0 ≤ ∑ i ∈ s, |f i - g i| := sum_nonneg fun _ _ => abs_nonneg _
    -- `B · B^{|s|−1} · Σ ≤ B^{|s|} · Σ`: equality when `s` is nonempty, and `Σ = 0` otherwise.
    have hstep : B * (B ^ (s.card - 1) * ∑ i ∈ s, |f i - g i|)
        ≤ B ^ s.card * ∑ i ∈ s, |f i - g i| := by
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hne.card_pos]
    rw [prod_insert ha, prod_insert ha, sum_insert ha, card_insert_of_notMem ha,
      Nat.add_sub_cancel]
    calc |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i|
        = |(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)| := by ring_nf
      _ ≤ |f a - g a| * |∏ i ∈ s, f i| + |g a| * |∏ i ∈ s, f i - ∏ i ∈ s, g i| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ |f a - g a| * B ^ s.card + B * (B ^ (s.card - 1) * ∑ i ∈ s, |f i - g i|) := by
          gcongr
          exact ih hf' hg'
      _ ≤ |f a - g a| * B ^ s.card + B ^ s.card * ∑ i ∈ s, |f i - g i| := by linarith
      _ = B ^ s.card * (|f a - g a| + ∑ i ∈ s, |f i - g i|) := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One edge term `|L − L'|(x_a, x_b)` is integrable against `μ^{⊗v}`. -/
lemma integrable_edgeTerm {v : ℕ} {L L' : Ω → Ω → ℝ} (hL : Measurable (Function.uncurry L))
    (hL' : Measurable (Function.uncurry L')) {B : ℝ} (hLB : ∀ x y, |L x y| ≤ B)
    (hL'B : ∀ x y, |L' x y| ≤ B) (a b : Fin v) :
    Integrable (fun x : Fin v → Ω => |L (x a) (x b) - L' (x a) (x b)|)
      (Measure.pi fun _ => μ) := by
  have hm : Measurable fun x : Fin v → Ω => |L (x a) (x b) - L' (x a) (x b)| :=
    continuous_abs.measurable.comp
      ((measurable_edgeFactor hL a b).sub (measurable_edgeFactor hL' a b))
  refine (integrable_const (2 * B)).mono' hm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  calc |L (x a) (x b) - L' (x a) (x b)| ≤ |L (x a) (x b)| + |L' (x a) (x b)| := abs_sub _ _
    _ ≤ 2 * B := by linarith [hLB (x a) (x b), hL'B (x a) (x b)]

/-- **`lem:L1-counting`.**  `|t(F, L) − t(F, L')| ≤ e B^{e−1} ‖L − L'‖₁` for kernels bounded by
`B ≥ 1`, where `e = |E(F)|`. -/
theorem homDensity_L1_lipschitz {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {L L' : Ω → Ω → ℝ} (hL : Measurable (Function.uncurry L))
    (hL' : Measurable (Function.uncurry L')) {B : ℝ} (hB : 1 ≤ B) (hLB : ∀ x y, |L x y| ≤ B)
    (hL'B : ∀ x y, |L' x y| ≤ B) :
    |homDensity F L μ - homDensity F L' μ|
      ≤ (edgePairs F).card * B ^ ((edgePairs F).card - 1)
          * l1norm μ (fun x y => L x y - L' x y) := by
  set e := (edgePairs F).card with he
  -- the edge difference as a function on `Ω × Ω`
  set D : Ω × Ω → ℝ := fun p => |L p.1 p.2 - L' p.1 p.2| with hD
  have hDm : Measurable D := continuous_abs.measurable.comp (hL.sub hL')
  have hDint : Integrable D (μ.prod μ) := by
    refine (integrable_const (2 * B)).mono' hDm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, hD, abs_abs]
    calc |L p.1 p.2 - L' p.1 p.2| ≤ |L p.1 p.2| + |L' p.1 p.2| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hLB p.1 p.2, hL'B p.1 p.2]
  have hedge : ∀ p ∈ edgePairs F,
      ∫ x, |L (x p.1) (x p.2) - L' (x p.1) (x p.2)| ∂(Measure.pi fun _ => μ)
        = l1norm μ (fun x y => L x y - L' x y) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (mem_edgePairs.mp hp).1.ne
    rw [integral_pair hne (f := D) hDm.aestronglyMeasurable, integral_prod D hDint]
    rfl
  have hI := integrable_edgeProd F (μ := μ) hL hLB
  have hI' := integrable_edgeProd F (μ := μ) hL' hL'B
  have hterm := fun p : Fin v × Fin v => integrable_edgeTerm (μ := μ) hL hL' hLB hL'B p.1 p.2
  rw [homDensity_eq_integral_edgeProd, homDensity_eq_integral_edgeProd, ← integral_sub hI hI']
  calc |∫ x, edgeProd F L x - edgeProd F L' x ∂(Measure.pi fun _ => μ)|
      ≤ ∫ x, |edgeProd F L x - edgeProd F L' x| ∂(Measure.pi fun _ => μ) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, B ^ (e - 1) * ∑ p ∈ edgePairs F, |L (x p.1) (x p.2) - L' (x p.1) (x p.2)|
          ∂(Measure.pi fun _ => μ) := by
        refine integral_mono (hI.sub hI').abs
          ((integrable_finsetSum _ fun p _ => hterm p).const_mul _) fun x => ?_
        exact abs_prod_sub_prod_le _ _ _ hB (fun p _ => hLB _ _) (fun p _ => hL'B _ _)
    _ = B ^ (e - 1) * ∑ p ∈ edgePairs F,
          ∫ x, |L (x p.1) (x p.2) - L' (x p.1) (x p.2)| ∂(Measure.pi fun _ => μ) := by
        rw [integral_const_mul, integral_finsetSum _ fun p _ => hterm p]
    _ = e * B ^ (e - 1) * l1norm μ (fun x y => L x y - L' x y) := by
        rw [sum_congr rfl hedge, sum_const, nsmul_eq_mul, ← he]
        ring

omit [IsProbabilityMeasure μ] in
/-- The complement does not change the `L¹` distance. -/
lemma l1norm_cmpl_sub (W V : Ω → Ω → ℝ) :
    l1norm μ (fun x y => cmpl W x y - cmpl V x y) = l1norm μ (fun x y => W x y - V x y) := by
  simp only [l1norm, cmpl]
  congr 1; funext x; congr 1; funext y
  rw [show 1 - W x y - (1 - V x y) = -(W x y - V x y) by ring, abs_neg]

/-- **`lem:L1-counting`, graphon form.**  For graphons, `|M(F, W) − M(F, V)| ≤ 2 e ‖W − V‖₁`,
`e = |E(F)|`: apply `homDensity_L1_lipschitz` with `B = 1` to `W, V` and to `1 − W, 1 − V`. -/
theorem commonalityM_L1_lipschitz {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    {W V : Ω → Ω → ℝ} (hW : Foundation.IsGraphon W μ) (hV : Foundation.IsGraphon V μ) :
    |commonalityM F W μ - commonalityM F V μ|
      ≤ 2 * (edgePairs F).card * l1norm μ (fun x y => W x y - V x y) := by
  have hb : ∀ {U : Ω → Ω → ℝ}, Foundation.IsGraphon U μ → ∀ x y, |U x y| ≤ 1 := fun hU x y => by
    rw [abs_le]; exact ⟨by linarith [hU.nonneg x y], hU.le_one x y⟩
  have h1 := homDensity_L1_lipschitz (μ := μ) F hW.meas hV.meas le_rfl (hb hW) (hb hV)
  have h2 := homDensity_L1_lipschitz (μ := μ) F (isGraphon_cmpl hW).meas (isGraphon_cmpl hV).meas
    le_rfl (hb (isGraphon_cmpl hW)) (hb (isGraphon_cmpl hV))
  rw [one_pow, mul_one] at h1 h2
  rw [l1norm_cmpl_sub] at h2
  rw [commonalityM, commonalityM]
  calc |homDensity F W μ + homDensity F (cmpl W) μ - (homDensity F V μ + homDensity F (cmpl V) μ)|
      ≤ |homDensity F W μ - homDensity F V μ| + |homDensity F (cmpl W) μ - homDensity F (cmpl V) μ| := by
        rw [show homDensity F W μ + homDensity F (cmpl W) μ
              - (homDensity F V μ + homDensity F (cmpl V) μ)
            = (homDensity F W μ - homDensity F V μ)
              + (homDensity F (cmpl W) μ - homDensity F (cmpl V) μ) by ring]
        exact abs_add_le _ _
    _ ≤ 2 * (edgePairs F).card * l1norm μ (fun x y => W x y - V x y) := by linarith

end ApicesCommonness
