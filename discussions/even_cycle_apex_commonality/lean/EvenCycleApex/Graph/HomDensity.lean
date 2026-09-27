import EvenCycleApex.Graph.Apex
import EvenCycleApex.Foundation.Defs
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Homomorphism densities on an arbitrary probability space

Blueprint `def:densities` and `def:normalization`; plan D4 and D5.

For a finite simple graph `F` on `Fin v`, a kernel `L : Ω → Ω → ℝ` and a measure `μ`,

```
  t(F, L) = ∫_{Ω^v} ∏_{ij ∈ E(F), i < j} L(x_i, x_j)  dμ^{⊗v}(x),
```

one factor per edge (`homDensity`).  With `U = 2W − 1` and `S_σ = 1 + σU`,
`colour_normalization` is `E_σ t(F, S_σ) = 2^{|E(F)|−1} M(F, W)`, where
`M(F, W) = t(F, W) + t(F, 1 − W)`; `normalizedApexDensity` and `normalizedCycleDensity` are the
blueprint's `A_{n/2,k}` and `R_n`.
-/

open MeasureTheory Finset

namespace EvenCycleApex

variable {Ω : Type*}

section Density

variable [MeasurableSpace Ω]

/-- **Homomorphism density** `t(F, L) = ∫_{Ω^V} ∏_{ij ∈ E(F)} L(x_i, x_j)`, one factor per
unordered edge (written as the ordered pair `i < j`). -/
noncomputable def homDensity {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (L : Ω → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ x : Fin v → Ω, ∏ p ∈ (Finset.univ.filter fun p : Fin v × Fin v => p.1 < p.2 ∧ F.Adj p.1 p.2),
      L (x p.1) (x p.2) ∂(Measure.pi fun _ => μ)

/-- The edge product of `F` at a vertex assignment `x`. -/
def edgeProd {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] (L : Ω → Ω → ℝ)
    (x : Fin v → Ω) : ℝ :=
  ∏ p ∈ edgePairs F, L (x p.1) (x p.2)

lemma homDensity_eq_integral_edgeProd {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (L : Ω → Ω → ℝ) (μ : Measure Ω) :
    homDensity F L μ = ∫ x, edgeProd F L x ∂(Measure.pi fun _ => μ) := rfl

/-! ### Measurability and integrability of the edge product -/

section Integrable

variable {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj] {L : Ω → Ω → ℝ}

lemma measurable_edgeFactor (hL : Measurable (Function.uncurry L)) (a b : Fin v) :
    Measurable fun x : Fin v → Ω => L (x a) (x b) := by
  have h : Measurable fun x : Fin v → Ω => (x a, x b) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply b)
  exact hL.comp h

lemma measurable_edgeProd (hL : Measurable (Function.uncurry L)) : Measurable (edgeProd F L) :=
  Finset.measurable_prod _ fun p _ => measurable_edgeFactor hL p.1 p.2

omit [MeasurableSpace Ω] in
lemma abs_edgeProd_le {B : ℝ} (hLB : ∀ x y, |L x y| ≤ B) (x : Fin v → Ω) :
    |edgeProd F L x| ≤ B ^ (edgePairs F).card := by
  rw [edgeProd, Finset.abs_prod]
  calc ∏ p ∈ edgePairs F, |L (x p.1) (x p.2)| ≤ ∏ _p ∈ edgePairs F, B :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p _ => hLB _ _
    _ = B ^ (edgePairs F).card := Finset.prod_const B

lemma integrable_edgeProd {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hL : Measurable (Function.uncurry L)) {B : ℝ} (hLB : ∀ x y, |L x y| ≤ B) :
    Integrable (edgeProd F L) (Measure.pi fun _ => μ) := by
  refine (integrable_const (B ^ (edgePairs F).card)).mono'
    (measurable_edgeProd F hL).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_edgeProd_le F hLB x

end Integrable

end Density

/-! ### Signed and colour kernels -/

/-- The signed kernel `U = 2W − 1`. -/
def signedKernel (W : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 2 * W x y - 1

/-- The colour kernel `S_σ = 1 + σ U`; the blueprint uses `σ = ±1`. -/
def colourKernel (σ : ℝ) (U : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 + σ * U x y

lemma colourKernel_one_signed (W : Ω → Ω → ℝ) :
    colourKernel 1 (signedKernel W) = fun x y => 2 * W x y := by
  funext x y; simp only [colourKernel, signedKernel]; ring

lemma colourKernel_neg_one_signed (W : Ω → Ω → ℝ) :
    colourKernel (-1) (signedKernel W) = fun x y => 2 * cmpl W x y := by
  funext x y; simp only [colourKernel, signedKernel, cmpl]; ring

variable [MeasurableSpace Ω]

/-- Scaling a kernel by `c` scales the density by `c ^ |E|`. -/
lemma homDensity_const_mul {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (c : ℝ) (L : Ω → Ω → ℝ) (μ : Measure Ω) :
    homDensity F (fun x y => c * L x y) μ = c ^ (edgePairs F).card * homDensity F L μ := by
  rw [homDensity_eq_integral_edgeProd, homDensity_eq_integral_edgeProd, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [edgeProd, Finset.prod_mul_distrib, Finset.prod_const]

/-! ### Normalization -/

/-- `M(F, W) = t(F, W) + t(F, 1 − W)`. -/
noncomputable def commonalityM {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (W : Ω → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  homDensity F W μ + homDensity F (cmpl W) μ

/-- **`def:normalization`.**  `E_σ t(F, S_σ) = 2^{|E(F)|−1} M(F, W)`, written without natural
subtraction as `(t(F, S₊) + t(F, S₋)) / 2 = 2^{|E(F)|} / 2 · M(F, W)`. -/
theorem colour_normalization {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (W : Ω → Ω → ℝ) (μ : Measure Ω) :
    (homDensity F (colourKernel 1 (signedKernel W)) μ
        + homDensity F (colourKernel (-1) (signedKernel W)) μ) / 2
      = 2 ^ (edgePairs F).card / 2 * commonalityM F W μ := by
  rw [colourKernel_one_signed, colourKernel_neg_one_signed, homDensity_const_mul,
    homDensity_const_mul, commonalityM]
  ring

/-- The normalized apex density `A_{n/2,k} = 2^{n(k+1)−1} M(C_n^{+k}, W)`. -/
noncomputable def normalizedApexDensity (W : Ω → Ω → ℝ) (μ : Measure Ω) (n k : ℕ) : ℝ :=
  2 ^ (n * (k + 1)) / 2 * commonalityM (apexCycle n k) W μ

/-- The normalized cycle density `R_n = 2^{n−1} M(C_n, W)`. -/
noncomputable def normalizedCycleDensity (W : Ω → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  2 ^ n / 2 * commonalityM (SimpleGraph.cycleGraph n) W μ

/-- `A_{n/2,k} = E_σ t(C_n^{+k}, S_σ)` for `n ≥ 3`. -/
theorem normalizedApexDensity_eq_colour_mean (W : Ω → Ω → ℝ) (μ : Measure Ω) {n k : ℕ}
    (hn : 3 ≤ n) :
    normalizedApexDensity W μ n k
      = (homDensity (apexCycle n k) (colourKernel 1 (signedKernel W)) μ
          + homDensity (apexCycle n k) (colourKernel (-1) (signedKernel W)) μ) / 2 := by
  rw [colour_normalization, apexCycle_edgeCount hn, normalizedApexDensity]

/-- `R_n = E_σ t(C_n, S_σ)` for `n ≥ 3`. -/
theorem normalizedCycleDensity_eq_colour_mean (W : Ω → Ω → ℝ) (μ : Measure Ω) {n : ℕ}
    (hn : 3 ≤ n) :
    normalizedCycleDensity W μ n
      = (homDensity (SimpleGraph.cycleGraph n) (colourKernel 1 (signedKernel W)) μ
          + homDensity (SimpleGraph.cycleGraph n) (colourKernel (-1) (signedKernel W)) μ) / 2 := by
  rw [colour_normalization, cycleGraph_card_edgePairs hn, normalizedCycleDensity]

end EvenCycleApex
