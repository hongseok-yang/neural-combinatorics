/-
# High-density theorem — moment expansion of `neckSum` (M1, `Thm expansion`), step 0

This begins the **hard** half: expressing `neckSum` (equivalently `Φ_m`) in the compression moments
`s_j = specMoment = ⟨g, Aʲ g⟩` so the positivity argument (`𝓟_{m,r} ≥ 0`, M3–M6) can be reached.
Nothing here proves positivity — it only rewrites the object into the moment-friendly form.

Step 0 (this file): the complement's `B`-operator iterate collapses to the plain `W`-path iterate.
Because `B_{1-W} f = (∫f)·1 − T_{1-W} f = (∫f)·1 − ((∫f)·1 − T_W f) = T_W f`, we have
`complIter (compl W) = pathIter W`.  Hence the necklace sum is a bilinear pairing of *complement*
path-iterates against *`W`* path-iterates:

  `neckSum W μ m = Σ_{j=0}^{m-2} (−1)ʲ ⟨ pathIter (compl W) j , pathIter W (m-1-j) ⟩`,

the shape the two-sided generating functions `𝓛_W`, `𝓛_U` (plan Tier 1) are read off from.  Expanding
each `pathIter` in the compression basis `{1, h_0, h_1, …}` via `kernelOp_compressIter`
(`T_W hₖ = sₖ·1 + h_{k+1}`) and collapsing `⟨h_i, h_j⟩ = s_{i+j}` is the next (large) step.
-/

import OddCycleBound.HighDensity.GraphonReduction

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.HighDensity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U W : Ω → Ω → ℝ}

/-- The complement kernel operator on `Good` inputs: `T_{1-U} f = (∫f)·1 − T_U f`. -/
lemma kernelOp_compl (hU : IsGraphon U μ) {f : Ω → ℝ} (hf : Good f) (x : Ω) :
    kernelOp (compl U) μ f x = mean μ f - kernelOp U μ f x := by
  have hfun : (fun y => compl U x y * f y) = (fun y => f y - U x y * f y) := by
    funext y; rw [compl]; ring
  show (∫ y, compl U x y * f y ∂μ) = mean μ f - kernelOp U μ f x
  rw [hfun, integral_sub hf.integrable (integrable_Uf hU hf x)]
  rfl

/-- **`B_{1-U} = T_U`.**  The complement `B`-operator iterate `complIter (compl U) n = Bⁿ 1` is just
the `U`-path iterate `kernelOpⁿ 1 = pathIter U n`. -/
lemma complIter_compl_eq_pathIter (hU : IsGraphon U μ) (n : ℕ) :
    complIter (compl U) μ n = pathIter U μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    show mean μ (complIter (compl U) μ n) - kernelOp (compl U) μ (complIter (compl U) μ n) x
        = kernelOp U μ (pathIter U μ n) x
    rw [ih, kernelOp_compl hU (good_pathIter hU n)]
    ring

/-- **`neckSum` as a complement-path / `W`-path pairing.**  Applying `B_{1-W} = T_W`,
`neckSum W μ m = Σ_{j<m-1} (−1)ʲ ⟨ pathIter (compl W) j , pathIter W (m-1-j) ⟩`. -/
lemma neckSum_eq (hW : IsGraphon W μ) (m : ℕ) :
    neckSum W μ m
      = ∑ j ∈ Finset.range (m - 1),
          (-1 : ℝ) ^ j * pairing μ (pathIter (compl W) μ j) (pathIter W μ (m - 1 - j)) := by
  unfold neckSum
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [complIter_compl_eq_pathIter hW (m - 1 - j)]

end OddCycleBound.HighDensity
