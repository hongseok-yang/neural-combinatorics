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

/-! ### Complement parity of the compression (graphon `frMoment_neg` / `trace_neg_pow` pillars)

The compression of the complement is the *negative* of the compression of `W`
(`compress (compl W) = − compress W`), because the constant direction (the hub) absorbs the `1 − ·`.
Iterating gives `compressIter (compl W) k = (−1)^{k+1} hₖ` and hence `specMoment (compl W) j =
(−1)ʲ sⱼ` — the graphon incarnation of the finite-rank parity pillars, and exactly what reduces the
cross-compression pairings in `neckSum` to pure `W`-moments. -/

private lemma integral_const_prob (c : ℝ) : (∫ (_ : Ω), c ∂μ) = c := by simp

/-- Scalar homogeneity of `kernelOp` (pointwise, unconditional). -/
lemma kernelOp_const_mul (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    kernelOp U μ (fun y => c * f y) x = c * kernelOp U μ f x := by
  show (∫ y, U x y * (c * f y) ∂μ) = c * ∫ y, U x y * f y ∂μ
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

/-- Scalar homogeneity of the compression. -/
lemma compress_const_mul (c : ℝ) (f : Ω → ℝ) :
    compress W μ (fun y => c * f y) = fun x => c * compress W μ f x := by
  funext x
  show kernelOp W μ (fun y => c * f y) x - mean μ (kernelOp W μ (fun y => c * f y))
      = c * (kernelOp W μ f x - mean μ (kernelOp W μ f))
  rw [kernelOp_const_mul]
  have hmean : mean μ (kernelOp W μ (fun y => c * f y)) = c * mean μ (kernelOp W μ f) := by
    show (∫ x, kernelOp W μ (fun y => c * f y) x ∂μ) = c * mean μ (kernelOp W μ f)
    rw [integral_congr_ae (ae_of_all _ fun x => kernelOp_const_mul c f x), integral_const_mul]
    rfl
  rw [hmean]; ring

/-- Row-degree of the complement: `degree (1-W) = 1 − degree W`. -/
lemma degree_compl (hW : IsGraphon W μ) (x : Ω) :
    degree (compl W) μ x = 1 - degree W μ x := by
  show ∫ y, compl W x y ∂μ = 1 - degree W μ x
  have hc : (fun y => compl W x y) = (fun y => (1 : ℝ) - W x y) := by funext y; rw [compl]
  rw [hc, integral_sub (integrable_const 1) ((goodK_of_isGraphon hW).integrable_row x),
    integral_const_prob]
  rfl

/-- Edge density of the complement: `edgeDensity (1-W) = 1 − edgeDensity W`. -/
lemma edgeDensity_compl (hW : IsGraphon W μ) :
    edgeDensity (compl W) μ = 1 - edgeDensity W μ := by
  show mean μ (degree (compl W) μ) = 1 - edgeDensity W μ
  have hdeg : degree (compl W) μ = fun x => 1 - degree W μ x := funext (degree_compl hW)
  rw [hdeg]
  show (∫ x, (1 - degree W μ x) ∂μ) = 1 - edgeDensity W μ
  rw [integral_sub (integrable_const 1) (good_degree hW).integrable, integral_const_prob]
  rfl

/-- Centered degree of the complement: `degCentered (1-W) = − degCentered W`. -/
lemma degCentered_compl (hW : IsGraphon W μ) :
    degCentered (compl W) μ = fun x => - degCentered W μ x := by
  funext x
  show degree (compl W) μ x - edgeDensity (compl W) μ = -(degree W μ x - edgeDensity W μ)
  rw [degree_compl hW x, edgeDensity_compl hW]; ring

/-- **`compress (compl W) = − compress W`** — the compression flips sign on the complement. -/
lemma compress_compl (hW : IsGraphon W μ) {f : Ω → ℝ} (hf : Good f) :
    compress (compl W) μ f = fun x => - compress W μ f x := by
  funext x
  show kernelOp (compl W) μ f x - mean μ (kernelOp (compl W) μ f)
      = -(kernelOp W μ f x - mean μ (kernelOp W μ f))
  have hk : ∀ y, kernelOp (compl W) μ f y = mean μ f - kernelOp W μ f y :=
    fun y => kernelOp_compl hW hf y
  have hmean : mean μ (kernelOp (compl W) μ f) = mean μ f - mean μ (kernelOp W μ f) := by
    show (∫ y, kernelOp (compl W) μ f y ∂μ) = mean μ f - mean μ (kernelOp W μ f)
    rw [integral_congr_ae (ae_of_all _ hk),
      integral_sub (integrable_const _) (good_kernelOp hW hf).integrable, integral_const_prob]
    rfl
  rw [hk x, hmean]; ring

/-- **`compressIter (compl W) k = (−1)^{k+1} hₖ`** — the complement compression iterate is the `W`
iterate with an alternating sign (graphon `frMoment_neg`). -/
lemma compressIter_compl (hW : IsGraphon W μ) (k : ℕ) :
    compressIter (compl W) μ k = fun x => (-1 : ℝ) ^ (k + 1) * compressIter W μ k x := by
  induction k with
  | zero =>
    funext x
    show degCentered (compl W) μ x = (-1 : ℝ) ^ (0 + 1) * compressIter W μ 0 x
    rw [compressIter_zero, congrFun (degCentered_compl hW) x]; ring
  | succ k ih =>
    have step : compressIter (compl W) μ (k + 1)
        = compress (compl W) μ (compressIter (compl W) μ k) := rfl
    rw [step, compress_compl hW (good_compressIter (isGraphon_compl hW) k), ih,
      compress_const_mul ((-1 : ℝ) ^ (k + 1)) (compressIter W μ k)]
    funext x
    show -((-1 : ℝ) ^ (k + 1) * compress W μ (compressIter W μ k) x)
        = (-1 : ℝ) ^ (k + 1 + 1) * compressIter W μ (k + 1) x
    have hdef : compress W μ (compressIter W μ k) = compressIter W μ (k + 1) := rfl
    rw [hdef, pow_succ]; ring

/-- **`specMoment (compl W) j = (−1)ʲ sⱼ`** — moment parity of the complement (graphon
`frMoment_neg` at the level of moments). -/
lemma specMoment_compl (hW : IsGraphon W μ) (j : ℕ) :
    specMoment (compl W) μ j = (-1 : ℝ) ^ j * specMoment W μ j := by
  show (∫ x, degCentered (compl W) μ x * compressIter (compl W) μ j x ∂μ)
      = (-1 : ℝ) ^ j * specMoment W μ j
  have hint : ∀ x, degCentered (compl W) μ x * compressIter (compl W) μ j x
      = (-1 : ℝ) ^ j * (degCentered W μ x * compressIter W μ j x) := by
    intro x
    rw [congrFun (degCentered_compl hW) x, congrFun (compressIter_compl hW j) x, pow_succ]
    ring
  rw [integral_congr_ae (ae_of_all _ hint), integral_const_mul]
  rfl

/-! ### Necklace pairings in closed path-density form

`neckSum` pairs `pathIter (compl W)` against `complIter (compl W)` — the *same* kernel `compl W` —
so the existing telescoping `pairing_pathIter_complIter_closed` (`Necklace.lean`) applies directly.
Its "complement means still to expand" are `mean (complIter (compl W) t) = pathDensity W t` (via
`B_{1-W}=T_W`), so every necklace pairing becomes an explicit finite sum of products of `W`- and
`(1-W)`-path densities — no operators, ready for the moment substitution `x_j → Σ sₖ`. -/

/-- The complement means are `W`-path densities: `mean (complIter (compl W) t) = pathDensity W t`. -/
lemma mean_complIter_compl (hW : IsGraphon W μ) (t : ℕ) :
    mean μ (complIter (compl W) μ t) = pathDensity W μ t := by
  rw [complIter_compl_eq_pathIter hW t]; rfl

/-- **Necklace pairing in path densities.**  `⟨pathIter (compl W) j, complIter (compl W) k⟩ =
Σ_{i<k} (−1)ⁱ · x_{k-1-i} · y_{j+i} + (−1)ᵏ · y_{j+k}`, with `x = pathDensity W`, `y = pathDensity
(compl W)`.  (Specialisation of `pairing_pathIter_complIter_closed` to `compl W`, folding
`mean(complIter (compl W)) = pathDensity W`.) -/
lemma pairing_compl_closed (hW : IsGraphon W μ) (j k : ℕ) :
    pairing μ (pathIter (compl W) μ j) (complIter (compl W) μ k)
      = (∑ i ∈ Finset.range k,
          (-1 : ℝ) ^ i * (pathDensity W μ (k - 1 - i) * pathDensity (compl W) μ (j + i)))
        + (-1 : ℝ) ^ k * pathDensity (compl W) μ (j + k) := by
  rw [pairing_pathIter_complIter_closed (isGraphon_compl hW) k j]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mean_complIter_compl hW (k - 1 - i)]

/-- **`neckSum` fully in path densities.**  Each necklace pairing replaced by its closed form; the
object is now an explicit double sum over products of `W`- and `(1-W)`-path densities. -/
lemma neckSum_pathDensity (hW : IsGraphon W μ) (m : ℕ) :
    neckSum W μ m
      = ∑ j ∈ Finset.range (m - 1),
          (-1 : ℝ) ^ j
            * ((∑ i ∈ Finset.range (m - 1 - j),
                  (-1 : ℝ) ^ i
                    * (pathDensity W μ (m - 1 - j - 1 - i) * pathDensity (compl W) μ (j + i)))
              + (-1 : ℝ) ^ (m - 1 - j) * pathDensity (compl W) μ (j + (m - 1 - j))) := by
  unfold neckSum
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairing_compl_closed hW j (m - 1 - j)]

end OddCycleBound.HighDensity
