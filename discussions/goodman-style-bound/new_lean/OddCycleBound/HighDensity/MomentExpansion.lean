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
import OddCycleBound.General.PathRecurrence

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

/-! ### The compression-basis expansion of a path iterate

`pathIter U a = kernelOpᵃ 1` expands in the basis `{1, h_0, h_1, …}` (`h_k = compressIter U k`) with
path-density coefficients:

  `pathIter U a = pathDensity U a · 1 + Σ_{k<a} pathDensity U (a-1-k) · h_k`,

the graphon `blockOp^a·e_hub` unroll.  Proof by induction: `kernelOp U 1 = p·1 + h_0`,
`kernelOp U h_k = s_k·1 + h_{k+1}` (`kernelOp_compressIter`) shift the basis; the `h`-coefficients
telescope by reindexing and the constant is the path-density recurrence `pathDensity_succ`. -/

/-- **Compression-basis expansion of `pathIter`.**  `pathIter U a = x_a·1 + Σ_{k<a} x_{a-1-k}·hₖ`
(`x = pathDensity U`, `hₖ = compressIter U k`). -/
lemma pathIter_expansion (hU : IsGraphon U μ) (a : ℕ) :
    pathIter U μ a
      = fun z => pathDensity U μ a
          + ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * compressIter U μ k z := by
  induction a with
  | zero =>
    funext z
    show (1 : ℝ)
        = pathDensity U μ 0 + ∑ k ∈ Finset.range 0, pathDensity U μ (0 - 1 - k) * compressIter U μ k z
    have h0 : pathDensity U μ 0 = 1 := mean_one
    rw [Finset.range_zero, Finset.sum_empty, add_zero, h0]
  | succ a ih =>
    funext z
    show (∫ y, U z y * pathIter U μ a y ∂μ)
        = pathDensity U μ (a + 1)
          + ∑ k ∈ Finset.range (a + 1), pathDensity U μ (a + 1 - 1 - k) * compressIter U μ k z
    -- expand the integrand via `ih`
    have hib : ∀ y, U z y * pathIter U μ a y
        = pathDensity U μ a * U z y
          + ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * (U z y * compressIter U μ k y) := by
      intro y
      have ihy : pathIter U μ a y
          = pathDensity U μ a + ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * compressIter U μ k y :=
        congrFun ih y
      rw [ihy, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    rw [integral_congr_ae (ae_of_all _ hib)]
    have hInt1 : Integrable (fun y => pathDensity U μ a * U z y) μ :=
      ((goodK_of_isGraphon hU).integrable_row z).const_mul _
    have hInt2 : Integrable
        (fun y => ∑ k ∈ Finset.range a,
          pathDensity U μ (a - 1 - k) * (U z y * compressIter U μ k y)) μ :=
      integrable_finsetSum _ fun k _ => (integrable_Uf hU (good_compressIter hU k) z).const_mul _
    rw [integral_add hInt1 hInt2, integral_const_mul,
      integral_finsetSum _ fun k _ => (integrable_Uf hU (good_compressIter hU k) z).const_mul _]
    have hterm : ∀ k, (∫ y, pathDensity U μ (a - 1 - k) * (U z y * compressIter U μ k y) ∂μ)
        = pathDensity U μ (a - 1 - k) * kernelOp U μ (compressIter U μ k) z := by
      intro k; rw [integral_const_mul]; rfl
    rw [Finset.sum_congr rfl fun k _ => hterm k,
      show (∫ y, U z y ∂μ) = degree U μ z from rfl, degree_eq' z]
    simp only [kernelOp_compressIter' hU, mul_add, Finset.sum_add_distrib]
    -- LHS = x_a(p + h_0 z) + Σ x_{a-1-k} s_k + Σ x_{a-1-k} h_{k+1} z; match RHS
    rw [pathDensity_succ hU a, Finset.sum_range_succ' (fun k =>
      pathDensity U μ (a + 1 - 1 - k) * compressIter U μ k z) a]
    have eMom : ∑ i ∈ Finset.range a, specMoment U μ i * pathDensity U μ (a - 1 - i)
        = ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * specMoment U μ k :=
      Finset.sum_congr rfl fun k _ => by ring
    have eShift : ∑ k ∈ Finset.range a,
          pathDensity U μ (a + 1 - 1 - (k + 1)) * compressIter U μ (k + 1) z
        = ∑ k ∈ Finset.range a, pathDensity U μ (a - 1 - k) * compressIter U μ (k + 1) z :=
      Finset.sum_congr rfl fun k _ => by
        rw [show a + 1 - 1 - (k + 1) = a - 1 - k from by omega]
    rw [eMom, eShift, show a + 1 - 1 - 0 = a from by omega]
    ring

/-! ### The necklace pairing in moments

Expanding `pathIter (compl W) j` in its own compression basis (`pathIter_expansion`), pairing against
`pathIter W k`, and collapsing via the parity `compressIter_compl` and the moment closed form
`pairing_compressIter_pathIter_closed` gives the cross pairing purely in `W`-path-densities `x`,
`(1-W)`-path-densities `y`, and `W`-moments `s`:

  `⟨pathIter(compl W) j, pathIter W k⟩ = y_j x_k
      + Σ_{a<j} y_{j-1-a} · (−1)^{a+1} · Σ_{i<k} s_{a+i} x_{k-1-i}`. -/

/-- **Cross path-iterate pairing in moments.** -/
lemma pairing_pathIter_compl_moment (hW : IsGraphon W μ) (j k : ℕ) :
    pairing μ (pathIter (compl W) μ j) (pathIter W μ k)
      = pathDensity (compl W) μ j * pathDensity W μ k
        + ∑ a ∈ Finset.range j,
            pathDensity (compl W) μ (j - 1 - a)
              * ((-1 : ℝ) ^ (a + 1)
                  * ∑ i ∈ Finset.range k, specMoment W μ (a + i) * pathDensity W μ (k - 1 - i)) := by
  show (∫ z, pathIter (compl W) μ j z * pathIter W μ k z ∂μ) = _
  have hexp : ∀ z, pathIter (compl W) μ j z * pathIter W μ k z
      = pathDensity (compl W) μ j * pathIter W μ k z
        + ∑ a ∈ Finset.range j,
            pathDensity (compl W) μ (j - 1 - a)
              * (compressIter (compl W) μ a z * pathIter W μ k z) := by
    intro z
    have hz : pathIter (compl W) μ j z
        = pathDensity (compl W) μ j
          + ∑ a ∈ Finset.range j, pathDensity (compl W) μ (j - 1 - a) * compressIter (compl W) μ a z :=
      congrFun (pathIter_expansion (isGraphon_compl hW) j) z
    rw [hz, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [integral_congr_ae (ae_of_all _ hexp)]
  have hInt1 : Integrable (fun z => pathDensity (compl W) μ j * pathIter W μ k z) μ :=
    (good_pathIter hW k).integrable.const_mul _
  have hInt2 : Integrable (fun z => ∑ a ∈ Finset.range j,
      pathDensity (compl W) μ (j - 1 - a) * (compressIter (compl W) μ a z * pathIter W μ k z)) μ :=
    integrable_finsetSum _ fun a _ =>
      (((good_compressIter (isGraphon_compl hW) a).mul (good_pathIter hW k)).integrable).const_mul _
  rw [integral_add hInt1 hInt2, integral_const_mul,
    integral_finsetSum _ fun a _ =>
      (((good_compressIter (isGraphon_compl hW) a).mul (good_pathIter hW k)).integrable).const_mul _,
    show (∫ z, pathIter W μ k z ∂μ) = pathDensity W μ k from rfl]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul]
  congr 1
  have hparity : pairing μ (compressIter (compl W) μ a) (pathIter W μ k)
      = (-1 : ℝ) ^ (a + 1) * pairing μ (compressIter W μ a) (pathIter W μ k) := by
    show (∫ z, compressIter (compl W) μ a z * pathIter W μ k z ∂μ)
        = (-1 : ℝ) ^ (a + 1) * ∫ z, compressIter W μ a z * pathIter W μ k z ∂μ
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show compressIter (compl W) μ a z * pathIter W μ k z
        = (-1 : ℝ) ^ (a + 1) * (compressIter W μ a z * pathIter W μ k z)
    rw [congrFun (compressIter_compl hW a) z]; ring
  show pairing μ (compressIter (compl W) μ a) (pathIter W μ k) = _
  rw [hparity, pairing_compressIter_pathIter_closed hW k a]

/-- **`neckSum` in path densities and moments.**  Substituting the cross-pairing moment form into
`neckSum_eq`, `neckSum` becomes an explicit operator-free expression in the `W`-path densities `x`,
the `(1-W)`-path densities `y`, and the `W`-moments `s` — the object the `𝓟_{m,r}` positivity
argument works on (still to expand `y` via `pathDensity_succ` at `compl W`, then the positivity). -/
lemma neckSum_moment (hW : IsGraphon W μ) (m : ℕ) :
    neckSum W μ m
      = ∑ j ∈ Finset.range (m - 1),
          (-1 : ℝ) ^ j
            * (pathDensity (compl W) μ j * pathDensity W μ (m - 1 - j)
              + ∑ a ∈ Finset.range j,
                  pathDensity (compl W) μ (j - 1 - a)
                    * ((-1 : ℝ) ^ (a + 1)
                        * ∑ i ∈ Finset.range (m - 1 - j),
                            specMoment W μ (a + i) * pathDensity W μ (m - 1 - j - 1 - i))) := by
  rw [neckSum_eq hW]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairing_pathIter_compl_moment hW j (m - 1 - j)]

end OddCycleBound.HighDensity
