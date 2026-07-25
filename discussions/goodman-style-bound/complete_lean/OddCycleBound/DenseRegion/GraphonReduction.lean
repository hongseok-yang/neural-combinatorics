/-
# High-density theorem — the graphon reduction to `Φ_m ≥ 0` (M0c, direct route)

This is the **graphon** step that the finite-rank `two_sided_identity` (`BlockPower.lean`) was
validating.  It turns the two-sided cyclic-trace identity into a statement about the *actual graphon*
cycle density `cycleDensity = t(C_m, ·)`, with **no** finite-rank approximation and **no** `L²` limit
(the plan's M0c, done directly instead of via the matrix bridge).

The graphon two-sided identity is already available as `complTrace_necklace` in `Necklace.lean`.
Applied to the complement `compl W = 1 − W` (itself a graphon, `isGraphon_compl`), for **odd** `m` the
sign `(−1)^{m-1} = 1`, so

  `t(C_m, W) = neckSum W μ m + ( x_{m-1} − t(C_m, compl W) )`,     `x_{m-1} = pathDensity (compl W) (m-1)`

where `neckSum` is the necklace pairing sum.  The edge-deletion bound `edge_deletion_general`,
`t(C_m, compl W) ≤ x_{m-1}`, then cancels the path-density term **exactly**, giving the clean

  `t(C_m, W) ≥ neckSum W μ m`.

Consequently the full target `t(C_m,W) ≥ p^m − p(1−p)^{m-1}` (odd `m`, any density) reduces to the
single inequality `neckSum W μ m ≥ p^m − p(1−p)^{m-1}` — the graphon incarnation of `Φ_m ≥ 0`, the
analytic crux to be discharged in milestones M1–M7.
-/

import OddCycleBound.Necklace

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-- The **necklace sum** `Ñ_m = Σ_{j=0}^{m-2} (−1)ʲ ⟨pathIterⱼ(1−W), complIter_{m-1-j}(1−W)⟩`.

This is the right-hand side of the two-sided identity `complTrace_necklace` applied to `compl W`,
with the path-density term stripped (it cancels against edge-deletion).  Proving
`neckSum W μ m ≥ p^m − p(1−p)^{m-1}` (odd `m`, `p = edgeDensity W μ`) is exactly `Φ_m ≥ 0`. -/
noncomputable def neckSum (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m - 1),
    (-1 : ℝ) ^ j * pairing μ (pathIter (compl W) μ j) (complIter (compl W) μ (m - 1 - j))

/-- **The graphon reduction.**  For every odd `m ≥ 3` and every graphon `W`,
`t(C_m, W) = cycleDensity μ W m ≥ neckSum W μ m`.

Proof: `complTrace_necklace` at `compl W` (a graphon by `isGraphon_compl`) with `(−1)^{m-1}=1`
(`m` odd) gives `t(C_m,W) = neckSum + (x_{m-1} − t(C_m, compl W))`; `edge_deletion_general` gives
`t(C_m, compl W) ≤ x_{m-1}`, so the parenthesised term is `≥ 0`.  No approximation, no limit. -/
theorem cycle_ge_neckSum (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    neckSum W μ m ≤ cycleDensity μ W m := by
  have hV : IsGraphon (compl W) μ := isGraphon_compl hW
  have hcc : compl (compl W) = W := by funext x y; simp only [compl]; ring
  have hn : m - 2 + 1 = m - 1 := by omega
  have hev : Even (m - 1) := by rcases hm with ⟨k, hk⟩; exact ⟨k, by omega⟩
  -- The two-sided identity at `compl W`, specialised to odd `m` (`(−1)^{m-1} = 1`).
  have key := complTrace_necklace hV (m - 2)
  rw [hn, hcc, hev.neg_one_pow, one_mul] at key
  -- Package it with folded `neckSum` / `cycleDensity` (all steps hold by `rfl`/defeq).
  have hid : cycleDensity μ W m
      = neckSum W μ m + (pathDensity (compl W) μ (m - 1) - cycleDensity μ (compl W) m) := key
  -- Edge deletion for the complement cancels the path-density term.
  have hdel := edge_deletion_general hV (m - 2)
  rw [show m - 2 + 2 = m from by omega, hn] at hdel
  linarith [hid, hdel]

/-- **The high-density target, reduced to `Φ_m ≥ 0`.**  Once the necklace-sum positivity
`p^m − p(1−p)^{m-1} ≤ neckSum W μ m` (the analytic crux, milestones M1–M7) is available, the graphon
odd-cycle lower bound `t(C_m, W) ≥ p^m − p(1−p)^{m-1}` follows for every odd `m ≥ 3` at any density. -/
theorem cycle_bound_of_neckSum (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hpos : edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)
              ≤ neckSum W μ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)
      ≤ cycleDensity μ W m :=
  hpos.trans (cycle_ge_neckSum hW hm hm3)

end OddCycleBound.DenseRegion
