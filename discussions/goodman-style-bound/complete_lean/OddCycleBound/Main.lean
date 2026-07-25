/-
# `Main.lean` — the odd-cycle Goodman bound, assembled by regime (paper §10, `thm:main`)

Target (`odd_cycle_bound`): for every graphon `W` with edge density `p` and every odd `m ≥ 3`,

```
cycleDensity μ W m  ≥  p^m − p(1−p)^{m−1}.
```

The proof splits into regimes, and **all of them are now formalized sorry-free**.  The dense regime
`p ≥ 2/3` (paper §4) has its analytic endgame (beta formula → gamma smoothing → gamma moment
inequality `H(b_*) > 0` via `L(t) < 0`) in `DenseRegion/Diagonal/`; the intermediate regime
`1/2 < p < 2/3` (paper §5–§9) is the operator/scalar envelope argument assembled in
`IntermediateRegion/IntermediateAssembly.lean`:

* `dense_cycle_bound`        — `p ≥ 2/3`, all odd `m ≥ 3`.  **PROVEN** (Phase D).
* `intermediate_cycle_bound` — `p < 2/3`, odd `m ≥ 11`.  **PROVEN** (Phase R, paper §5–§9).
* `small_cycle_bound`        — odd `3 ≤ m ≤ 9`, all `p`.  **PROVEN** (short-cycle SOS + `m=9` corner).
* `fisher_triangle_bound`    — Fisher/Razborov–Reiher triangle-density bound.  **PROVEN**; it is the
  external `TriangleDensityLowerBoundUpTo (2/3)` interface that the archived conditional
  intermediate-region route consumes (unconditionality insurance for Phase R).
* `odd_cycle_bound`          — the complete theorem, assembled from the three cycle regimes.

`Main.lean` is a leaf: nothing imports it except (eventually) the axiom-audit `CheckComplete.lean`.
-/
import OddCycleBound.DenseRegion.Diagonal.DenseRegionEndgame
import OddCycleBound.Fisher.GraphonBridge
import OddCycleBound.ShortCycles
import OddCycleBound.IntermediateRegion.IntermediateAssembly

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/-- **(1) Dense regime `p ≥ 2/3`** (paper §4, `thm:dense-region`).  **Proven sorry-free**: this is
the fully unconditional dense-region bound, the analytic heart of the whole proof (Phase D). -/
theorem dense_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ)
    (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) :=
  DenseRegion.dense_region_cycle_bound_unconditional hW hp hm hm3

/-- **(2) Intermediate regime `p < 2/3`** for odd `m ≥ 11` (paper §5–§9, Phase R).
Internally: `p ≤ 1/2` is trivial (`RHS ≤ 0 ≤ cycleDensity`), and `1/2 < p < 2/3` is the
operator/scalar envelope argument (`intermediateRegion_odd_cycle_bound`).  **Proven sorry-free.** -/
theorem intermediate_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hm : Odd m) (hm11 : 11 ≤ m)
    (hp : edgeDensity W μ < 2 / 3) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  by_cases hp2 : edgeDensity W μ ≤ 1 / 2
  · -- `p ≤ 1/2`: the RHS is `≤ 0`, and cycle densities are nonnegative.
    have hp0 : 0 ≤ edgeDensity W μ := edgeDensity_nonneg hW
    have hple : edgeDensity W μ ≤ 1 - edgeDensity W μ := by linarith
    have hpow : edgeDensity W μ ^ (m - 1) ≤ (1 - edgeDensity W μ) ^ (m - 1) :=
      pow_le_pow_left₀ hp0 hple (m - 1)
    have hmul := mul_le_mul_of_nonneg_left hpow hp0
    have hsplit : edgeDensity W μ ^ m = edgeDensity W μ * edgeDensity W μ ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ']
    have hnonneg : (0 : ℝ) ≤ cycleDensity μ W m := trace_compPow_nonneg hW (m - 1)
    nlinarith [hmul, hnonneg, hsplit]
  · -- `1/2 < p < 2/3`: the operator/scalar envelope argument (Phase R).
    have hp1 : (1 : ℝ) / 2 < edgeDensity W μ := not_le.mp hp2
    have hm9 : 9 ≤ m := by omega
    exact IntermediateRegion.intermediateRegion_odd_cycle_bound hW hm hm9 hp1 hp

/-- **(3) Small odd cycles `3 ≤ m ≤ 9`**, all `p` (paper §2 short cycles + the `m = 9` corner).
`m = 3, 5, 7` are the Goodman/sum-of-squares short-cycle bounds (`ShortCycles.lean`, from the
complement necklace + degree-2 SOS certificate); `m = 9` is the intermediate region's boundary case.

Dispatch (`m = 2k+1`, `1 ≤ k ≤ 4`): `m = 3, 5, 7` are the three short-cycle bounds; `m = 9` splits on
`p`:  `p ≥ 2/3` reuses the unconditional dense-region bound; `p ≤ 1/2` is trivial
(`RHS ≤ 0 ≤ cycleDensity`); the single corner `m = 9 ∧ 1/2 < p < 2/3` is discharged by the
intermediate-region bound (`intermediateRegion_odd_cycle_bound`).  **Proven sorry-free.** -/
theorem small_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hm : Odd m) (hm3 : 3 ≤ m) (hm9 : m ≤ 9) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := hm
  have hk1 : 1 ≤ k := by omega
  have hk4 : k ≤ 4 := by omega
  interval_cases k
  · exact cycleDensity_three_bound hW
  · exact cycleDensity_five_bound hW
  · exact cycleDensity_seven_bound hW
  · -- `m = 9`: split on the edge density `p`.
    show cycleDensity μ W 9 ≥ edgeDensity W μ ^ 9 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 8
    by_cases hp : 2 / 3 ≤ edgeDensity W μ
    · -- Dense regime: the unconditional dense-region bound applies to every odd `m ≥ 3`.
      exact dense_cycle_bound hW hp ⟨4, rfl⟩ (by norm_num)
    · by_cases hp2 : edgeDensity W μ ≤ 1 / 2
      · -- `p ≤ 1/2`: the RHS is `≤ 0`, and cycle densities are nonnegative.
        have hnonneg : 0 ≤ cycleDensity μ W 9 := trace_compPow_nonneg hW 8
        linarith [rhs9_nonpos_of_le_half hW hp2, hnonneg]
      · -- The remaining corner `1/2 < p < 2/3` at `m = 9` (boundary case of Phase R, paper §5–§9).
        exact IntermediateRegion.intermediateRegion_odd_cycle_bound hW ⟨4, by norm_num⟩
          (by norm_num) (not_le.mp hp2) (not_le.mp hp)

/-- **(4) Fisher's triangle-density lower bound** (Razborov–Reiher).  For a graphon `W` with
`1/2 < p ≤ 2/3` (`p = edgeDensity W μ`), the triangle density `cycleDensity μ W 3` is at least
`(3/2)·c·(1−c)²`, where `c = (1 − √(4 − 6p))/3`.  **Proven sorry-free** in `Fisher/`; this is not an
odd-cycle regime but the external interface the archived conditional intermediate-region route
consumes (unconditionality insurance for Phase R), restated here directly in terms of
`cycleDensity`/`edgeDensity` so the statement is self-contained. -/
theorem fisher_triangle_bound (hW : IsGraphon W μ)
    (hp1 : 1 / 2 < edgeDensity W μ) (hp2 : edgeDensity W μ ≤ 2 / 3) :
    let c := (1 - Real.sqrt (4 - 6 * edgeDensity W μ)) / 3
    (3 / 2) * c * (1 - c) ^ 2 ≤ cycleDensity μ W 3 :=
  triangleDensityLowerBound_twoThirds hW hp1 hp2

/-- **(5) The odd-cycle Goodman bound** (paper §10, `thm:main`): for every graphon `W` and every odd
`m ≥ 3`, `cycleDensity μ W m ≥ p^m − p(1−p)^{m−1}`.  Assembled from the three cycle regimes:
`m ≤ 9` → `small_cycle_bound`; else `p ≥ 2/3` → `dense_cycle_bound`, `p < 2/3` →
`intermediate_cycle_bound`. -/
theorem odd_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  by_cases hm9 : m ≤ 9
  · exact small_cycle_bound hW hm hm3 hm9
  · have hm11 : 11 ≤ m := by rcases hm with ⟨k, rfl⟩; omega
    by_cases hp : 2 / 3 ≤ edgeDensity W μ
    · exact dense_cycle_bound hW hp hm hm3
    · exact intermediate_cycle_bound hW hm hm11 (not_le.mp hp)

end OddCycleBound
