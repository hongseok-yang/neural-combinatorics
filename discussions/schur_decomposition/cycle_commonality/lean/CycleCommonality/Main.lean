import CycleCommonality.Extremal

/-!
# The exact commonality region, for step graphons

Theorem `thm:main` of `adjacent_cycle_commonality.tex`, in the finite model.

For `n = 2k ≥ 4` even, `α*_n ∈ (1/2, 1)` is the unique solution of `ρ_n(α*) = 2^{1-n}`
(`exists_critical`, `rho_strictMonoOn`), and the scaled commonality inequality
`eq:scaled-target`

```
  t(C_n, W) + κ_n(a) t(C_{n+1}, 1-W) ≥ ρ_n(a)
```

holds for **every** step graphon exactly when `a ≤ α*_n`:

* `≤` is `StepGraphon.lower_bound` (§6, resting on Corollary `cor:rank-one-trace` and Lemma
  `lem:kappa-bounds`);
* `>` fails at the balanced two-clique (`twoClique.violates`, §7).

What is **not** covered here is Lemma `lem:step-reduction`, the passage from step graphons to
arbitrary graphons, and Lemma `lem:trace-density`, the identification of `Tr (T ^ r)` with the
integral homomorphism density.  Both are the subject of `Analytic/`; in this file the cycle
densities *are* the traces.  See `DEVIATIONS.md`.
-/

namespace CycleCommonality

/-- **Theorem `thm:main` for step graphons.**  The scaled commonality inequality holds for every
weighted step graphon if and only if `a` does not exceed the critical point `c = α*_n`. -/
theorem commonality_iff {n : ℕ} (hne : Even n) (hn4 : 4 ≤ n) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1) (hcrit : rho n c = twoCliqueValue n)
    (ha0 : 0 < a) :
    (∀ (N : ℕ), 0 < N → ∀ G : StepGraphon N,
        rho n a ≤ G.densityCompl n + kappa n a * G.density (n + 1))
      ↔ a ≤ c := by
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have hviol := twoClique.violates hne hn4 (by linarith : (0 : ℝ) ≤ c) hcrit hcon
    have := h 2 (by norm_num) twoClique
    linarith
  · intro hac N hN G
    exact G.lower_bound hN hne hn4 hc hc1 hcrit ha0 hac

/-- The critical point exists and is unique in `(1/2, 1)`. -/
theorem exists_unique_critical {n : ℕ} (hn4 : 4 ≤ n) :
    ∃! c : ℝ, (1 / 2 < c ∧ c < 1) ∧ rho n c = twoCliqueValue n := by
  obtain ⟨c, hc, hc1, hcrit⟩ := exists_critical (by omega : 2 ≤ n)
  refine ⟨c, ⟨⟨hc, hc1⟩, hcrit⟩, ?_⟩
  rintro d ⟨⟨hd, hd1⟩, hdcrit⟩
  by_contra hne
  have hmono := rho_strictMonoOn (by omega : 2 ≤ n)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hmono (by linarith : (0:ℝ) ≤ d) (by linarith : (0:ℝ) ≤ c) hlt
    rw [hdcrit, hcrit] at this
    exact lt_irrefl _ this
  · have := hmono (by linarith : (0:ℝ) ≤ c) (by linarith : (0:ℝ) ≤ d) hlt
    rw [hdcrit, hcrit] at this
    exact lt_irrefl _ this

end CycleCommonality
