import EvenCycleApex.Certificate.Checks.Pos

/-!
# The three universal graph inequalities

Blueprint `thm:certificate-inequalities` for the three targets on the proof path (`P_mean,2` is
excluded by plan D10): on every finite host — weights `w ≥ 0` of total mass one and a symmetric
kernel `|U| ≤ 1`, with no condition on the sign of `∑ w U` — the three graph polynomials of
`def:certificate-targets`, built in `Targets.lean` from their literal edge sets, evaluate to
nonnegative numbers.

The proof is `cert_sound` (M6) applied to the certificates checked by the kernel in
`Checks/{Witness,MeanThree,Neg,Pos}.lean` (`decide +kernel` throughout).
-/

namespace EvenCycleApex

/-- **`thm:certificate-inequalities`** (`P_mean,3`, `P₋`, `P₊`). -/
theorem three_universal_graph_inequalities {d : ℕ} (K : FiniteKernel d) :
    0 ≤ evalPoly K targetMeanThree ∧ 0 ≤ evalPoly K targetNeg ∧ 0 ≤ evalPoly K targetPos :=
  ⟨Checks.meanThree_nonneg K, Checks.negMajority_nonneg K, Checks.posMajority_nonneg K⟩

end EvenCycleApex
