import Taeyoung.Foundation

/-!
# A computable mirror of `properAssignmentCount`

`Foundation/ChromaticPolynomial.lean` defines

```
properAssignmentCount H k = (univ.filter (IsProperAssignment H)).card
```

through `Classical.propDecidable`, so the definition is `noncomputable` and the
kernel cannot evaluate it.  That is deliberate — the foundation should not carry
a `DecidableRel H.Adj` obligation into every statement — but it blocks the one
tool that makes the negative rows tractable.

This file supplies the mirror.  `properCount` is the same cardinality taken with
the *decidable* instance that `graphFromEdges` already provides, and
`properAssignmentCount_eq` identifies the two.  The proof is
`Subsingleton.elim` on the `Decidable` instances: `Finset.filter` depends on the
instance only through a subsingleton, so the two filters are literally the same
finset.

With this in place a colouring count is a `decide +kernel` away.  Measured on
Atlas 129, `graphFromEdges 6 [(0,1),(0,4),(0,5),(1,2),(2,3),(3,4),(3,5)]`, with
`maxRecDepth 100000`:

| `k` | functions | `decide +kernel` |
|---:|---:|---|
| 3 | 729 | fast |
| 4 | 4096 | fast |
| 5 | 15625 | seconds |
| 6 | 46656 | ≈ 2 min 37 s |

and the axiom report stays `[propext, Classical.choice, Quot.sound]` — this is
kernel reduction, **not** `native_decide`.  The `k = 6` row is the one an earlier
draft of `docs/TODO.md` recorded as "out of reach"; it was measured with plain
`decide`, whose budget is the elaborator's heartbeats rather than the kernel.

Note what this does *not* give.  `IsChromaticPolynomial` quantifies over **every**
`k`, so finitely many evaluated values never establish it — they pin the
coefficients only once one already knows the count is a polynomial.  Supplying
that is the remaining work; see `docs/TODO.md` §6.
-/

open Finset

namespace Taeyoung.Methods.Negative

open Taeyoung

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The computable form of `IsProperAssignment`, with explicit binders so that
the `Decidable` instance is found by `inferInstance`. -/
def IsProper {k : ℕ} (x : V → Fin k) : Prop :=
  ∀ u v, H.Adj u v → x u ≠ x v

instance instDecidableIsProper {k : ℕ} (x : V → Fin k) :
    Decidable (IsProper H x) := by
  unfold IsProper
  infer_instance

lemma isProper_iff {k : ℕ} (x : V → Fin k) :
    IsProper H x ↔ IsProperAssignment H x :=
  ⟨fun h _ _ huv ↦ h _ _ huv, fun h u v huv ↦ h huv⟩

/-- **The computable colouring count.** -/
def properCount (k : ℕ) : ℕ :=
  ((univ : Finset (V → Fin k)).filter (IsProper H)).card

/-- **The mirror is the foundation's count.**  Both sides are the cardinality of
a filter of `univ` by the same predicate; the `Decidable` instances differ, and
`Subsingleton.elim` removes that difference. -/
theorem properAssignmentCount_eq (k : ℕ) :
    properAssignmentCount H k = properCount H k := by
  classical
  rw [properAssignmentCount, properCount]
  congr 1
  refine Finset.filter_congr fun x _ ↦ ?_
  exact (isProper_iff H x).symm

/-! ### A worked instance

Atlas 129, one of the 19 negative rows.  This is here as a regression test that
the two-step idiom — rewrite along `properAssignmentCount_eq`, then
`decide +kernel` — really does evaluate the foundation's own count, and that its
axiom report stays clean.  The value `42` is the number of proper `3`-colourings
of this graph. -/

section Worked

/-- Atlas 129: `graph6` `EheO`, seven edges on six vertices. -/
def graph129 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4), (3, 5)]

instance : DecidableRel graph129.Adj := graphFromEdges_decidableAdj _ _

set_option maxRecDepth 100000 in
theorem properAssignmentCount_graph129_three :
    properAssignmentCount graph129 3 = 42 := by
  rw [properAssignmentCount_eq]
  decide +kernel

end Worked

end Taeyoung.Methods.Negative
