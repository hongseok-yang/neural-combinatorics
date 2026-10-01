import TreeApex.Appendix.Sidorenko

/-!
# The plan's declaration names (TREES_VERIFICATION_PLAN.md §6)

The audit list of plan §6 names some results at the top level of `TreeApex`, where the development
places them in the namespaces of the structures they are about (`ProbHost` for host statements,
`SymLaw` for the generic tree extension) or states them for a host on any finite type.  This file
restates each such result under the plan's name, so that `CheckAxiomsTree.lean` can audit exactly
the §6 list.  Each restatement is a one-line application of the development's theorem.

Every paper label has a Lean declaration of the same meaning; the correspondence is the
per-statement table of `TREES_DASHBOARD.md`.
-/

open Finset SimpleGraph

namespace TreeApex

open EvenCycleApex

variable {V : Type*} [Fintype V]

/-- §6 `hostDensity_apexGraph_treeGraph`: the weights of `T^{+k}` on a host `Fin d`
(the even-cycle library's `hostDensity`). -/
theorem hostDensity_apexGraph_treeGraph {d : ℕ} (w : Fin d → ℝ) (M : Fin d → Fin d → ℝ)
    (par : ℕ → ℕ) (m k : ℕ) :
    hostDensity w (apexGraph (treeGraph par m) k) M
      = ∑ s : Fin k → Fin d, ∑ x : Fin (m + 1) → Fin d, (∏ i, w (s i)) *
          (∏ u, (w (x u) * ∏ i, M (x u) (s i))) * ∏ i : Fin m, M (x (parV par i)) (x i.succ) :=
  hostDens_apexGraph_treeGraph w M par m k

/-- §6 `hostDensity_double_of_connected` (`eq:connected-blocks`, host form). -/
theorem hostDensity_double_of_connected (K : ProbHost V) {v : ℕ} (F : SimpleGraph (Fin v))
    [DecidableRel F.Adj] (hF : F.Connected) :
    hostDens K.double.w F K.double.M = K.Mh F / 2 ^ v :=
  K.hostDens_double_of_connected F hF

/-- §6 `host_goodman_identity` (`lem:goodman` on hosts). -/
theorem host_goodman_identity (K : ProbHost V) :
    K.Mh (⊤ : SimpleGraph (Fin 3)) = 3 / 2 * K.Mh (pathGraph 3) - 1 / 2 :=
  K.host_goodman_identity

/-- §6 `host_half_le_sigma` (`lem:goodman` on hosts). -/
theorem host_half_le_sigma (K : ProbHost V) : 1 / 2 ≤ K.Mh (pathGraph 3) :=
  K.host_half_le_sigma

/-- §6 `h_ge` (**T1**, `eq:triangle-bounds`). -/
theorem h_ge (K : ProbHost V) (hR : 0 < K.R) : Real.log K.R - Real.log K.E ≤ K.h :=
  K.h_ge hR

/-- §6 `I_le` (**T2**, `eq:triangle-bounds`; `I = A − 2h`). -/
theorem I_le (K : ProbHost V) (hR : 0 < K.R) : K.A - 2 * K.h ≤ Real.log K.D - Real.log K.R :=
  K.I_le hR

/-- §6 `relEnt_book` (**B1**, `eq:book-entropy`, `k = j + 1`). -/
theorem relEnt_book (K : ProbHost V) (j : ℕ) (hR : 0 < K.R) :
    relEnt (K.bookRef j hR).bookWeight
        (fun q : (Fin (j + 1) → V) × V × V => (K.bookLaw j hR).Q q.1 q.2.1 q.2.2)
      = Real.log K.R + j * K.h :=
  K.relEnt_book j hR

/-- §6 `g_ge` (**B2**, `eq:book-extension`, `k = j + 1`). -/
theorem g_ge (K : ProbHost V) (j : ℕ) (hR : 0 < K.R) :
    (j + 1) * Real.log K.R - Real.log K.E - j * Real.log K.D
      ≤ (K.bookLaw j hR).condRelEnt (K.bookRef j hR) :=
  K.g_ge j hR

/-- §6 `relEnt_treeLaw` (**TE4**, `eq:tree-entropy`), for any symmetric finite law. -/
theorem relEnt_treeLaw {S X : Type*} [Fintype S] [Fintype X] (L : SymLaw S X) (R : RefFactors L)
    (par : ℕ → ℕ) (m : ℕ) :
    relEnt (R.treeWeight par (m + 1)) (L.treeLaw par (m + 1))
      = relEnt R.bookWeight (fun q : S × X × X => L.Q q.1 q.2.1 q.2.2) + m * L.condRelEnt R :=
  L.relEnt_treeLaw R par m

/-- §6 `finite_counting_inequality` (`thm:finite`, weighted; tree on `n = m + 1` vertices). -/
theorem finite_counting_inequality (K : ProbHost V) (par : ℕ → ℕ) {m k : ℕ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) :
    K.R ^ (k * m)
      ≤ hostDens K.w (apexGraph (treeGraph par m) k) K.M * K.E ^ (m + k - 2)
          * K.D ^ ((k - 1) * (m - 1)) :=
  K.finite_counting_inequality par hm hk

/-- §6 `host_two_colour_polynomial` (`eq:two-color-polynomial` on hosts; `n = m + 2`,
`k = j + 1`). -/
theorem host_two_colour_polynomial (K : ProbHost V) (par : ℕ → ℕ) (m j : ℕ) :
    K.Mh (⊤ : SimpleGraph (Fin 3)) ^ ((j + 1) * (m + 1))
      ≤ K.Mh (apexGraph (treeGraph par (m + 1)) (j + 1)) * K.Mh (pathGraph 3) ^ (j * m) :=
  K.host_two_colour_polynomial par m j

/-- §6 `commonness_scalar` (the display in the proof of `thm:common`). -/
theorem commonness_scalar {σ τ x : ℝ} (m j : ℕ) (hσ : 1 / 2 ≤ σ) (hτ : τ = 3 / 2 * σ - 1 / 2)
    (h : τ ^ ((j + 1) * (m + 1)) ≤ x * σ ^ (j * m)) : 4 / 2 ^ ((j + 2) * (m + 2)) ≤ x :=
  ProbHost.commonness_scalar m j hσ hτ h

/-- §6 `host_commonness` (`thm:common` on hosts, `n = m + 2`, `k = j + 1`). -/
theorem host_commonness (K : ProbHost V) (par : ℕ → ℕ) (m j : ℕ) :
    4 / 2 ^ ((j + 2) * (m + 2)) ≤ K.Mh (apexGraph (treeGraph par (m + 1)) (j + 1)) :=
  K.host_commonness par m j

/-- §6 `host_star_commonness` (the star case of `thm:common` on hosts, `k = j + 1`). -/
theorem host_star_commonness (K : ProbHost V) (par : ℕ → ℕ) (j : ℕ) :
    4 / 2 ^ ((j + 2) * 1) ≤ K.Mh (apexGraph (treeGraph par 0) (j + 1)) :=
  K.host_star_commonness par j

end TreeApex
