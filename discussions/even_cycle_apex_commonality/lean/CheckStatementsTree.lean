import TreeApex

/-! The elaborated headline statements (T7 gate: compare with TREES_VERIFICATION_PLAN.md T-D5). -/

#check @TreeApex.tree_apex_one_colour
#check @TreeApex.tree_apex_two_colour_polynomial
#check @TreeApex.half_le_commonalityM_path
#check @TreeApex.goodman_identity
#check @TreeApex.tree_apex_two_colour
#check @TreeApex.tree_apex_common
#check @TreeApex.tree_apex_one_colour'
#check @TreeApex.tree_apex_two_colour_polynomial'
#print TreeApex.apexGraph

/-! The T-D5 statements, copied verbatim from the plan, each closed by the corresponding theorem. -/

section StatementLock

open EvenCycleApex Foundation SimpleGraph MeasureTheory TreeApex

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Ω → Ω → ℝ} {n k : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj]

example (hW : IsGraphon W μ) (hT : T.IsTree) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
      ≤ homDensity (apexGraph T k) W μ
          * homDensity (⊤ : SimpleGraph (Fin 2)) W μ ^ (n + k - 3)
          * homDensity (pathGraph 3) W μ ^ ((k - 1) * (n - 2)) :=
  tree_apex_one_colour T hW hT hn hk

example (hW : IsGraphon W μ) (hT : T.IsTree) (hn : 2 ≤ n)
    (hk : 1 ≤ k) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
      ≤ commonalityM (apexGraph T k) W μ * commonalityM (pathGraph 3) W μ ^ ((k - 1) * (n - 2)) :=
  tree_apex_two_colour_polynomial T hW hT hn hk

example (hW : IsGraphon W μ) :
    1 / 2 ≤ commonalityM (pathGraph 3) W μ :=
  half_le_commonalityM_path hW

example (hW : IsGraphon W μ) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ = 3 / 2 * commonalityM (pathGraph 3) W μ - 1 / 2 :=
  goodman_identity hW

example (hW : IsGraphon W μ) (hT : T.IsTree) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    commonalityM (⊤ : SimpleGraph (Fin 3)) W μ ^ (k * (n - 1))
        / commonalityM (pathGraph 3) W μ ^ ((k - 1) * (n - 2))
      ≤ commonalityM (apexGraph T k) W μ :=
  tree_apex_two_colour T hW hT hn hk

example (hW : IsGraphon W μ) (hT : T.IsTree) (hk : 1 ≤ k) :
    4 / 2 ^ ((k + 1) * n) ≤ homDensity (apexGraph T k) W μ + homDensity (apexGraph T k) (cmpl W) μ :=
  tree_apex_common T hW hT hk

/-- `4 / 2^((k+1)n)` is `2^{1 − e(T^{+k})}`: the edge count is `(k+1)n − 1`. -/
example (hT : T.IsTree) : (edgePairs (apexGraph T k)).card = (k + 1) * n - 1 :=
  apexGraph_edgeCount T hT

end StatementLock
