import TreeApex

/-! Import-closure check for the tree development (TREES_VERIFICATION_PLAN.md, T-D7).

Lists the `EvenCycleApex` modules in the import closure of `TreeApex` and fails if any of them is
heavy (`Conditional`, `Moments`, `Finite`, `Certificate`, `Transfer`, `Main`, `Equality`). -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames.filter fun m => (`EvenCycleApex).isPrefixOf m
  let heavy := [`EvenCycleApex.Conditional, `EvenCycleApex.Moments, `EvenCycleApex.Finite,
    `EvenCycleApex.Certificate, `EvenCycleApex.Transfer, `EvenCycleApex.Main,
    `EvenCycleApex.Equality]
  let bad := mods.filter fun m => heavy.any fun h => h.isPrefixOf m
  IO.println s!"EvenCycleApex modules in the closure of TreeApex ({mods.size}):"
  for m in mods.qsort (·.toString < ·.toString) do
    IO.println s!"  {m}"
  if bad.isEmpty then
    IO.println "import closure OK: no heavy EvenCycleApex module"
  else
    throwError m!"heavy modules in the closure: {bad.toList}"
