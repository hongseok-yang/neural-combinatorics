import ApicesCommonness

/-! Import check: the shared part `Common` imports nothing from `Trees` or `Cycles`, and `Trees`
and `Cycles` import nothing from each other.  Prints the number of modules in each part. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let common := `ApicesCommonness.Common
  let parts := [common, `ApicesCommonness.Trees, `ApicesCommonness.Cycles]
  let partOf (m : Name) : Option Name := parts.find? (·.isPrefixOf m)
  let mut bad : Array (Name × Name) := #[]
  for (m, d) in env.header.moduleNames.zip env.header.moduleData do
    if let some p := partOf m then
      for i in d.imports do
        if let some q := partOf i.module then
          unless q == p || q == common do
            bad := bad.push (m, i.module)
  for p in parts do
    let n := (env.header.moduleNames.filter fun m => p.isPrefixOf m).size
    IO.println s!"{p}: {n} modules"
  if bad.isEmpty then
    IO.println "imports OK: Common imports neither Trees nor Cycles; Trees and Cycles are independent"
  else
    throwError s!"forbidden imports: {bad.toList}"
