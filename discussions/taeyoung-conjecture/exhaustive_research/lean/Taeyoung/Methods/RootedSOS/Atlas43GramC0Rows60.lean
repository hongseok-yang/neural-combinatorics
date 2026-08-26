import Taeyoung.Methods.RootedSOS.Atlas43GramBase
import Mathlib.Tactic.FinCases

open Finset
namespace Taeyoung.Methods.RootedSOS.Atlas43Gram

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem C₀_rows_60 (i : Fin 10) :
    ∑ j, abs (C₀ (⟨60 + i.1, by omega⟩ : Fin 107) j) ≤ 1 := by
  fin_cases i <;> decide +kernel

end Taeyoung.Methods.RootedSOS.Atlas43Gram
