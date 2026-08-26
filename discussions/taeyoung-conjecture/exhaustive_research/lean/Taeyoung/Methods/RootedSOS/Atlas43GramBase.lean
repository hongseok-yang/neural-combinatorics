import Taeyoung.Methods.RootedSOS.Atlas43Data
import Taeyoung.Methods.RootedSOS.Gram

/-!
# Exact Gram-matrix entries for the Atlas 43 certificate

The JSON stores every upper-triangular correction entry in lexicographic
order.  This module gives that data its mathematical type and proves symmetry
by construction.  Kernel checks of diagonal dominance are kept in small,
separately compiled modules.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43Gram

open Taeyoung.Methods.RootedSOS.Atlas43Data

/-- Position of `(i,j)`, with `i ≤ j`, in lexicographic enumeration of the
upper triangle of an `n × n` matrix. -/
def upperIndex (n i j : Nat) : Nat :=
  i * n - i * (i + 1) / 2 + j

private def correctionEntry (_block order offset i j : Nat) : Array Int :=
  corrections[(offset + upperIndex order (min i j) (max i j))]?.getD #[]

/-- A rational correction entry, reflected across the diagonal.  Invalid or
zero-denominator input maps to zero and is subsequently rejected by the
certificate checks. -/
def correctionValue (block order offset i j : Nat) : ℚ :=
  let entry := correctionEntry block order offset i j
  Rat.ofInt (entry[3]?.getD 0) / Rat.ofInt (entry[4]?.getD 0)

def C₀ (i j : Fin 107) : ℚ := correctionValue 0 107 0 i j
def C₁ (i j : Fin 48) : ℚ := correctionValue 1 48 5778 i j

theorem C₀_symm (i j : Fin 107) : C₀ i j = C₀ j i := by
  simp [C₀, correctionValue, correctionEntry, Nat.min_comm, Nat.max_comm]

theorem C₁_symm (i j : Fin 48) : C₁ i j = C₁ j i := by
  simp [C₁, correctionValue, correctionEntry, Nat.min_comm, Nat.max_comm]

end Taeyoung.Methods.RootedSOS.Atlas43Gram
