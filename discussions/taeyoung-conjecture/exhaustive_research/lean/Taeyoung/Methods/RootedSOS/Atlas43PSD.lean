import Taeyoung.Methods.RootedSOS.Atlas43Gram

/-!
# Positive semidefiniteness of the Atlas 43 certificate matrices

The certificate stores integer factors `F₀` and `F₁`; its common scale is
handled by the coefficient identity.  Here we only need the integer factors,
since multiplication by the positive common scale does not affect
nonnegativity.  Safe array lookup deliberately returns zero on malformed
input; the later coefficient checks reject any such malformed certificate.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43PSD

open Taeyoung.Methods.RootedSOS
open Taeyoung.Methods.RootedSOS.Atlas43Data
open Taeyoung.Methods.RootedSOS.Atlas43Gram

def F₀Int (a : Fin 128) (i : Fin 107) : ℤ :=
  (factors0[a.1]?.getD #[])[i.1]?.getD 0

def F₁Int (a : Fin 64) (i : Fin 48) : ℤ :=
  (factors1[a.1]?.getD #[])[i.1]?.getD 0

noncomputable def F₀ (a : Fin 128) (i : Fin 107) : ℝ := F₀Int a i

noncomputable def F₁ (a : Fin 64) (i : Fin 48) : ℝ := F₁Int a i

theorem gram₀_nonneg (v : Fin 128 → ℝ) :
    0 ≤ factoredRatGramForm F₀ C₀ v :=
  factoredRatGramForm_nonneg F₀ C₀ C₀_symm C₀_row_dominant v

theorem gram₁_nonneg (v : Fin 64 → ℝ) :
    0 ≤ factoredRatGramForm F₁ C₁ v :=
  factoredRatGramForm_nonneg F₁ C₁ C₁_symm C₁_row_dominant v

end Taeyoung.Methods.RootedSOS.Atlas43PSD
