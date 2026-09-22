import Taeyoung.Methods.RootedSOS.CompactS4.Young211Rows00
import Taeyoung.Methods.RootedSOS.CompactS4.Young211Rows13
import Taeyoung.Methods.RootedSOS.CompactS4.Young211Rows26
import Taeyoung.Methods.RootedSOS.SparseFlagCoefficients

namespace Taeyoung.Methods.RootedSOS.CompactS4.Young211

theorem code_identity (i j : Fin 30) : codeIdentity i j := by
  by_cases h : i.1 < 13
  · let k : Fin 13 := ⟨i.1-0, by omega⟩
    have hi : (⟨0+k.1, by omega⟩ : Fin 30) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [hi] using code_rows_00 k j
  by_cases h : i.1 < 26
  · let k : Fin 13 := ⟨i.1-13, by omega⟩
    have hi : (⟨13+k.1, by omega⟩ : Fin 30) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [hi] using code_rows_13 k j
  by_cases h : i.1 < 30
  · let k : Fin 4 := ⟨i.1-26, by omega⟩
    have hi : (⟨26+k.1, by omega⟩ : Fin 30) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa only [hi] using code_rows_26 k j
  omega

theorem pulled_exact (g : Fin 143) (i j : Fin 30) :
    pulled g i j = groupCoefficient i j g := pulled_exact_of_code i j (code_identity i j) g

theorem pair_basis_density
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (i j : Fin 30) (W : Taeyoung.Graphon Ω μ) :
    (∑ a : Fin 352, ∑ b : Fin 352, (TInt a i : Real) * (TInt b j : Real) *
      Taeyoung.homDensity (S4Flags.gluedGraph a b) W) =
      ∑ g : Fin 143, (pulled g i j : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W) := by
  let f : Fin 143 → Real := fun g =>
    Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
      Taeyoung.homDensity (S4Classification.coreGraph6 g) W
  calc
    _ = ∑ a : Fin 352, ∑ b : Fin 352,
        (TInt a i : Real) * (TInt b j : Real) * f (pairGroup a b) := by
      simp_rw [pair_density]
      rfl
    _ = ∑ g : Fin 143, (groupCoefficient i j g : Real) * f g :=
      sparseVector_pair_grouped pairGroup (root i) (root j) (value i) (value j) f
    _ = _ := by simp only [pulled_exact]; rfl

#print axioms pulled_exact
#print axioms pair_basis_density
end Taeyoung.Methods.RootedSOS.CompactS4.Young211
