import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows00
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows10
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows20
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows30
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows40
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows50
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows60
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows70
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows80
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows90
import Taeyoung.Methods.RootedSOS.Atlas43GramC0Rows100
import Taeyoung.Methods.RootedSOS.Atlas43GramC1Rows00
import Taeyoung.Methods.RootedSOS.Atlas43GramC1Rows10
import Taeyoung.Methods.RootedSOS.Atlas43GramC1Rows20
import Taeyoung.Methods.RootedSOS.Atlas43GramC1Rows30
import Taeyoung.Methods.RootedSOS.Atlas43GramC1Rows40

/-!
# Exact Gram matrices for the Atlas 43 certificate

This module assembles the separately checked ten-row blocks into the two
diagonal-dominance theorems used by the generic Gram positivity argument.
-/

open Finset

namespace Taeyoung.Methods.RootedSOS.Atlas43Gram

private theorem C₀_congr {i k : Fin 107} (h : i.1 = k.1)
    (hk : ∑ j, abs (C₀ k j) ≤ 1) : ∑ j, abs (C₀ i j) ≤ 1 := by
  have : i = k := Fin.ext h
  simpa [this] using hk

private theorem C₁_congr {i k : Fin 48} (h : i.1 = k.1)
    (hk : ∑ j, abs (C₁ k j) ≤ 1) : ∑ j, abs (C₁ i j) ≤ 1 := by
  have : i = k := Fin.ext h
  simpa [this] using hk

theorem C₀_row_dominant (i : Fin 107) : ∑ j, abs (C₀ i j) ≤ 1 := by
  by_cases h₀ : i.1 < 10
  · exact C₀_congr rfl (C₀_rows_00 ⟨i.1, h₀⟩)
  by_cases h₁ : i.1 < 20
  · let k : Fin 10 := ⟨i.1 - 10, by omega⟩
    apply C₀_congr (k := ⟨10 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_10 k
  by_cases h₂ : i.1 < 30
  · let k : Fin 10 := ⟨i.1 - 20, by omega⟩
    apply C₀_congr (k := ⟨20 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_20 k
  by_cases h₃ : i.1 < 40
  · let k : Fin 10 := ⟨i.1 - 30, by omega⟩
    apply C₀_congr (k := ⟨30 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_30 k
  by_cases h₄ : i.1 < 50
  · let k : Fin 10 := ⟨i.1 - 40, by omega⟩
    apply C₀_congr (k := ⟨40 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_40 k
  by_cases h₅ : i.1 < 60
  · let k : Fin 10 := ⟨i.1 - 50, by omega⟩
    apply C₀_congr (k := ⟨50 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_50 k
  by_cases h₆ : i.1 < 70
  · let k : Fin 10 := ⟨i.1 - 60, by omega⟩
    apply C₀_congr (k := ⟨60 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_60 k
  by_cases h₇ : i.1 < 80
  · let k : Fin 10 := ⟨i.1 - 70, by omega⟩
    apply C₀_congr (k := ⟨70 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_70 k
  by_cases h₈ : i.1 < 90
  · let k : Fin 10 := ⟨i.1 - 80, by omega⟩
    apply C₀_congr (k := ⟨80 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_80 k
  by_cases h₉ : i.1 < 100
  · let k : Fin 10 := ⟨i.1 - 90, by omega⟩
    apply C₀_congr (k := ⟨90 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_90 k
  · let k : Fin 7 := ⟨i.1 - 100, by omega⟩
    apply C₀_congr (k := ⟨100 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₀_rows_100 k

theorem C₁_row_dominant (i : Fin 48) : ∑ j, abs (C₁ i j) ≤ 1 := by
  by_cases h₀ : i.1 < 10
  · exact C₁_congr rfl (C₁_rows_00 ⟨i.1, h₀⟩)
  by_cases h₁ : i.1 < 20
  · let k : Fin 10 := ⟨i.1 - 10, by omega⟩
    apply C₁_congr (k := ⟨10 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₁_rows_10 k
  by_cases h₂ : i.1 < 30
  · let k : Fin 10 := ⟨i.1 - 20, by omega⟩
    apply C₁_congr (k := ⟨20 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₁_rows_20 k
  by_cases h₃ : i.1 < 40
  · let k : Fin 10 := ⟨i.1 - 30, by omega⟩
    apply C₁_congr (k := ⟨30 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₁_rows_30 k
  · let k : Fin 8 := ⟨i.1 - 40, by omega⟩
    apply C₁_congr (k := ⟨40 + k.1, by omega⟩) (by simp [k]; omega)
    exact C₁_rows_40 k

end Taeyoung.Methods.RootedSOS.Atlas43Gram
