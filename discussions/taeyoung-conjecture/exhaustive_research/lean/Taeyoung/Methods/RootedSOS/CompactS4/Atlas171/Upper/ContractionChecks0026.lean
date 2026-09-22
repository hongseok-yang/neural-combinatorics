import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0026 : ∀ i : Fin 1,
    contractionCheck ⟨26+i.1, by omega⟩ := by decide +kernel
private theorem check_0027 : ∀ i : Fin 1,
    contractionCheck ⟨27+i.1, by omega⟩ := by decide +kernel
private theorem check_0028 : ∀ i : Fin 1,
    contractionCheck ⟨28+i.1, by omega⟩ := by decide +kernel
private theorem check_0029 : ∀ i : Fin 1,
    contractionCheck ⟨29+i.1, by omega⟩ := by decide +kernel
private theorem check_0030 : ∀ i : Fin 1,
    contractionCheck ⟨30+i.1, by omega⟩ := by decide +kernel
private theorem check_0031 : ∀ i : Fin 1,
    contractionCheck ⟨31+i.1, by omega⟩ := by decide +kernel
private theorem check_0032 : ∀ i : Fin 1,
    contractionCheck ⟨32+i.1, by omega⟩ := by decide +kernel
private theorem check_0033 : ∀ i : Fin 1,
    contractionCheck ⟨33+i.1, by omega⟩ := by decide +kernel
private theorem check_0034 : ∀ i : Fin 1,
    contractionCheck ⟨34+i.1, by omega⟩ := by decide +kernel
private theorem check_0035 : ∀ i : Fin 1,
    contractionCheck ⟨35+i.1, by omega⟩ := by decide +kernel
private theorem check_0036 : ∀ i : Fin 1,
    contractionCheck ⟨36+i.1, by omega⟩ := by decide +kernel
private theorem check_0037 : ∀ i : Fin 1,
    contractionCheck ⟨37+i.1, by omega⟩ := by decide +kernel
private theorem check_0038 : ∀ i : Fin 1,
    contractionCheck ⟨38+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0026 (i : Fin 13) : contractionCheck ⟨26+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨26+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0026 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨27+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0027 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨28+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0028 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨29+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0029 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨30+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0030 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨31+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0031 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨32+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0032 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨33+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0033 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨34+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0034 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨35+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0035 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨36+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0036 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨37+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0037 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨38+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0038 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper
