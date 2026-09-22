import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0091 : ∀ i : Fin 1,
    contractionCheck ⟨91+i.1, by omega⟩ := by decide +kernel
private theorem check_0092 : ∀ i : Fin 1,
    contractionCheck ⟨92+i.1, by omega⟩ := by decide +kernel
private theorem check_0093 : ∀ i : Fin 1,
    contractionCheck ⟨93+i.1, by omega⟩ := by decide +kernel
private theorem check_0094 : ∀ i : Fin 1,
    contractionCheck ⟨94+i.1, by omega⟩ := by decide +kernel
private theorem check_0095 : ∀ i : Fin 1,
    contractionCheck ⟨95+i.1, by omega⟩ := by decide +kernel
private theorem check_0096 : ∀ i : Fin 1,
    contractionCheck ⟨96+i.1, by omega⟩ := by decide +kernel
private theorem check_0097 : ∀ i : Fin 1,
    contractionCheck ⟨97+i.1, by omega⟩ := by decide +kernel
private theorem check_0098 : ∀ i : Fin 1,
    contractionCheck ⟨98+i.1, by omega⟩ := by decide +kernel
private theorem check_0099 : ∀ i : Fin 1,
    contractionCheck ⟨99+i.1, by omega⟩ := by decide +kernel
private theorem check_0100 : ∀ i : Fin 1,
    contractionCheck ⟨100+i.1, by omega⟩ := by decide +kernel
private theorem check_0101 : ∀ i : Fin 1,
    contractionCheck ⟨101+i.1, by omega⟩ := by decide +kernel
private theorem check_0102 : ∀ i : Fin 1,
    contractionCheck ⟨102+i.1, by omega⟩ := by decide +kernel
private theorem check_0103 : ∀ i : Fin 1,
    contractionCheck ⟨103+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0091 (i : Fin 13) : contractionCheck ⟨91+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨91+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0091 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨92+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0092 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨93+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0093 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨94+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0094 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨95+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0095 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨96+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0096 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨97+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0097 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨98+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0098 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨99+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0099 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨100+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0100 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨101+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0101 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨102+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0102 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨103+j.1, by omega⟩ : Fin 143) = ⟨91+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0103 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
