import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0052 : ∀ i : Fin 1,
    contractionCheck ⟨52+i.1, by omega⟩ := by decide +kernel
private theorem check_0053 : ∀ i : Fin 1,
    contractionCheck ⟨53+i.1, by omega⟩ := by decide +kernel
private theorem check_0054 : ∀ i : Fin 1,
    contractionCheck ⟨54+i.1, by omega⟩ := by decide +kernel
private theorem check_0055 : ∀ i : Fin 1,
    contractionCheck ⟨55+i.1, by omega⟩ := by decide +kernel
private theorem check_0056 : ∀ i : Fin 1,
    contractionCheck ⟨56+i.1, by omega⟩ := by decide +kernel
private theorem check_0057 : ∀ i : Fin 1,
    contractionCheck ⟨57+i.1, by omega⟩ := by decide +kernel
private theorem check_0058 : ∀ i : Fin 1,
    contractionCheck ⟨58+i.1, by omega⟩ := by decide +kernel
private theorem check_0059 : ∀ i : Fin 1,
    contractionCheck ⟨59+i.1, by omega⟩ := by decide +kernel
private theorem check_0060 : ∀ i : Fin 1,
    contractionCheck ⟨60+i.1, by omega⟩ := by decide +kernel
private theorem check_0061 : ∀ i : Fin 1,
    contractionCheck ⟨61+i.1, by omega⟩ := by decide +kernel
private theorem check_0062 : ∀ i : Fin 1,
    contractionCheck ⟨62+i.1, by omega⟩ := by decide +kernel
private theorem check_0063 : ∀ i : Fin 1,
    contractionCheck ⟨63+i.1, by omega⟩ := by decide +kernel
private theorem check_0064 : ∀ i : Fin 1,
    contractionCheck ⟨64+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0052 (i : Fin 13) : contractionCheck ⟨52+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨52+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0052 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨53+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0053 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨54+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0054 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨55+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0055 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨56+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0056 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨57+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0057 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨58+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0058 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨59+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0059 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨60+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0060 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨61+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0061 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨62+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0062 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨63+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0063 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨64+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0064 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper
