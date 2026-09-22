import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0078 : ∀ i : Fin 1,
    contractionCheck ⟨78+i.1, by omega⟩ := by decide +kernel
private theorem check_0079 : ∀ i : Fin 1,
    contractionCheck ⟨79+i.1, by omega⟩ := by decide +kernel
private theorem check_0080 : ∀ i : Fin 1,
    contractionCheck ⟨80+i.1, by omega⟩ := by decide +kernel
private theorem check_0081 : ∀ i : Fin 1,
    contractionCheck ⟨81+i.1, by omega⟩ := by decide +kernel
private theorem check_0082 : ∀ i : Fin 1,
    contractionCheck ⟨82+i.1, by omega⟩ := by decide +kernel
private theorem check_0083 : ∀ i : Fin 1,
    contractionCheck ⟨83+i.1, by omega⟩ := by decide +kernel
private theorem check_0084 : ∀ i : Fin 1,
    contractionCheck ⟨84+i.1, by omega⟩ := by decide +kernel
private theorem check_0085 : ∀ i : Fin 1,
    contractionCheck ⟨85+i.1, by omega⟩ := by decide +kernel
private theorem check_0086 : ∀ i : Fin 1,
    contractionCheck ⟨86+i.1, by omega⟩ := by decide +kernel
private theorem check_0087 : ∀ i : Fin 1,
    contractionCheck ⟨87+i.1, by omega⟩ := by decide +kernel
private theorem check_0088 : ∀ i : Fin 1,
    contractionCheck ⟨88+i.1, by omega⟩ := by decide +kernel
private theorem check_0089 : ∀ i : Fin 1,
    contractionCheck ⟨89+i.1, by omega⟩ := by decide +kernel
private theorem check_0090 : ∀ i : Fin 1,
    contractionCheck ⟨90+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0078 (i : Fin 13) : contractionCheck ⟨78+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨78+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0078 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨79+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0079 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨80+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0080 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨81+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0081 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨82+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0082 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨83+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0083 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨84+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0084 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨85+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0085 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨86+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0086 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨87+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0087 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨88+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0088 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨89+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0089 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨90+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0090 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle
