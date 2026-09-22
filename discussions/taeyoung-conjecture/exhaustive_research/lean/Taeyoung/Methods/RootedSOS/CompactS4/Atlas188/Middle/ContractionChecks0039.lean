import Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0039 : ∀ i : Fin 1,
    contractionCheck ⟨39+i.1, by omega⟩ := by decide +kernel
private theorem check_0040 : ∀ i : Fin 1,
    contractionCheck ⟨40+i.1, by omega⟩ := by decide +kernel
private theorem check_0041 : ∀ i : Fin 1,
    contractionCheck ⟨41+i.1, by omega⟩ := by decide +kernel
private theorem check_0042 : ∀ i : Fin 1,
    contractionCheck ⟨42+i.1, by omega⟩ := by decide +kernel
private theorem check_0043 : ∀ i : Fin 1,
    contractionCheck ⟨43+i.1, by omega⟩ := by decide +kernel
private theorem check_0044 : ∀ i : Fin 1,
    contractionCheck ⟨44+i.1, by omega⟩ := by decide +kernel
private theorem check_0045 : ∀ i : Fin 1,
    contractionCheck ⟨45+i.1, by omega⟩ := by decide +kernel
private theorem check_0046 : ∀ i : Fin 1,
    contractionCheck ⟨46+i.1, by omega⟩ := by decide +kernel
private theorem check_0047 : ∀ i : Fin 1,
    contractionCheck ⟨47+i.1, by omega⟩ := by decide +kernel
private theorem check_0048 : ∀ i : Fin 1,
    contractionCheck ⟨48+i.1, by omega⟩ := by decide +kernel
private theorem check_0049 : ∀ i : Fin 1,
    contractionCheck ⟨49+i.1, by omega⟩ := by decide +kernel
private theorem check_0050 : ∀ i : Fin 1,
    contractionCheck ⟨50+i.1, by omega⟩ := by decide +kernel
private theorem check_0051 : ∀ i : Fin 1,
    contractionCheck ⟨51+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0039 (i : Fin 13) : contractionCheck ⟨39+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨39+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0039 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨40+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0040 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨41+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0041 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨42+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0042 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨43+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0043 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨44+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0044 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨45+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0045 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨46+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0046 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨47+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0047 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨48+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0048 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨49+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0049 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨50+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0050 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨51+j.1, by omega⟩ : Fin 143) = ⟨39+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0051 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle
