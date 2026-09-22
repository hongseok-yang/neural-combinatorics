import Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas185
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0013 : ∀ i : Fin 1,
    contractionCheck ⟨13+i.1, by omega⟩ := by decide +kernel
private theorem check_0014 : ∀ i : Fin 1,
    contractionCheck ⟨14+i.1, by omega⟩ := by decide +kernel
private theorem check_0015 : ∀ i : Fin 1,
    contractionCheck ⟨15+i.1, by omega⟩ := by decide +kernel
private theorem check_0016 : ∀ i : Fin 1,
    contractionCheck ⟨16+i.1, by omega⟩ := by decide +kernel
private theorem check_0017 : ∀ i : Fin 1,
    contractionCheck ⟨17+i.1, by omega⟩ := by decide +kernel
private theorem check_0018 : ∀ i : Fin 1,
    contractionCheck ⟨18+i.1, by omega⟩ := by decide +kernel
private theorem check_0019 : ∀ i : Fin 1,
    contractionCheck ⟨19+i.1, by omega⟩ := by decide +kernel
private theorem check_0020 : ∀ i : Fin 1,
    contractionCheck ⟨20+i.1, by omega⟩ := by decide +kernel
private theorem check_0021 : ∀ i : Fin 1,
    contractionCheck ⟨21+i.1, by omega⟩ := by decide +kernel
private theorem check_0022 : ∀ i : Fin 1,
    contractionCheck ⟨22+i.1, by omega⟩ := by decide +kernel
private theorem check_0023 : ∀ i : Fin 1,
    contractionCheck ⟨23+i.1, by omega⟩ := by decide +kernel
private theorem check_0024 : ∀ i : Fin 1,
    contractionCheck ⟨24+i.1, by omega⟩ := by decide +kernel
private theorem check_0025 : ∀ i : Fin 1,
    contractionCheck ⟨25+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0013 (i : Fin 13) : contractionCheck ⟨13+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨13+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0013 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨14+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0014 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨15+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0015 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨16+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0016 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨17+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0017 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨18+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0018 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨19+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0019 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨20+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0020 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨21+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0021 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨22+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0022 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨23+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0023 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨24+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0024 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨25+j.1, by omega⟩ : Fin 143) = ⟨13+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0025 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas185
