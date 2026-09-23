import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0065 : ∀ i : Fin 1,
    contractionCheck ⟨65+i.1, by omega⟩ := by decide +kernel
private theorem check_0066 : ∀ i : Fin 1,
    contractionCheck ⟨66+i.1, by omega⟩ := by decide +kernel
private theorem check_0067 : ∀ i : Fin 1,
    contractionCheck ⟨67+i.1, by omega⟩ := by decide +kernel
private theorem check_0068 : ∀ i : Fin 1,
    contractionCheck ⟨68+i.1, by omega⟩ := by decide +kernel
private theorem check_0069 : ∀ i : Fin 1,
    contractionCheck ⟨69+i.1, by omega⟩ := by decide +kernel
private theorem check_0070 : ∀ i : Fin 1,
    contractionCheck ⟨70+i.1, by omega⟩ := by decide +kernel
private theorem check_0071 : ∀ i : Fin 1,
    contractionCheck ⟨71+i.1, by omega⟩ := by decide +kernel
private theorem check_0072 : ∀ i : Fin 1,
    contractionCheck ⟨72+i.1, by omega⟩ := by decide +kernel
private theorem check_0073 : ∀ i : Fin 1,
    contractionCheck ⟨73+i.1, by omega⟩ := by decide +kernel
private theorem check_0074 : ∀ i : Fin 1,
    contractionCheck ⟨74+i.1, by omega⟩ := by decide +kernel
private theorem check_0075 : ∀ i : Fin 1,
    contractionCheck ⟨75+i.1, by omega⟩ := by decide +kernel
private theorem check_0076 : ∀ i : Fin 1,
    contractionCheck ⟨76+i.1, by omega⟩ := by decide +kernel
private theorem check_0077 : ∀ i : Fin 1,
    contractionCheck ⟨77+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0065 (i : Fin 13) : contractionCheck ⟨65+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨65+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0065 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨66+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0066 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨67+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0067 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨68+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0068 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨69+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0069 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨70+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0070 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨71+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0071 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨72+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0072 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨73+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0073 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨74+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0074 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨75+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0075 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨76+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0076 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨77+j.1, by omega⟩ : Fin 143) = ⟨65+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0077 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
