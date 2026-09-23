import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.IntervalBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0026 : ∀ i : Fin 1,
    polynomialCheck ⟨26+i.1, by omega⟩ := by decide +kernel
private theorem check_0027 : ∀ i : Fin 1,
    polynomialCheck ⟨27+i.1, by omega⟩ := by decide +kernel
private theorem check_0028 : ∀ i : Fin 1,
    polynomialCheck ⟨28+i.1, by omega⟩ := by decide +kernel
private theorem check_0029 : ∀ i : Fin 1,
    polynomialCheck ⟨29+i.1, by omega⟩ := by decide +kernel
private theorem check_0030 : ∀ i : Fin 1,
    polynomialCheck ⟨30+i.1, by omega⟩ := by decide +kernel
private theorem check_0031 : ∀ i : Fin 1,
    polynomialCheck ⟨31+i.1, by omega⟩ := by decide +kernel
private theorem check_0032 : ∀ i : Fin 1,
    polynomialCheck ⟨32+i.1, by omega⟩ := by decide +kernel
private theorem check_0033 : ∀ i : Fin 1,
    polynomialCheck ⟨33+i.1, by omega⟩ := by decide +kernel
private theorem check_0034 : ∀ i : Fin 1,
    polynomialCheck ⟨34+i.1, by omega⟩ := by decide +kernel
private theorem check_0035 : ∀ i : Fin 1,
    polynomialCheck ⟨35+i.1, by omega⟩ := by decide +kernel
private theorem check_0036 : ∀ i : Fin 1,
    polynomialCheck ⟨36+i.1, by omega⟩ := by decide +kernel
private theorem check_0037 : ∀ i : Fin 1,
    polynomialCheck ⟨37+i.1, by omega⟩ := by decide +kernel
private theorem check_0038 : ∀ i : Fin 1,
    polynomialCheck ⟨38+i.1, by omega⟩ := by decide +kernel
private theorem check_0039 : ∀ i : Fin 1,
    polynomialCheck ⟨39+i.1, by omega⟩ := by decide +kernel
private theorem check_0040 : ∀ i : Fin 1,
    polynomialCheck ⟨40+i.1, by omega⟩ := by decide +kernel
private theorem check_0041 : ∀ i : Fin 1,
    polynomialCheck ⟨41+i.1, by omega⟩ := by decide +kernel
private theorem check_0042 : ∀ i : Fin 1,
    polynomialCheck ⟨42+i.1, by omega⟩ := by decide +kernel
private theorem check_0043 : ∀ i : Fin 1,
    polynomialCheck ⟨43+i.1, by omega⟩ := by decide +kernel
private theorem check_0044 : ∀ i : Fin 1,
    polynomialCheck ⟨44+i.1, by omega⟩ := by decide +kernel
private theorem check_0045 : ∀ i : Fin 1,
    polynomialCheck ⟨45+i.1, by omega⟩ := by decide +kernel
private theorem check_0046 : ∀ i : Fin 1,
    polynomialCheck ⟨46+i.1, by omega⟩ := by decide +kernel
private theorem check_0047 : ∀ i : Fin 1,
    polynomialCheck ⟨47+i.1, by omega⟩ := by decide +kernel
private theorem check_0048 : ∀ i : Fin 1,
    polynomialCheck ⟨48+i.1, by omega⟩ := by decide +kernel
private theorem check_0049 : ∀ i : Fin 1,
    polynomialCheck ⟨49+i.1, by omega⟩ := by decide +kernel
private theorem check_0050 : ∀ i : Fin 1,
    polynomialCheck ⟨50+i.1, by omega⟩ := by decide +kernel
private theorem check_0051 : ∀ i : Fin 1,
    polynomialCheck ⟨51+i.1, by omega⟩ := by decide +kernel
theorem IntervalChecks_0026 (i : Fin 26) : polynomialCheck ⟨26+i.1, by omega⟩ := by
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
  by_cases h : i.1 < 14
  · let j : Fin 1 := ⟨i.1-13, by omega⟩
    have he : (⟨39+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0039 j
  by_cases h : i.1 < 15
  · let j : Fin 1 := ⟨i.1-14, by omega⟩
    have he : (⟨40+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0040 j
  by_cases h : i.1 < 16
  · let j : Fin 1 := ⟨i.1-15, by omega⟩
    have he : (⟨41+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0041 j
  by_cases h : i.1 < 17
  · let j : Fin 1 := ⟨i.1-16, by omega⟩
    have he : (⟨42+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0042 j
  by_cases h : i.1 < 18
  · let j : Fin 1 := ⟨i.1-17, by omega⟩
    have he : (⟨43+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0043 j
  by_cases h : i.1 < 19
  · let j : Fin 1 := ⟨i.1-18, by omega⟩
    have he : (⟨44+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0044 j
  by_cases h : i.1 < 20
  · let j : Fin 1 := ⟨i.1-19, by omega⟩
    have he : (⟨45+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0045 j
  by_cases h : i.1 < 21
  · let j : Fin 1 := ⟨i.1-20, by omega⟩
    have he : (⟨46+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0046 j
  by_cases h : i.1 < 22
  · let j : Fin 1 := ⟨i.1-21, by omega⟩
    have he : (⟨47+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0047 j
  by_cases h : i.1 < 23
  · let j : Fin 1 := ⟨i.1-22, by omega⟩
    have he : (⟨48+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0048 j
  by_cases h : i.1 < 24
  · let j : Fin 1 := ⟨i.1-23, by omega⟩
    have he : (⟨49+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0049 j
  by_cases h : i.1 < 25
  · let j : Fin 1 := ⟨i.1-24, by omega⟩
    have he : (⟨50+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0050 j
  by_cases h : i.1 < 26
  · let j : Fin 1 := ⟨i.1-25, by omega⟩
    have he : (⟨51+j.1, by omega⟩ : Fin 143) = ⟨26+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0051 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower
