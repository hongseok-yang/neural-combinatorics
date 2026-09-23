import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.IntervalBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0000 : ∀ i : Fin 1,
    polynomialCheck ⟨0+i.1, by omega⟩ := by decide +kernel
private theorem check_0001 : ∀ i : Fin 1,
    polynomialCheck ⟨1+i.1, by omega⟩ := by decide +kernel
private theorem check_0002 : ∀ i : Fin 1,
    polynomialCheck ⟨2+i.1, by omega⟩ := by decide +kernel
private theorem check_0003 : ∀ i : Fin 1,
    polynomialCheck ⟨3+i.1, by omega⟩ := by decide +kernel
private theorem check_0004 : ∀ i : Fin 1,
    polynomialCheck ⟨4+i.1, by omega⟩ := by decide +kernel
private theorem check_0005 : ∀ i : Fin 1,
    polynomialCheck ⟨5+i.1, by omega⟩ := by decide +kernel
private theorem check_0006 : ∀ i : Fin 1,
    polynomialCheck ⟨6+i.1, by omega⟩ := by decide +kernel
private theorem check_0007 : ∀ i : Fin 1,
    polynomialCheck ⟨7+i.1, by omega⟩ := by decide +kernel
private theorem check_0008 : ∀ i : Fin 1,
    polynomialCheck ⟨8+i.1, by omega⟩ := by decide +kernel
private theorem check_0009 : ∀ i : Fin 1,
    polynomialCheck ⟨9+i.1, by omega⟩ := by decide +kernel
private theorem check_0010 : ∀ i : Fin 1,
    polynomialCheck ⟨10+i.1, by omega⟩ := by decide +kernel
private theorem check_0011 : ∀ i : Fin 1,
    polynomialCheck ⟨11+i.1, by omega⟩ := by decide +kernel
private theorem check_0012 : ∀ i : Fin 1,
    polynomialCheck ⟨12+i.1, by omega⟩ := by decide +kernel
private theorem check_0013 : ∀ i : Fin 1,
    polynomialCheck ⟨13+i.1, by omega⟩ := by decide +kernel
private theorem check_0014 : ∀ i : Fin 1,
    polynomialCheck ⟨14+i.1, by omega⟩ := by decide +kernel
private theorem check_0015 : ∀ i : Fin 1,
    polynomialCheck ⟨15+i.1, by omega⟩ := by decide +kernel
private theorem check_0016 : ∀ i : Fin 1,
    polynomialCheck ⟨16+i.1, by omega⟩ := by decide +kernel
private theorem check_0017 : ∀ i : Fin 1,
    polynomialCheck ⟨17+i.1, by omega⟩ := by decide +kernel
private theorem check_0018 : ∀ i : Fin 1,
    polynomialCheck ⟨18+i.1, by omega⟩ := by decide +kernel
private theorem check_0019 : ∀ i : Fin 1,
    polynomialCheck ⟨19+i.1, by omega⟩ := by decide +kernel
private theorem check_0020 : ∀ i : Fin 1,
    polynomialCheck ⟨20+i.1, by omega⟩ := by decide +kernel
private theorem check_0021 : ∀ i : Fin 1,
    polynomialCheck ⟨21+i.1, by omega⟩ := by decide +kernel
private theorem check_0022 : ∀ i : Fin 1,
    polynomialCheck ⟨22+i.1, by omega⟩ := by decide +kernel
private theorem check_0023 : ∀ i : Fin 1,
    polynomialCheck ⟨23+i.1, by omega⟩ := by decide +kernel
private theorem check_0024 : ∀ i : Fin 1,
    polynomialCheck ⟨24+i.1, by omega⟩ := by decide +kernel
private theorem check_0025 : ∀ i : Fin 1,
    polynomialCheck ⟨25+i.1, by omega⟩ := by decide +kernel
theorem IntervalChecks_0000 (i : Fin 26) : polynomialCheck ⟨0+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0000 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨1+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0001 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨2+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0002 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨3+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0003 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨4+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0004 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨5+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0005 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨6+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0006 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨7+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0007 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨8+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0008 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨9+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0009 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨10+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0010 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨11+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0011 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨12+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0012 j
  by_cases h : i.1 < 14
  · let j : Fin 1 := ⟨i.1-13, by omega⟩
    have he : (⟨13+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0013 j
  by_cases h : i.1 < 15
  · let j : Fin 1 := ⟨i.1-14, by omega⟩
    have he : (⟨14+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0014 j
  by_cases h : i.1 < 16
  · let j : Fin 1 := ⟨i.1-15, by omega⟩
    have he : (⟨15+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0015 j
  by_cases h : i.1 < 17
  · let j : Fin 1 := ⟨i.1-16, by omega⟩
    have he : (⟨16+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0016 j
  by_cases h : i.1 < 18
  · let j : Fin 1 := ⟨i.1-17, by omega⟩
    have he : (⟨17+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0017 j
  by_cases h : i.1 < 19
  · let j : Fin 1 := ⟨i.1-18, by omega⟩
    have he : (⟨18+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0018 j
  by_cases h : i.1 < 20
  · let j : Fin 1 := ⟨i.1-19, by omega⟩
    have he : (⟨19+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0019 j
  by_cases h : i.1 < 21
  · let j : Fin 1 := ⟨i.1-20, by omega⟩
    have he : (⟨20+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0020 j
  by_cases h : i.1 < 22
  · let j : Fin 1 := ⟨i.1-21, by omega⟩
    have he : (⟨21+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0021 j
  by_cases h : i.1 < 23
  · let j : Fin 1 := ⟨i.1-22, by omega⟩
    have he : (⟨22+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0022 j
  by_cases h : i.1 < 24
  · let j : Fin 1 := ⟨i.1-23, by omega⟩
    have he : (⟨23+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0023 j
  by_cases h : i.1 < 25
  · let j : Fin 1 := ⟨i.1-24, by omega⟩
    have he : (⟨24+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0024 j
  by_cases h : i.1 < 26
  · let j : Fin 1 := ⟨i.1-25, by omega⟩
    have he : (⟨25+j.1, by omega⟩ : Fin 143) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0025 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
