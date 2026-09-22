import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.IntervalBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0078 : ∀ i : Fin 1,
    polynomialCheck ⟨78+i.1, by omega⟩ := by decide +kernel
private theorem check_0079 : ∀ i : Fin 1,
    polynomialCheck ⟨79+i.1, by omega⟩ := by decide +kernel
private theorem check_0080 : ∀ i : Fin 1,
    polynomialCheck ⟨80+i.1, by omega⟩ := by decide +kernel
private theorem check_0081 : ∀ i : Fin 1,
    polynomialCheck ⟨81+i.1, by omega⟩ := by decide +kernel
private theorem check_0082 : ∀ i : Fin 1,
    polynomialCheck ⟨82+i.1, by omega⟩ := by decide +kernel
private theorem check_0083 : ∀ i : Fin 1,
    polynomialCheck ⟨83+i.1, by omega⟩ := by decide +kernel
private theorem check_0084 : ∀ i : Fin 1,
    polynomialCheck ⟨84+i.1, by omega⟩ := by decide +kernel
private theorem check_0085 : ∀ i : Fin 1,
    polynomialCheck ⟨85+i.1, by omega⟩ := by decide +kernel
private theorem check_0086 : ∀ i : Fin 1,
    polynomialCheck ⟨86+i.1, by omega⟩ := by decide +kernel
private theorem check_0087 : ∀ i : Fin 1,
    polynomialCheck ⟨87+i.1, by omega⟩ := by decide +kernel
private theorem check_0088 : ∀ i : Fin 1,
    polynomialCheck ⟨88+i.1, by omega⟩ := by decide +kernel
private theorem check_0089 : ∀ i : Fin 1,
    polynomialCheck ⟨89+i.1, by omega⟩ := by decide +kernel
private theorem check_0090 : ∀ i : Fin 1,
    polynomialCheck ⟨90+i.1, by omega⟩ := by decide +kernel
private theorem check_0091 : ∀ i : Fin 1,
    polynomialCheck ⟨91+i.1, by omega⟩ := by decide +kernel
private theorem check_0092 : ∀ i : Fin 1,
    polynomialCheck ⟨92+i.1, by omega⟩ := by decide +kernel
private theorem check_0093 : ∀ i : Fin 1,
    polynomialCheck ⟨93+i.1, by omega⟩ := by decide +kernel
private theorem check_0094 : ∀ i : Fin 1,
    polynomialCheck ⟨94+i.1, by omega⟩ := by decide +kernel
private theorem check_0095 : ∀ i : Fin 1,
    polynomialCheck ⟨95+i.1, by omega⟩ := by decide +kernel
private theorem check_0096 : ∀ i : Fin 1,
    polynomialCheck ⟨96+i.1, by omega⟩ := by decide +kernel
private theorem check_0097 : ∀ i : Fin 1,
    polynomialCheck ⟨97+i.1, by omega⟩ := by decide +kernel
private theorem check_0098 : ∀ i : Fin 1,
    polynomialCheck ⟨98+i.1, by omega⟩ := by decide +kernel
private theorem check_0099 : ∀ i : Fin 1,
    polynomialCheck ⟨99+i.1, by omega⟩ := by decide +kernel
private theorem check_0100 : ∀ i : Fin 1,
    polynomialCheck ⟨100+i.1, by omega⟩ := by decide +kernel
private theorem check_0101 : ∀ i : Fin 1,
    polynomialCheck ⟨101+i.1, by omega⟩ := by decide +kernel
private theorem check_0102 : ∀ i : Fin 1,
    polynomialCheck ⟨102+i.1, by omega⟩ := by decide +kernel
private theorem check_0103 : ∀ i : Fin 1,
    polynomialCheck ⟨103+i.1, by omega⟩ := by decide +kernel
theorem IntervalChecks_0078 (i : Fin 26) : polynomialCheck ⟨78+i.1, by omega⟩ := by
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
  by_cases h : i.1 < 14
  · let j : Fin 1 := ⟨i.1-13, by omega⟩
    have he : (⟨91+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0091 j
  by_cases h : i.1 < 15
  · let j : Fin 1 := ⟨i.1-14, by omega⟩
    have he : (⟨92+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0092 j
  by_cases h : i.1 < 16
  · let j : Fin 1 := ⟨i.1-15, by omega⟩
    have he : (⟨93+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0093 j
  by_cases h : i.1 < 17
  · let j : Fin 1 := ⟨i.1-16, by omega⟩
    have he : (⟨94+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0094 j
  by_cases h : i.1 < 18
  · let j : Fin 1 := ⟨i.1-17, by omega⟩
    have he : (⟨95+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0095 j
  by_cases h : i.1 < 19
  · let j : Fin 1 := ⟨i.1-18, by omega⟩
    have he : (⟨96+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0096 j
  by_cases h : i.1 < 20
  · let j : Fin 1 := ⟨i.1-19, by omega⟩
    have he : (⟨97+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0097 j
  by_cases h : i.1 < 21
  · let j : Fin 1 := ⟨i.1-20, by omega⟩
    have he : (⟨98+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0098 j
  by_cases h : i.1 < 22
  · let j : Fin 1 := ⟨i.1-21, by omega⟩
    have he : (⟨99+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0099 j
  by_cases h : i.1 < 23
  · let j : Fin 1 := ⟨i.1-22, by omega⟩
    have he : (⟨100+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0100 j
  by_cases h : i.1 < 24
  · let j : Fin 1 := ⟨i.1-23, by omega⟩
    have he : (⟨101+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0101 j
  by_cases h : i.1 < 25
  · let j : Fin 1 := ⟨i.1-24, by omega⟩
    have he : (⟨102+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0102 j
  by_cases h : i.1 < 26
  · let j : Fin 1 := ⟨i.1-25, by omega⟩
    have he : (⟨103+j.1, by omega⟩ : Fin 143) = ⟨78+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0103 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
