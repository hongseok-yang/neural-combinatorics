import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.IntervalBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas194
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0052 : ∀ i : Fin 1,
    polynomialCheck ⟨52+i.1, by omega⟩ := by decide +kernel
private theorem check_0053 : ∀ i : Fin 1,
    polynomialCheck ⟨53+i.1, by omega⟩ := by decide +kernel
private theorem check_0054 : ∀ i : Fin 1,
    polynomialCheck ⟨54+i.1, by omega⟩ := by decide +kernel
private theorem check_0055 : ∀ i : Fin 1,
    polynomialCheck ⟨55+i.1, by omega⟩ := by decide +kernel
private theorem check_0056 : ∀ i : Fin 1,
    polynomialCheck ⟨56+i.1, by omega⟩ := by decide +kernel
private theorem check_0057 : ∀ i : Fin 1,
    polynomialCheck ⟨57+i.1, by omega⟩ := by decide +kernel
private theorem check_0058 : ∀ i : Fin 1,
    polynomialCheck ⟨58+i.1, by omega⟩ := by decide +kernel
private theorem check_0059 : ∀ i : Fin 1,
    polynomialCheck ⟨59+i.1, by omega⟩ := by decide +kernel
private theorem check_0060 : ∀ i : Fin 1,
    polynomialCheck ⟨60+i.1, by omega⟩ := by decide +kernel
private theorem check_0061 : ∀ i : Fin 1,
    polynomialCheck ⟨61+i.1, by omega⟩ := by decide +kernel
private theorem check_0062 : ∀ i : Fin 1,
    polynomialCheck ⟨62+i.1, by omega⟩ := by decide +kernel
private theorem check_0063 : ∀ i : Fin 1,
    polynomialCheck ⟨63+i.1, by omega⟩ := by decide +kernel
private theorem check_0064 : ∀ i : Fin 1,
    polynomialCheck ⟨64+i.1, by omega⟩ := by decide +kernel
private theorem check_0065 : ∀ i : Fin 1,
    polynomialCheck ⟨65+i.1, by omega⟩ := by decide +kernel
private theorem check_0066 : ∀ i : Fin 1,
    polynomialCheck ⟨66+i.1, by omega⟩ := by decide +kernel
private theorem check_0067 : ∀ i : Fin 1,
    polynomialCheck ⟨67+i.1, by omega⟩ := by decide +kernel
private theorem check_0068 : ∀ i : Fin 1,
    polynomialCheck ⟨68+i.1, by omega⟩ := by decide +kernel
private theorem check_0069 : ∀ i : Fin 1,
    polynomialCheck ⟨69+i.1, by omega⟩ := by decide +kernel
private theorem check_0070 : ∀ i : Fin 1,
    polynomialCheck ⟨70+i.1, by omega⟩ := by decide +kernel
private theorem check_0071 : ∀ i : Fin 1,
    polynomialCheck ⟨71+i.1, by omega⟩ := by decide +kernel
private theorem check_0072 : ∀ i : Fin 1,
    polynomialCheck ⟨72+i.1, by omega⟩ := by decide +kernel
private theorem check_0073 : ∀ i : Fin 1,
    polynomialCheck ⟨73+i.1, by omega⟩ := by decide +kernel
private theorem check_0074 : ∀ i : Fin 1,
    polynomialCheck ⟨74+i.1, by omega⟩ := by decide +kernel
private theorem check_0075 : ∀ i : Fin 1,
    polynomialCheck ⟨75+i.1, by omega⟩ := by decide +kernel
private theorem check_0076 : ∀ i : Fin 1,
    polynomialCheck ⟨76+i.1, by omega⟩ := by decide +kernel
private theorem check_0077 : ∀ i : Fin 1,
    polynomialCheck ⟨77+i.1, by omega⟩ := by decide +kernel
theorem IntervalChecks_0052 (i : Fin 26) : polynomialCheck ⟨52+i.1, by omega⟩ := by
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
  by_cases h : i.1 < 14
  · let j : Fin 1 := ⟨i.1-13, by omega⟩
    have he : (⟨65+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0065 j
  by_cases h : i.1 < 15
  · let j : Fin 1 := ⟨i.1-14, by omega⟩
    have he : (⟨66+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0066 j
  by_cases h : i.1 < 16
  · let j : Fin 1 := ⟨i.1-15, by omega⟩
    have he : (⟨67+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0067 j
  by_cases h : i.1 < 17
  · let j : Fin 1 := ⟨i.1-16, by omega⟩
    have he : (⟨68+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0068 j
  by_cases h : i.1 < 18
  · let j : Fin 1 := ⟨i.1-17, by omega⟩
    have he : (⟨69+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0069 j
  by_cases h : i.1 < 19
  · let j : Fin 1 := ⟨i.1-18, by omega⟩
    have he : (⟨70+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0070 j
  by_cases h : i.1 < 20
  · let j : Fin 1 := ⟨i.1-19, by omega⟩
    have he : (⟨71+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0071 j
  by_cases h : i.1 < 21
  · let j : Fin 1 := ⟨i.1-20, by omega⟩
    have he : (⟨72+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0072 j
  by_cases h : i.1 < 22
  · let j : Fin 1 := ⟨i.1-21, by omega⟩
    have he : (⟨73+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0073 j
  by_cases h : i.1 < 23
  · let j : Fin 1 := ⟨i.1-22, by omega⟩
    have he : (⟨74+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0074 j
  by_cases h : i.1 < 24
  · let j : Fin 1 := ⟨i.1-23, by omega⟩
    have he : (⟨75+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0075 j
  by_cases h : i.1 < 25
  · let j : Fin 1 := ⟨i.1-24, by omega⟩
    have he : (⟨76+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0076 j
  by_cases h : i.1 < 26
  · let j : Fin 1 := ⟨i.1-25, by omega⟩
    have he : (⟨77+j.1, by omega⟩ : Fin 143) = ⟨52+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0077 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas194
