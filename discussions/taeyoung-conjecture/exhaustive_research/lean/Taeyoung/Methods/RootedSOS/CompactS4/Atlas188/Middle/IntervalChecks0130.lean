import Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.IntervalBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0130 : ∀ i : Fin 1,
    polynomialCheck ⟨130+i.1, by omega⟩ := by decide +kernel
private theorem check_0131 : ∀ i : Fin 1,
    polynomialCheck ⟨131+i.1, by omega⟩ := by decide +kernel
private theorem check_0132 : ∀ i : Fin 1,
    polynomialCheck ⟨132+i.1, by omega⟩ := by decide +kernel
private theorem check_0133 : ∀ i : Fin 1,
    polynomialCheck ⟨133+i.1, by omega⟩ := by decide +kernel
private theorem check_0134 : ∀ i : Fin 1,
    polynomialCheck ⟨134+i.1, by omega⟩ := by decide +kernel
private theorem check_0135 : ∀ i : Fin 1,
    polynomialCheck ⟨135+i.1, by omega⟩ := by decide +kernel
private theorem check_0136 : ∀ i : Fin 1,
    polynomialCheck ⟨136+i.1, by omega⟩ := by decide +kernel
private theorem check_0137 : ∀ i : Fin 1,
    polynomialCheck ⟨137+i.1, by omega⟩ := by decide +kernel
private theorem check_0138 : ∀ i : Fin 1,
    polynomialCheck ⟨138+i.1, by omega⟩ := by decide +kernel
private theorem check_0139 : ∀ i : Fin 1,
    polynomialCheck ⟨139+i.1, by omega⟩ := by decide +kernel
private theorem check_0140 : ∀ i : Fin 1,
    polynomialCheck ⟨140+i.1, by omega⟩ := by decide +kernel
private theorem check_0141 : ∀ i : Fin 1,
    polynomialCheck ⟨141+i.1, by omega⟩ := by decide +kernel
private theorem check_0142 : ∀ i : Fin 1,
    polynomialCheck ⟨142+i.1, by omega⟩ := by decide +kernel
theorem IntervalChecks_0130 (i : Fin 13) : polynomialCheck ⟨130+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨130+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0130 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨131+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0131 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨132+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0132 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨133+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0133 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨134+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0134 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨135+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0135 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨136+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0136 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨137+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0137 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨138+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0138 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨139+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0139 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨140+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0140 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨141+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0141 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨142+j.1, by omega⟩ : Fin 143) = ⟨130+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0142 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle
