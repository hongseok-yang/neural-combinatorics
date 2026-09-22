import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.IntervalBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0104 : ∀ i : Fin 1,
    polynomialCheck ⟨104+i.1, by omega⟩ := by decide +kernel
private theorem check_0105 : ∀ i : Fin 1,
    polynomialCheck ⟨105+i.1, by omega⟩ := by decide +kernel
private theorem check_0106 : ∀ i : Fin 1,
    polynomialCheck ⟨106+i.1, by omega⟩ := by decide +kernel
private theorem check_0107 : ∀ i : Fin 1,
    polynomialCheck ⟨107+i.1, by omega⟩ := by decide +kernel
private theorem check_0108 : ∀ i : Fin 1,
    polynomialCheck ⟨108+i.1, by omega⟩ := by decide +kernel
private theorem check_0109 : ∀ i : Fin 1,
    polynomialCheck ⟨109+i.1, by omega⟩ := by decide +kernel
private theorem check_0110 : ∀ i : Fin 1,
    polynomialCheck ⟨110+i.1, by omega⟩ := by decide +kernel
private theorem check_0111 : ∀ i : Fin 1,
    polynomialCheck ⟨111+i.1, by omega⟩ := by decide +kernel
private theorem check_0112 : ∀ i : Fin 1,
    polynomialCheck ⟨112+i.1, by omega⟩ := by decide +kernel
private theorem check_0113 : ∀ i : Fin 1,
    polynomialCheck ⟨113+i.1, by omega⟩ := by decide +kernel
private theorem check_0114 : ∀ i : Fin 1,
    polynomialCheck ⟨114+i.1, by omega⟩ := by decide +kernel
private theorem check_0115 : ∀ i : Fin 1,
    polynomialCheck ⟨115+i.1, by omega⟩ := by decide +kernel
private theorem check_0116 : ∀ i : Fin 1,
    polynomialCheck ⟨116+i.1, by omega⟩ := by decide +kernel
private theorem check_0117 : ∀ i : Fin 1,
    polynomialCheck ⟨117+i.1, by omega⟩ := by decide +kernel
private theorem check_0118 : ∀ i : Fin 1,
    polynomialCheck ⟨118+i.1, by omega⟩ := by decide +kernel
private theorem check_0119 : ∀ i : Fin 1,
    polynomialCheck ⟨119+i.1, by omega⟩ := by decide +kernel
private theorem check_0120 : ∀ i : Fin 1,
    polynomialCheck ⟨120+i.1, by omega⟩ := by decide +kernel
private theorem check_0121 : ∀ i : Fin 1,
    polynomialCheck ⟨121+i.1, by omega⟩ := by decide +kernel
private theorem check_0122 : ∀ i : Fin 1,
    polynomialCheck ⟨122+i.1, by omega⟩ := by decide +kernel
private theorem check_0123 : ∀ i : Fin 1,
    polynomialCheck ⟨123+i.1, by omega⟩ := by decide +kernel
private theorem check_0124 : ∀ i : Fin 1,
    polynomialCheck ⟨124+i.1, by omega⟩ := by decide +kernel
private theorem check_0125 : ∀ i : Fin 1,
    polynomialCheck ⟨125+i.1, by omega⟩ := by decide +kernel
private theorem check_0126 : ∀ i : Fin 1,
    polynomialCheck ⟨126+i.1, by omega⟩ := by decide +kernel
private theorem check_0127 : ∀ i : Fin 1,
    polynomialCheck ⟨127+i.1, by omega⟩ := by decide +kernel
private theorem check_0128 : ∀ i : Fin 1,
    polynomialCheck ⟨128+i.1, by omega⟩ := by decide +kernel
private theorem check_0129 : ∀ i : Fin 1,
    polynomialCheck ⟨129+i.1, by omega⟩ := by decide +kernel
theorem IntervalChecks_0104 (i : Fin 26) : polynomialCheck ⟨104+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨104+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0104 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨105+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0105 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨106+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0106 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨107+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0107 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨108+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0108 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨109+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0109 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨110+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0110 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨111+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0111 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨112+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0112 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨113+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0113 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨114+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0114 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨115+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0115 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨116+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0116 j
  by_cases h : i.1 < 14
  · let j : Fin 1 := ⟨i.1-13, by omega⟩
    have he : (⟨117+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0117 j
  by_cases h : i.1 < 15
  · let j : Fin 1 := ⟨i.1-14, by omega⟩
    have he : (⟨118+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0118 j
  by_cases h : i.1 < 16
  · let j : Fin 1 := ⟨i.1-15, by omega⟩
    have he : (⟨119+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0119 j
  by_cases h : i.1 < 17
  · let j : Fin 1 := ⟨i.1-16, by omega⟩
    have he : (⟨120+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0120 j
  by_cases h : i.1 < 18
  · let j : Fin 1 := ⟨i.1-17, by omega⟩
    have he : (⟨121+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0121 j
  by_cases h : i.1 < 19
  · let j : Fin 1 := ⟨i.1-18, by omega⟩
    have he : (⟨122+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0122 j
  by_cases h : i.1 < 20
  · let j : Fin 1 := ⟨i.1-19, by omega⟩
    have he : (⟨123+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0123 j
  by_cases h : i.1 < 21
  · let j : Fin 1 := ⟨i.1-20, by omega⟩
    have he : (⟨124+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0124 j
  by_cases h : i.1 < 22
  · let j : Fin 1 := ⟨i.1-21, by omega⟩
    have he : (⟨125+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0125 j
  by_cases h : i.1 < 23
  · let j : Fin 1 := ⟨i.1-22, by omega⟩
    have he : (⟨126+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0126 j
  by_cases h : i.1 < 24
  · let j : Fin 1 := ⟨i.1-23, by omega⟩
    have he : (⟨127+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0127 j
  by_cases h : i.1 < 25
  · let j : Fin 1 := ⟨i.1-24, by omega⟩
    have he : (⟨128+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0128 j
  by_cases h : i.1 < 26
  · let j : Fin 1 := ⟨i.1-25, by omega⟩
    have he : (⟨129+j.1, by omega⟩ : Fin 143) = ⟨104+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0129 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower
