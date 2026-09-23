import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0104 : ∀ i : Fin 1,
    contractionCheck ⟨104+i.1, by omega⟩ := by decide +kernel
private theorem check_0105 : ∀ i : Fin 1,
    contractionCheck ⟨105+i.1, by omega⟩ := by decide +kernel
private theorem check_0106 : ∀ i : Fin 1,
    contractionCheck ⟨106+i.1, by omega⟩ := by decide +kernel
private theorem check_0107 : ∀ i : Fin 1,
    contractionCheck ⟨107+i.1, by omega⟩ := by decide +kernel
private theorem check_0108 : ∀ i : Fin 1,
    contractionCheck ⟨108+i.1, by omega⟩ := by decide +kernel
private theorem check_0109 : ∀ i : Fin 1,
    contractionCheck ⟨109+i.1, by omega⟩ := by decide +kernel
private theorem check_0110 : ∀ i : Fin 1,
    contractionCheck ⟨110+i.1, by omega⟩ := by decide +kernel
private theorem check_0111 : ∀ i : Fin 1,
    contractionCheck ⟨111+i.1, by omega⟩ := by decide +kernel
private theorem check_0112 : ∀ i : Fin 1,
    contractionCheck ⟨112+i.1, by omega⟩ := by decide +kernel
private theorem check_0113 : ∀ i : Fin 1,
    contractionCheck ⟨113+i.1, by omega⟩ := by decide +kernel
private theorem check_0114 : ∀ i : Fin 1,
    contractionCheck ⟨114+i.1, by omega⟩ := by decide +kernel
private theorem check_0115 : ∀ i : Fin 1,
    contractionCheck ⟨115+i.1, by omega⟩ := by decide +kernel
private theorem check_0116 : ∀ i : Fin 1,
    contractionCheck ⟨116+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0104 (i : Fin 13) : contractionCheck ⟨104+i.1, by omega⟩ := by
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
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
