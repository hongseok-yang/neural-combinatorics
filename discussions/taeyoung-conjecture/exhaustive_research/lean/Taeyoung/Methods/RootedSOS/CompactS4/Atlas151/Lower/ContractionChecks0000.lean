import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0000 : ∀ i : Fin 1,
    contractionCheck ⟨0+i.1, by omega⟩ := by decide +kernel
private theorem check_0001 : ∀ i : Fin 1,
    contractionCheck ⟨1+i.1, by omega⟩ := by decide +kernel
private theorem check_0002 : ∀ i : Fin 1,
    contractionCheck ⟨2+i.1, by omega⟩ := by decide +kernel
private theorem check_0003 : ∀ i : Fin 1,
    contractionCheck ⟨3+i.1, by omega⟩ := by decide +kernel
private theorem check_0004 : ∀ i : Fin 1,
    contractionCheck ⟨4+i.1, by omega⟩ := by decide +kernel
private theorem check_0005 : ∀ i : Fin 1,
    contractionCheck ⟨5+i.1, by omega⟩ := by decide +kernel
private theorem check_0006 : ∀ i : Fin 1,
    contractionCheck ⟨6+i.1, by omega⟩ := by decide +kernel
private theorem check_0007 : ∀ i : Fin 1,
    contractionCheck ⟨7+i.1, by omega⟩ := by decide +kernel
private theorem check_0008 : ∀ i : Fin 1,
    contractionCheck ⟨8+i.1, by omega⟩ := by decide +kernel
private theorem check_0009 : ∀ i : Fin 1,
    contractionCheck ⟨9+i.1, by omega⟩ := by decide +kernel
private theorem check_0010 : ∀ i : Fin 1,
    contractionCheck ⟨10+i.1, by omega⟩ := by decide +kernel
private theorem check_0011 : ∀ i : Fin 1,
    contractionCheck ⟨11+i.1, by omega⟩ := by decide +kernel
private theorem check_0012 : ∀ i : Fin 1,
    contractionCheck ⟨12+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0000 (i : Fin 13) : contractionCheck ⟨0+i.1, by omega⟩ := by
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
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower
