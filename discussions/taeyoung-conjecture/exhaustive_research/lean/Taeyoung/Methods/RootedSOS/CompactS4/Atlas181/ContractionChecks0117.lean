import Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.ContractionBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas181
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0117 : ∀ i : Fin 1,
    contractionCheck ⟨117+i.1, by omega⟩ := by decide +kernel
private theorem check_0118 : ∀ i : Fin 1,
    contractionCheck ⟨118+i.1, by omega⟩ := by decide +kernel
private theorem check_0119 : ∀ i : Fin 1,
    contractionCheck ⟨119+i.1, by omega⟩ := by decide +kernel
private theorem check_0120 : ∀ i : Fin 1,
    contractionCheck ⟨120+i.1, by omega⟩ := by decide +kernel
private theorem check_0121 : ∀ i : Fin 1,
    contractionCheck ⟨121+i.1, by omega⟩ := by decide +kernel
private theorem check_0122 : ∀ i : Fin 1,
    contractionCheck ⟨122+i.1, by omega⟩ := by decide +kernel
private theorem check_0123 : ∀ i : Fin 1,
    contractionCheck ⟨123+i.1, by omega⟩ := by decide +kernel
private theorem check_0124 : ∀ i : Fin 1,
    contractionCheck ⟨124+i.1, by omega⟩ := by decide +kernel
private theorem check_0125 : ∀ i : Fin 1,
    contractionCheck ⟨125+i.1, by omega⟩ := by decide +kernel
private theorem check_0126 : ∀ i : Fin 1,
    contractionCheck ⟨126+i.1, by omega⟩ := by decide +kernel
private theorem check_0127 : ∀ i : Fin 1,
    contractionCheck ⟨127+i.1, by omega⟩ := by decide +kernel
private theorem check_0128 : ∀ i : Fin 1,
    contractionCheck ⟨128+i.1, by omega⟩ := by decide +kernel
private theorem check_0129 : ∀ i : Fin 1,
    contractionCheck ⟨129+i.1, by omega⟩ := by decide +kernel
theorem ContractionChecks_0117 (i : Fin 13) : contractionCheck ⟨117+i.1, by omega⟩ := by
  by_cases h : i.1 < 1
  · let j : Fin 1 := ⟨i.1-0, by omega⟩
    have he : (⟨117+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0117 j
  by_cases h : i.1 < 2
  · let j : Fin 1 := ⟨i.1-1, by omega⟩
    have he : (⟨118+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0118 j
  by_cases h : i.1 < 3
  · let j : Fin 1 := ⟨i.1-2, by omega⟩
    have he : (⟨119+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0119 j
  by_cases h : i.1 < 4
  · let j : Fin 1 := ⟨i.1-3, by omega⟩
    have he : (⟨120+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0120 j
  by_cases h : i.1 < 5
  · let j : Fin 1 := ⟨i.1-4, by omega⟩
    have he : (⟨121+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0121 j
  by_cases h : i.1 < 6
  · let j : Fin 1 := ⟨i.1-5, by omega⟩
    have he : (⟨122+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0122 j
  by_cases h : i.1 < 7
  · let j : Fin 1 := ⟨i.1-6, by omega⟩
    have he : (⟨123+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0123 j
  by_cases h : i.1 < 8
  · let j : Fin 1 := ⟨i.1-7, by omega⟩
    have he : (⟨124+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0124 j
  by_cases h : i.1 < 9
  · let j : Fin 1 := ⟨i.1-8, by omega⟩
    have he : (⟨125+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0125 j
  by_cases h : i.1 < 10
  · let j : Fin 1 := ⟨i.1-9, by omega⟩
    have he : (⟨126+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0126 j
  by_cases h : i.1 < 11
  · let j : Fin 1 := ⟨i.1-10, by omega⟩
    have he : (⟨127+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0127 j
  by_cases h : i.1 < 12
  · let j : Fin 1 := ⟨i.1-11, by omega⟩
    have he : (⟨128+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0128 j
  by_cases h : i.1 < 13
  · let j : Fin 1 := ⟨i.1-12, by omega⟩
    have he : (⟨129+j.1, by omega⟩ : Fin 143) = ⟨117+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0129 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas181
