import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.RightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_1024 : ∀ i : Fin 64,
    rightCheck ⟨1024+i.1, by omega⟩ := by decide +kernel
private theorem check_1088 : ∀ i : Fin 64,
    rightCheck ⟨1088+i.1, by omega⟩ := by decide +kernel
private theorem check_1152 : ∀ i : Fin 64,
    rightCheck ⟨1152+i.1, by omega⟩ := by decide +kernel
private theorem check_1216 : ∀ i : Fin 64,
    rightCheck ⟨1216+i.1, by omega⟩ := by decide +kernel
private theorem check_1280 : ∀ i : Fin 64,
    rightCheck ⟨1280+i.1, by omega⟩ := by decide +kernel
private theorem check_1344 : ∀ i : Fin 64,
    rightCheck ⟨1344+i.1, by omega⟩ := by decide +kernel
private theorem check_1408 : ∀ i : Fin 64,
    rightCheck ⟨1408+i.1, by omega⟩ := by decide +kernel
private theorem check_1472 : ∀ i : Fin 64,
    rightCheck ⟨1472+i.1, by omega⟩ := by decide +kernel
private theorem check_1536 : ∀ i : Fin 64,
    rightCheck ⟨1536+i.1, by omega⟩ := by decide +kernel
private theorem check_1600 : ∀ i : Fin 64,
    rightCheck ⟨1600+i.1, by omega⟩ := by decide +kernel
private theorem check_1664 : ∀ i : Fin 64,
    rightCheck ⟨1664+i.1, by omega⟩ := by decide +kernel
private theorem check_1728 : ∀ i : Fin 64,
    rightCheck ⟨1728+i.1, by omega⟩ := by decide +kernel
private theorem check_1792 : ∀ i : Fin 64,
    rightCheck ⟨1792+i.1, by omega⟩ := by decide +kernel
private theorem check_1856 : ∀ i : Fin 64,
    rightCheck ⟨1856+i.1, by omega⟩ := by decide +kernel
private theorem check_1920 : ∀ i : Fin 64,
    rightCheck ⟨1920+i.1, by omega⟩ := by decide +kernel
private theorem check_1984 : ∀ i : Fin 64,
    rightCheck ⟨1984+i.1, by omega⟩ := by decide +kernel
theorem RightChecks_1024 (i : Fin 1024) : rightCheck ⟨1024+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1024 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨1088+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1088 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨1152+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1152 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨1216+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1216 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨1280+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1280 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨1344+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1344 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨1408+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1408 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨1472+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1472 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨1536+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1536 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨1600+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1600 j
  by_cases h : i.1 < 704
  · let j : Fin 64 := ⟨i.1-640, by omega⟩
    have he : (⟨1664+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1664 j
  by_cases h : i.1 < 768
  · let j : Fin 64 := ⟨i.1-704, by omega⟩
    have he : (⟨1728+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1728 j
  by_cases h : i.1 < 832
  · let j : Fin 64 := ⟨i.1-768, by omega⟩
    have he : (⟨1792+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1792 j
  by_cases h : i.1 < 896
  · let j : Fin 64 := ⟨i.1-832, by omega⟩
    have he : (⟨1856+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1856 j
  by_cases h : i.1 < 960
  · let j : Fin 64 := ⟨i.1-896, by omega⟩
    have he : (⟨1920+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1920 j
  by_cases h : i.1 < 1024
  · let j : Fin 64 := ⟨i.1-960, by omega⟩
    have he : (⟨1984+j.1, by omega⟩ : Fin 5820) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1984 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
