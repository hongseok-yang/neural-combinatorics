import Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.RightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas122
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_5120 : ∀ i : Fin 64,
    rightCheck ⟨5120+i.1, by omega⟩ := by decide +kernel
private theorem check_5184 : ∀ i : Fin 64,
    rightCheck ⟨5184+i.1, by omega⟩ := by decide +kernel
private theorem check_5248 : ∀ i : Fin 64,
    rightCheck ⟨5248+i.1, by omega⟩ := by decide +kernel
private theorem check_5312 : ∀ i : Fin 64,
    rightCheck ⟨5312+i.1, by omega⟩ := by decide +kernel
private theorem check_5376 : ∀ i : Fin 64,
    rightCheck ⟨5376+i.1, by omega⟩ := by decide +kernel
private theorem check_5440 : ∀ i : Fin 64,
    rightCheck ⟨5440+i.1, by omega⟩ := by decide +kernel
private theorem check_5504 : ∀ i : Fin 64,
    rightCheck ⟨5504+i.1, by omega⟩ := by decide +kernel
private theorem check_5568 : ∀ i : Fin 64,
    rightCheck ⟨5568+i.1, by omega⟩ := by decide +kernel
private theorem check_5632 : ∀ i : Fin 64,
    rightCheck ⟨5632+i.1, by omega⟩ := by decide +kernel
private theorem check_5696 : ∀ i : Fin 64,
    rightCheck ⟨5696+i.1, by omega⟩ := by decide +kernel
private theorem check_5760 : ∀ i : Fin 60,
    rightCheck ⟨5760+i.1, by omega⟩ := by decide +kernel
theorem RightChecks_5120 (i : Fin 700) : rightCheck ⟨5120+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨5120+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5120 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨5184+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5184 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨5248+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5248 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨5312+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5312 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨5376+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5376 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨5440+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5440 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨5504+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5504 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨5568+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5568 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨5632+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5632 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨5696+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5696 j
  by_cases h : i.1 < 700
  · let j : Fin 60 := ⟨i.1-640, by omega⟩
    have he : (⟨5760+j.1, by omega⟩ : Fin 5820) = ⟨5120+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5760 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas122
