import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.RightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_3072 : ∀ i : Fin 64,
    rightCheck ⟨3072+i.1, by omega⟩ := by decide +kernel
private theorem check_3136 : ∀ i : Fin 64,
    rightCheck ⟨3136+i.1, by omega⟩ := by decide +kernel
private theorem check_3200 : ∀ i : Fin 64,
    rightCheck ⟨3200+i.1, by omega⟩ := by decide +kernel
private theorem check_3264 : ∀ i : Fin 64,
    rightCheck ⟨3264+i.1, by omega⟩ := by decide +kernel
private theorem check_3328 : ∀ i : Fin 64,
    rightCheck ⟨3328+i.1, by omega⟩ := by decide +kernel
private theorem check_3392 : ∀ i : Fin 64,
    rightCheck ⟨3392+i.1, by omega⟩ := by decide +kernel
private theorem check_3456 : ∀ i : Fin 64,
    rightCheck ⟨3456+i.1, by omega⟩ := by decide +kernel
private theorem check_3520 : ∀ i : Fin 64,
    rightCheck ⟨3520+i.1, by omega⟩ := by decide +kernel
private theorem check_3584 : ∀ i : Fin 64,
    rightCheck ⟨3584+i.1, by omega⟩ := by decide +kernel
private theorem check_3648 : ∀ i : Fin 64,
    rightCheck ⟨3648+i.1, by omega⟩ := by decide +kernel
private theorem check_3712 : ∀ i : Fin 64,
    rightCheck ⟨3712+i.1, by omega⟩ := by decide +kernel
private theorem check_3776 : ∀ i : Fin 64,
    rightCheck ⟨3776+i.1, by omega⟩ := by decide +kernel
private theorem check_3840 : ∀ i : Fin 64,
    rightCheck ⟨3840+i.1, by omega⟩ := by decide +kernel
private theorem check_3904 : ∀ i : Fin 64,
    rightCheck ⟨3904+i.1, by omega⟩ := by decide +kernel
private theorem check_3968 : ∀ i : Fin 64,
    rightCheck ⟨3968+i.1, by omega⟩ := by decide +kernel
private theorem check_4032 : ∀ i : Fin 64,
    rightCheck ⟨4032+i.1, by omega⟩ := by decide +kernel
theorem RightChecks_3072 (i : Fin 1024) : rightCheck ⟨3072+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3072 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨3136+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3136 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨3200+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3200 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨3264+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3264 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨3328+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3328 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨3392+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3392 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨3456+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3456 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨3520+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3520 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨3584+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3584 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨3648+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3648 j
  by_cases h : i.1 < 704
  · let j : Fin 64 := ⟨i.1-640, by omega⟩
    have he : (⟨3712+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3712 j
  by_cases h : i.1 < 768
  · let j : Fin 64 := ⟨i.1-704, by omega⟩
    have he : (⟨3776+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3776 j
  by_cases h : i.1 < 832
  · let j : Fin 64 := ⟨i.1-768, by omega⟩
    have he : (⟨3840+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3840 j
  by_cases h : i.1 < 896
  · let j : Fin 64 := ⟨i.1-832, by omega⟩
    have he : (⟨3904+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3904 j
  by_cases h : i.1 < 960
  · let j : Fin 64 := ⟨i.1-896, by omega⟩
    have he : (⟨3968+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3968 j
  by_cases h : i.1 < 1024
  · let j : Fin 64 := ⟨i.1-960, by omega⟩
    have he : (⟨4032+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4032 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
