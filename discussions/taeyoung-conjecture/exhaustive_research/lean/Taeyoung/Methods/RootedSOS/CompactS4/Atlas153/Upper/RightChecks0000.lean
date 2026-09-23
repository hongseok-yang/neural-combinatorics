import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper.RightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0000 : ∀ i : Fin 64,
    rightCheck ⟨0+i.1, by omega⟩ := by decide +kernel
private theorem check_0064 : ∀ i : Fin 64,
    rightCheck ⟨64+i.1, by omega⟩ := by decide +kernel
private theorem check_0128 : ∀ i : Fin 64,
    rightCheck ⟨128+i.1, by omega⟩ := by decide +kernel
private theorem check_0192 : ∀ i : Fin 64,
    rightCheck ⟨192+i.1, by omega⟩ := by decide +kernel
private theorem check_0256 : ∀ i : Fin 64,
    rightCheck ⟨256+i.1, by omega⟩ := by decide +kernel
private theorem check_0320 : ∀ i : Fin 64,
    rightCheck ⟨320+i.1, by omega⟩ := by decide +kernel
private theorem check_0384 : ∀ i : Fin 64,
    rightCheck ⟨384+i.1, by omega⟩ := by decide +kernel
private theorem check_0448 : ∀ i : Fin 64,
    rightCheck ⟨448+i.1, by omega⟩ := by decide +kernel
private theorem check_0512 : ∀ i : Fin 64,
    rightCheck ⟨512+i.1, by omega⟩ := by decide +kernel
private theorem check_0576 : ∀ i : Fin 64,
    rightCheck ⟨576+i.1, by omega⟩ := by decide +kernel
private theorem check_0640 : ∀ i : Fin 64,
    rightCheck ⟨640+i.1, by omega⟩ := by decide +kernel
private theorem check_0704 : ∀ i : Fin 64,
    rightCheck ⟨704+i.1, by omega⟩ := by decide +kernel
private theorem check_0768 : ∀ i : Fin 64,
    rightCheck ⟨768+i.1, by omega⟩ := by decide +kernel
private theorem check_0832 : ∀ i : Fin 64,
    rightCheck ⟨832+i.1, by omega⟩ := by decide +kernel
private theorem check_0896 : ∀ i : Fin 64,
    rightCheck ⟨896+i.1, by omega⟩ := by decide +kernel
private theorem check_0960 : ∀ i : Fin 64,
    rightCheck ⟨960+i.1, by omega⟩ := by decide +kernel
theorem RightChecks_0000 (i : Fin 1024) : rightCheck ⟨0+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0000 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨64+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0064 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨128+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0128 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨192+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0192 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨256+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0256 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨320+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0320 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨384+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0384 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨448+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0448 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0512 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨576+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0576 j
  by_cases h : i.1 < 704
  · let j : Fin 64 := ⟨i.1-640, by omega⟩
    have he : (⟨640+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0640 j
  by_cases h : i.1 < 768
  · let j : Fin 64 := ⟨i.1-704, by omega⟩
    have he : (⟨704+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0704 j
  by_cases h : i.1 < 832
  · let j : Fin 64 := ⟨i.1-768, by omega⟩
    have he : (⟨768+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0768 j
  by_cases h : i.1 < 896
  · let j : Fin 64 := ⟨i.1-832, by omega⟩
    have he : (⟨832+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0832 j
  by_cases h : i.1 < 960
  · let j : Fin 64 := ⟨i.1-896, by omega⟩
    have he : (⟨896+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0896 j
  by_cases h : i.1 < 1024
  · let j : Fin 64 := ⟨i.1-960, by omega⟩
    have he : (⟨960+j.1, by omega⟩ : Fin 5820) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0960 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Upper
