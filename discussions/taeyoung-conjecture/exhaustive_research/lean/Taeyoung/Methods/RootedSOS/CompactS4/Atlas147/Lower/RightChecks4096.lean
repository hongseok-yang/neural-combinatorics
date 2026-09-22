import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.RightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_4096 : ∀ i : Fin 64,
    rightCheck ⟨4096+i.1, by omega⟩ := by decide +kernel
private theorem check_4160 : ∀ i : Fin 64,
    rightCheck ⟨4160+i.1, by omega⟩ := by decide +kernel
private theorem check_4224 : ∀ i : Fin 64,
    rightCheck ⟨4224+i.1, by omega⟩ := by decide +kernel
private theorem check_4288 : ∀ i : Fin 64,
    rightCheck ⟨4288+i.1, by omega⟩ := by decide +kernel
private theorem check_4352 : ∀ i : Fin 64,
    rightCheck ⟨4352+i.1, by omega⟩ := by decide +kernel
private theorem check_4416 : ∀ i : Fin 64,
    rightCheck ⟨4416+i.1, by omega⟩ := by decide +kernel
private theorem check_4480 : ∀ i : Fin 64,
    rightCheck ⟨4480+i.1, by omega⟩ := by decide +kernel
private theorem check_4544 : ∀ i : Fin 64,
    rightCheck ⟨4544+i.1, by omega⟩ := by decide +kernel
private theorem check_4608 : ∀ i : Fin 64,
    rightCheck ⟨4608+i.1, by omega⟩ := by decide +kernel
private theorem check_4672 : ∀ i : Fin 64,
    rightCheck ⟨4672+i.1, by omega⟩ := by decide +kernel
private theorem check_4736 : ∀ i : Fin 64,
    rightCheck ⟨4736+i.1, by omega⟩ := by decide +kernel
private theorem check_4800 : ∀ i : Fin 64,
    rightCheck ⟨4800+i.1, by omega⟩ := by decide +kernel
private theorem check_4864 : ∀ i : Fin 64,
    rightCheck ⟨4864+i.1, by omega⟩ := by decide +kernel
private theorem check_4928 : ∀ i : Fin 64,
    rightCheck ⟨4928+i.1, by omega⟩ := by decide +kernel
private theorem check_4992 : ∀ i : Fin 64,
    rightCheck ⟨4992+i.1, by omega⟩ := by decide +kernel
private theorem check_5056 : ∀ i : Fin 64,
    rightCheck ⟨5056+i.1, by omega⟩ := by decide +kernel
theorem RightChecks_4096 (i : Fin 1024) : rightCheck ⟨4096+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨4096+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4096 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨4160+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4160 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨4224+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4224 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨4288+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4288 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨4352+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4352 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨4416+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4416 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨4480+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4480 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨4544+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4544 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨4608+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4608 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨4672+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4672 j
  by_cases h : i.1 < 704
  · let j : Fin 64 := ⟨i.1-640, by omega⟩
    have he : (⟨4736+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4736 j
  by_cases h : i.1 < 768
  · let j : Fin 64 := ⟨i.1-704, by omega⟩
    have he : (⟨4800+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4800 j
  by_cases h : i.1 < 832
  · let j : Fin 64 := ⟨i.1-768, by omega⟩
    have he : (⟨4864+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4864 j
  by_cases h : i.1 < 896
  · let j : Fin 64 := ⟨i.1-832, by omega⟩
    have he : (⟨4928+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4928 j
  by_cases h : i.1 < 960
  · let j : Fin 64 := ⟨i.1-896, by omega⟩
    have he : (⟨4992+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_4992 j
  by_cases h : i.1 < 1024
  · let j : Fin 64 := ⟨i.1-960, by omega⟩
    have he : (⟨5056+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_5056 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower
