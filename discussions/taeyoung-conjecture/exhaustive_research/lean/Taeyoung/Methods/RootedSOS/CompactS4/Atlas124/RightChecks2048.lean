import Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.RightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas124
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_2048 : ∀ i : Fin 64,
    rightCheck ⟨2048+i.1, by omega⟩ := by decide +kernel
private theorem check_2112 : ∀ i : Fin 64,
    rightCheck ⟨2112+i.1, by omega⟩ := by decide +kernel
private theorem check_2176 : ∀ i : Fin 64,
    rightCheck ⟨2176+i.1, by omega⟩ := by decide +kernel
private theorem check_2240 : ∀ i : Fin 64,
    rightCheck ⟨2240+i.1, by omega⟩ := by decide +kernel
private theorem check_2304 : ∀ i : Fin 64,
    rightCheck ⟨2304+i.1, by omega⟩ := by decide +kernel
private theorem check_2368 : ∀ i : Fin 64,
    rightCheck ⟨2368+i.1, by omega⟩ := by decide +kernel
private theorem check_2432 : ∀ i : Fin 64,
    rightCheck ⟨2432+i.1, by omega⟩ := by decide +kernel
private theorem check_2496 : ∀ i : Fin 64,
    rightCheck ⟨2496+i.1, by omega⟩ := by decide +kernel
private theorem check_2560 : ∀ i : Fin 64,
    rightCheck ⟨2560+i.1, by omega⟩ := by decide +kernel
private theorem check_2624 : ∀ i : Fin 64,
    rightCheck ⟨2624+i.1, by omega⟩ := by decide +kernel
private theorem check_2688 : ∀ i : Fin 64,
    rightCheck ⟨2688+i.1, by omega⟩ := by decide +kernel
private theorem check_2752 : ∀ i : Fin 64,
    rightCheck ⟨2752+i.1, by omega⟩ := by decide +kernel
private theorem check_2816 : ∀ i : Fin 64,
    rightCheck ⟨2816+i.1, by omega⟩ := by decide +kernel
private theorem check_2880 : ∀ i : Fin 64,
    rightCheck ⟨2880+i.1, by omega⟩ := by decide +kernel
private theorem check_2944 : ∀ i : Fin 64,
    rightCheck ⟨2944+i.1, by omega⟩ := by decide +kernel
private theorem check_3008 : ∀ i : Fin 64,
    rightCheck ⟨3008+i.1, by omega⟩ := by decide +kernel
theorem RightChecks_2048 (i : Fin 1024) : rightCheck ⟨2048+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨2048+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2048 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨2112+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2112 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨2176+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2176 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨2240+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2240 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨2304+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2304 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨2368+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2368 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨2432+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2432 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨2496+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2496 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨2560+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2560 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨2624+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2624 j
  by_cases h : i.1 < 704
  · let j : Fin 64 := ⟨i.1-640, by omega⟩
    have he : (⟨2688+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2688 j
  by_cases h : i.1 < 768
  · let j : Fin 64 := ⟨i.1-704, by omega⟩
    have he : (⟨2752+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2752 j
  by_cases h : i.1 < 832
  · let j : Fin 64 := ⟨i.1-768, by omega⟩
    have he : (⟨2816+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2816 j
  by_cases h : i.1 < 896
  · let j : Fin 64 := ⟨i.1-832, by omega⟩
    have he : (⟨2880+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2880 j
  by_cases h : i.1 < 960
  · let j : Fin 64 := ⟨i.1-896, by omega⟩
    have he : (⟨2944+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2944 j
  by_cases h : i.1 < 1024
  · let j : Fin 64 := ⟨i.1-960, by omega⟩
    have he : (⟨3008+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3008 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas124
