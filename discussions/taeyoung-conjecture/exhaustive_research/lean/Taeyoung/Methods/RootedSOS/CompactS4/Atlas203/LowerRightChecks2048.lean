import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.LowerRightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_2048 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2048+i.1, by omega⟩ := by decide +kernel
private theorem check_2112 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2112+i.1, by omega⟩ := by decide +kernel
private theorem check_2176 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2176+i.1, by omega⟩ := by decide +kernel
private theorem check_2240 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2240+i.1, by omega⟩ := by decide +kernel
private theorem check_2304 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2304+i.1, by omega⟩ := by decide +kernel
private theorem check_2368 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2368+i.1, by omega⟩ := by decide +kernel
private theorem check_2432 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2432+i.1, by omega⟩ := by decide +kernel
private theorem check_2496 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2496+i.1, by omega⟩ := by decide +kernel
private theorem check_2560 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2560+i.1, by omega⟩ := by decide +kernel
private theorem check_2624 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2624+i.1, by omega⟩ := by decide +kernel
private theorem check_2688 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2688+i.1, by omega⟩ := by decide +kernel
private theorem check_2752 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2752+i.1, by omega⟩ := by decide +kernel
private theorem check_2816 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2816+i.1, by omega⟩ := by decide +kernel
private theorem check_2880 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2880+i.1, by omega⟩ := by decide +kernel
private theorem check_2944 : ∀ i : Fin 64,
    Lower.rightCheck ⟨2944+i.1, by omega⟩ := by decide +kernel
private theorem check_3008 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3008+i.1, by omega⟩ := by decide +kernel
private theorem check_3072 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3072+i.1, by omega⟩ := by decide +kernel
private theorem check_3136 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3136+i.1, by omega⟩ := by decide +kernel
private theorem check_3200 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3200+i.1, by omega⟩ := by decide +kernel
private theorem check_3264 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3264+i.1, by omega⟩ := by decide +kernel
private theorem check_3328 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3328+i.1, by omega⟩ := by decide +kernel
private theorem check_3392 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3392+i.1, by omega⟩ := by decide +kernel
private theorem check_3456 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3456+i.1, by omega⟩ := by decide +kernel
private theorem check_3520 : ∀ i : Fin 64,
    Lower.rightCheck ⟨3520+i.1, by omega⟩ := by decide +kernel
private theorem check_3584 : ∀ i : Fin 48,
    Lower.rightCheck ⟨3584+i.1, by omega⟩ := by decide +kernel
theorem LowerRightChecks_2048 (i : Fin 1584) : Lower.rightCheck ⟨2048+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨2048+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2048 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨2112+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2112 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨2176+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2176 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨2240+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2240 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨2304+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2304 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨2368+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2368 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨2432+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2432 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨2496+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2496 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨2560+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2560 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨2624+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2624 j
  by_cases h : i.1 < 704
  · let j : Fin 64 := ⟨i.1-640, by omega⟩
    have he : (⟨2688+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2688 j
  by_cases h : i.1 < 768
  · let j : Fin 64 := ⟨i.1-704, by omega⟩
    have he : (⟨2752+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2752 j
  by_cases h : i.1 < 832
  · let j : Fin 64 := ⟨i.1-768, by omega⟩
    have he : (⟨2816+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2816 j
  by_cases h : i.1 < 896
  · let j : Fin 64 := ⟨i.1-832, by omega⟩
    have he : (⟨2880+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2880 j
  by_cases h : i.1 < 960
  · let j : Fin 64 := ⟨i.1-896, by omega⟩
    have he : (⟨2944+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2944 j
  by_cases h : i.1 < 1024
  · let j : Fin 64 := ⟨i.1-960, by omega⟩
    have he : (⟨3008+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3008 j
  by_cases h : i.1 < 1088
  · let j : Fin 64 := ⟨i.1-1024, by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3072 j
  by_cases h : i.1 < 1152
  · let j : Fin 64 := ⟨i.1-1088, by omega⟩
    have he : (⟨3136+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3136 j
  by_cases h : i.1 < 1216
  · let j : Fin 64 := ⟨i.1-1152, by omega⟩
    have he : (⟨3200+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3200 j
  by_cases h : i.1 < 1280
  · let j : Fin 64 := ⟨i.1-1216, by omega⟩
    have he : (⟨3264+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3264 j
  by_cases h : i.1 < 1344
  · let j : Fin 64 := ⟨i.1-1280, by omega⟩
    have he : (⟨3328+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3328 j
  by_cases h : i.1 < 1408
  · let j : Fin 64 := ⟨i.1-1344, by omega⟩
    have he : (⟨3392+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3392 j
  by_cases h : i.1 < 1472
  · let j : Fin 64 := ⟨i.1-1408, by omega⟩
    have he : (⟨3456+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3456 j
  by_cases h : i.1 < 1536
  · let j : Fin 64 := ⟨i.1-1472, by omega⟩
    have he : (⟨3520+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3520 j
  by_cases h : i.1 < 1584
  · let j : Fin 48 := ⟨i.1-1536, by omega⟩
    have he : (⟨3584+j.1, by omega⟩ : Fin 3632) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3584 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
