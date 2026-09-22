import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.LowerRightBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas130
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0000 : ∀ i : Fin 64,
    Lower.rightCheck ⟨0+i.1, by omega⟩ := by decide +kernel
private theorem check_0064 : ∀ i : Fin 64,
    Lower.rightCheck ⟨64+i.1, by omega⟩ := by decide +kernel
private theorem check_0128 : ∀ i : Fin 64,
    Lower.rightCheck ⟨128+i.1, by omega⟩ := by decide +kernel
private theorem check_0192 : ∀ i : Fin 64,
    Lower.rightCheck ⟨192+i.1, by omega⟩ := by decide +kernel
private theorem check_0256 : ∀ i : Fin 64,
    Lower.rightCheck ⟨256+i.1, by omega⟩ := by decide +kernel
private theorem check_0320 : ∀ i : Fin 64,
    Lower.rightCheck ⟨320+i.1, by omega⟩ := by decide +kernel
private theorem check_0384 : ∀ i : Fin 64,
    Lower.rightCheck ⟨384+i.1, by omega⟩ := by decide +kernel
private theorem check_0448 : ∀ i : Fin 64,
    Lower.rightCheck ⟨448+i.1, by omega⟩ := by decide +kernel
private theorem check_0512 : ∀ i : Fin 64,
    Lower.rightCheck ⟨512+i.1, by omega⟩ := by decide +kernel
private theorem check_0576 : ∀ i : Fin 64,
    Lower.rightCheck ⟨576+i.1, by omega⟩ := by decide +kernel
private theorem check_0640 : ∀ i : Fin 64,
    Lower.rightCheck ⟨640+i.1, by omega⟩ := by decide +kernel
private theorem check_0704 : ∀ i : Fin 64,
    Lower.rightCheck ⟨704+i.1, by omega⟩ := by decide +kernel
private theorem check_0768 : ∀ i : Fin 64,
    Lower.rightCheck ⟨768+i.1, by omega⟩ := by decide +kernel
private theorem check_0832 : ∀ i : Fin 64,
    Lower.rightCheck ⟨832+i.1, by omega⟩ := by decide +kernel
private theorem check_0896 : ∀ i : Fin 64,
    Lower.rightCheck ⟨896+i.1, by omega⟩ := by decide +kernel
private theorem check_0960 : ∀ i : Fin 64,
    Lower.rightCheck ⟨960+i.1, by omega⟩ := by decide +kernel
private theorem check_1024 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1024+i.1, by omega⟩ := by decide +kernel
private theorem check_1088 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1088+i.1, by omega⟩ := by decide +kernel
private theorem check_1152 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1152+i.1, by omega⟩ := by decide +kernel
private theorem check_1216 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1216+i.1, by omega⟩ := by decide +kernel
private theorem check_1280 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1280+i.1, by omega⟩ := by decide +kernel
private theorem check_1344 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1344+i.1, by omega⟩ := by decide +kernel
private theorem check_1408 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1408+i.1, by omega⟩ := by decide +kernel
private theorem check_1472 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1472+i.1, by omega⟩ := by decide +kernel
private theorem check_1536 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1536+i.1, by omega⟩ := by decide +kernel
private theorem check_1600 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1600+i.1, by omega⟩ := by decide +kernel
private theorem check_1664 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1664+i.1, by omega⟩ := by decide +kernel
private theorem check_1728 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1728+i.1, by omega⟩ := by decide +kernel
private theorem check_1792 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1792+i.1, by omega⟩ := by decide +kernel
private theorem check_1856 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1856+i.1, by omega⟩ := by decide +kernel
private theorem check_1920 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1920+i.1, by omega⟩ := by decide +kernel
private theorem check_1984 : ∀ i : Fin 64,
    Lower.rightCheck ⟨1984+i.1, by omega⟩ := by decide +kernel
theorem LowerRightChecks_0000 (i : Fin 2048) : Lower.rightCheck ⟨0+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0000 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨64+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0064 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨128+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0128 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨192+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0192 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨256+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0256 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨320+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0320 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨384+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0384 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨448+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0448 j
  by_cases h : i.1 < 576
  · let j : Fin 64 := ⟨i.1-512, by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0512 j
  by_cases h : i.1 < 640
  · let j : Fin 64 := ⟨i.1-576, by omega⟩
    have he : (⟨576+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0576 j
  by_cases h : i.1 < 704
  · let j : Fin 64 := ⟨i.1-640, by omega⟩
    have he : (⟨640+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0640 j
  by_cases h : i.1 < 768
  · let j : Fin 64 := ⟨i.1-704, by omega⟩
    have he : (⟨704+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0704 j
  by_cases h : i.1 < 832
  · let j : Fin 64 := ⟨i.1-768, by omega⟩
    have he : (⟨768+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0768 j
  by_cases h : i.1 < 896
  · let j : Fin 64 := ⟨i.1-832, by omega⟩
    have he : (⟨832+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0832 j
  by_cases h : i.1 < 960
  · let j : Fin 64 := ⟨i.1-896, by omega⟩
    have he : (⟨896+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0896 j
  by_cases h : i.1 < 1024
  · let j : Fin 64 := ⟨i.1-960, by omega⟩
    have he : (⟨960+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0960 j
  by_cases h : i.1 < 1088
  · let j : Fin 64 := ⟨i.1-1024, by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1024 j
  by_cases h : i.1 < 1152
  · let j : Fin 64 := ⟨i.1-1088, by omega⟩
    have he : (⟨1088+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1088 j
  by_cases h : i.1 < 1216
  · let j : Fin 64 := ⟨i.1-1152, by omega⟩
    have he : (⟨1152+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1152 j
  by_cases h : i.1 < 1280
  · let j : Fin 64 := ⟨i.1-1216, by omega⟩
    have he : (⟨1216+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1216 j
  by_cases h : i.1 < 1344
  · let j : Fin 64 := ⟨i.1-1280, by omega⟩
    have he : (⟨1280+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1280 j
  by_cases h : i.1 < 1408
  · let j : Fin 64 := ⟨i.1-1344, by omega⟩
    have he : (⟨1344+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1344 j
  by_cases h : i.1 < 1472
  · let j : Fin 64 := ⟨i.1-1408, by omega⟩
    have he : (⟨1408+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1408 j
  by_cases h : i.1 < 1536
  · let j : Fin 64 := ⟨i.1-1472, by omega⟩
    have he : (⟨1472+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1472 j
  by_cases h : i.1 < 1600
  · let j : Fin 64 := ⟨i.1-1536, by omega⟩
    have he : (⟨1536+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1536 j
  by_cases h : i.1 < 1664
  · let j : Fin 64 := ⟨i.1-1600, by omega⟩
    have he : (⟨1600+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1600 j
  by_cases h : i.1 < 1728
  · let j : Fin 64 := ⟨i.1-1664, by omega⟩
    have he : (⟨1664+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1664 j
  by_cases h : i.1 < 1792
  · let j : Fin 64 := ⟨i.1-1728, by omega⟩
    have he : (⟨1728+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1728 j
  by_cases h : i.1 < 1856
  · let j : Fin 64 := ⟨i.1-1792, by omega⟩
    have he : (⟨1792+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1792 j
  by_cases h : i.1 < 1920
  · let j : Fin 64 := ⟨i.1-1856, by omega⟩
    have he : (⟨1856+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1856 j
  by_cases h : i.1 < 1984
  · let j : Fin 64 := ⟨i.1-1920, by omega⟩
    have he : (⟨1920+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1920 j
  by_cases h : i.1 < 2048
  · let j : Fin 64 := ⟨i.1-1984, by omega⟩
    have he : (⟨1984+j.1, by omega⟩ : Fin 3632) = ⟨0+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1984 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas130
