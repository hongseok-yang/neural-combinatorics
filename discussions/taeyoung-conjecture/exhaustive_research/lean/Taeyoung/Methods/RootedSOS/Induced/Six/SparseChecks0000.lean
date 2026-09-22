import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0000 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨0+i.1, by omega⟩ := by decide +kernel
private theorem check_0064 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨64+i.1, by omega⟩ := by decide +kernel
private theorem check_0128 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨128+i.1, by omega⟩ := by decide +kernel
private theorem check_0192 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨192+i.1, by omega⟩ := by decide +kernel
private theorem check_0256 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨256+i.1, by omega⟩ := by decide +kernel
private theorem check_0320 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨320+i.1, by omega⟩ := by decide +kernel
private theorem check_0384 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨384+i.1, by omega⟩ := by decide +kernel
private theorem check_0448 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨448+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_0000 (i : Fin 512) : Sparse.columnCheck ⟨0+i.1, by omega⟩ := by
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
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
