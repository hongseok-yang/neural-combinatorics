import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_2048 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2048+i.1, by omega⟩ := by decide +kernel
private theorem check_2112 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2112+i.1, by omega⟩ := by decide +kernel
private theorem check_2176 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2176+i.1, by omega⟩ := by decide +kernel
private theorem check_2240 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2240+i.1, by omega⟩ := by decide +kernel
private theorem check_2304 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2304+i.1, by omega⟩ := by decide +kernel
private theorem check_2368 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2368+i.1, by omega⟩ := by decide +kernel
private theorem check_2432 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2432+i.1, by omega⟩ := by decide +kernel
private theorem check_2496 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2496+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_2048 (i : Fin 512) : Sparse.columnCheck ⟨2048+i.1, by omega⟩ := by
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
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
