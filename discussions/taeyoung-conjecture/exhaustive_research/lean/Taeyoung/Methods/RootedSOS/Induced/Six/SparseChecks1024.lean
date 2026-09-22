import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_1024 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1024+i.1, by omega⟩ := by decide +kernel
private theorem check_1088 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1088+i.1, by omega⟩ := by decide +kernel
private theorem check_1152 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1152+i.1, by omega⟩ := by decide +kernel
private theorem check_1216 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1216+i.1, by omega⟩ := by decide +kernel
private theorem check_1280 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1280+i.1, by omega⟩ := by decide +kernel
private theorem check_1344 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1344+i.1, by omega⟩ := by decide +kernel
private theorem check_1408 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1408+i.1, by omega⟩ := by decide +kernel
private theorem check_1472 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1472+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_1024 (i : Fin 512) : Sparse.columnCheck ⟨1024+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1024 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨1088+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1088 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨1152+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1152 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨1216+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1216 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨1280+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1280 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨1344+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1344 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨1408+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1408 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨1472+j.1, by omega⟩ : Fin 3632) = ⟨1024+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1472 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
