import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_1536 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1536+i.1, by omega⟩ := by decide +kernel
private theorem check_1600 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1600+i.1, by omega⟩ := by decide +kernel
private theorem check_1664 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1664+i.1, by omega⟩ := by decide +kernel
private theorem check_1728 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1728+i.1, by omega⟩ := by decide +kernel
private theorem check_1792 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1792+i.1, by omega⟩ := by decide +kernel
private theorem check_1856 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1856+i.1, by omega⟩ := by decide +kernel
private theorem check_1920 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1920+i.1, by omega⟩ := by decide +kernel
private theorem check_1984 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨1984+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_1536 (i : Fin 512) : Sparse.columnCheck ⟨1536+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨1536+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1536 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨1600+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1600 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨1664+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1664 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨1728+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1728 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨1792+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1792 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨1856+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1856 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨1920+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1920 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨1984+j.1, by omega⟩ : Fin 3632) = ⟨1536+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_1984 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
