import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_0512 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨512+i.1, by omega⟩ := by decide +kernel
private theorem check_0576 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨576+i.1, by omega⟩ := by decide +kernel
private theorem check_0640 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨640+i.1, by omega⟩ := by decide +kernel
private theorem check_0704 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨704+i.1, by omega⟩ := by decide +kernel
private theorem check_0768 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨768+i.1, by omega⟩ := by decide +kernel
private theorem check_0832 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨832+i.1, by omega⟩ := by decide +kernel
private theorem check_0896 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨896+i.1, by omega⟩ := by decide +kernel
private theorem check_0960 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨960+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_0512 (i : Fin 512) : Sparse.columnCheck ⟨512+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0512 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨576+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0576 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨640+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0640 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨704+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0704 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨768+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0768 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨832+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0832 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨896+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0896 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨960+j.1, by omega⟩ : Fin 3632) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_0960 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
