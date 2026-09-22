import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_3072 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3072+i.1, by omega⟩ := by decide +kernel
private theorem check_3136 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3136+i.1, by omega⟩ := by decide +kernel
private theorem check_3200 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3200+i.1, by omega⟩ := by decide +kernel
private theorem check_3264 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3264+i.1, by omega⟩ := by decide +kernel
private theorem check_3328 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3328+i.1, by omega⟩ := by decide +kernel
private theorem check_3392 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3392+i.1, by omega⟩ := by decide +kernel
private theorem check_3456 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3456+i.1, by omega⟩ := by decide +kernel
private theorem check_3520 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3520+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_3072 (i : Fin 512) : Sparse.columnCheck ⟨3072+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3072 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨3136+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3136 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨3200+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3200 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨3264+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3264 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨3328+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3328 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨3392+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3392 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨3456+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3456 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨3520+j.1, by omega⟩ : Fin 3632) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3520 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
