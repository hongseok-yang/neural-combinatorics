import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_2560 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2560+i.1, by omega⟩ := by decide +kernel
private theorem check_2624 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2624+i.1, by omega⟩ := by decide +kernel
private theorem check_2688 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2688+i.1, by omega⟩ := by decide +kernel
private theorem check_2752 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2752+i.1, by omega⟩ := by decide +kernel
private theorem check_2816 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2816+i.1, by omega⟩ := by decide +kernel
private theorem check_2880 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2880+i.1, by omega⟩ := by decide +kernel
private theorem check_2944 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨2944+i.1, by omega⟩ := by decide +kernel
private theorem check_3008 : ∀ i : Fin 64,
    Sparse.columnCheck ⟨3008+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_2560 (i : Fin 512) : Sparse.columnCheck ⟨2560+i.1, by omega⟩ := by
  by_cases h : i.1 < 64
  · let j : Fin 64 := ⟨i.1-0, by omega⟩
    have he : (⟨2560+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2560 j
  by_cases h : i.1 < 128
  · let j : Fin 64 := ⟨i.1-64, by omega⟩
    have he : (⟨2624+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2624 j
  by_cases h : i.1 < 192
  · let j : Fin 64 := ⟨i.1-128, by omega⟩
    have he : (⟨2688+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2688 j
  by_cases h : i.1 < 256
  · let j : Fin 64 := ⟨i.1-192, by omega⟩
    have he : (⟨2752+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2752 j
  by_cases h : i.1 < 320
  · let j : Fin 64 := ⟨i.1-256, by omega⟩
    have he : (⟨2816+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2816 j
  by_cases h : i.1 < 384
  · let j : Fin 64 := ⟨i.1-320, by omega⟩
    have he : (⟨2880+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2880 j
  by_cases h : i.1 < 448
  · let j : Fin 64 := ⟨i.1-384, by omega⟩
    have he : (⟨2944+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_2944 j
  by_cases h : i.1 < 512
  · let j : Fin 64 := ⟨i.1-448, by omega⟩
    have he : (⟨3008+j.1, by omega⟩ : Fin 3632) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3008 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
