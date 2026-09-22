import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_0512 : ∀ i : Fin 128,
    columnCheck ⟨512+i.1, by omega⟩ := by decide +kernel
private theorem checked_0640 : ∀ i : Fin 128,
    columnCheck ⟨640+i.1, by omega⟩ := by decide +kernel
private theorem checked_0768 : ∀ i : Fin 128,
    columnCheck ⟨768+i.1, by omega⟩ := by decide +kernel
private theorem checked_0896 : ∀ i : Fin 128,
    columnCheck ⟨896+i.1, by omega⟩ := by decide +kernel

theorem columns_0512 (i : Fin 512) : columnCheck ⟨512+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 5820) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0512 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨640+j.1, by omega⟩ : Fin 5820) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0640 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨768+j.1, by omega⟩ : Fin 5820) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0768 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨896+j.1, by omega⟩ : Fin 5820) = ⟨512+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_0896 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
