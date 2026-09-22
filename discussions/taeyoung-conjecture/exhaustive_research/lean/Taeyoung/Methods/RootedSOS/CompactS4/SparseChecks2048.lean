import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_2048 : ∀ i : Fin 128,
    columnCheck ⟨2048+i.1, by omega⟩ := by decide +kernel
private theorem checked_2176 : ∀ i : Fin 128,
    columnCheck ⟨2176+i.1, by omega⟩ := by decide +kernel
private theorem checked_2304 : ∀ i : Fin 128,
    columnCheck ⟨2304+i.1, by omega⟩ := by decide +kernel
private theorem checked_2432 : ∀ i : Fin 128,
    columnCheck ⟨2432+i.1, by omega⟩ := by decide +kernel

theorem columns_2048 (i : Fin 512) : columnCheck ⟨2048+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨2048+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2048 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨2176+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2176 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨2304+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2304 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨2432+j.1, by omega⟩ : Fin 5820) = ⟨2048+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2432 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
