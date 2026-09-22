import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_4608 : ∀ i : Fin 128,
    columnCheck ⟨4608+i.1, by omega⟩ := by decide +kernel
private theorem checked_4736 : ∀ i : Fin 128,
    columnCheck ⟨4736+i.1, by omega⟩ := by decide +kernel
private theorem checked_4864 : ∀ i : Fin 128,
    columnCheck ⟨4864+i.1, by omega⟩ := by decide +kernel
private theorem checked_4992 : ∀ i : Fin 128,
    columnCheck ⟨4992+i.1, by omega⟩ := by decide +kernel

theorem columns_4608 (i : Fin 512) : columnCheck ⟨4608+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨4608+j.1, by omega⟩ : Fin 5820) = ⟨4608+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4608 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨4736+j.1, by omega⟩ : Fin 5820) = ⟨4608+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4736 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨4864+j.1, by omega⟩ : Fin 5820) = ⟨4608+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4864 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨4992+j.1, by omega⟩ : Fin 5820) = ⟨4608+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4992 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
