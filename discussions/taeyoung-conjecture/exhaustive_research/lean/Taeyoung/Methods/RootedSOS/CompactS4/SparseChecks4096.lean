import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_4096 : ∀ i : Fin 128,
    columnCheck ⟨4096+i.1, by omega⟩ := by decide +kernel
private theorem checked_4224 : ∀ i : Fin 128,
    columnCheck ⟨4224+i.1, by omega⟩ := by decide +kernel
private theorem checked_4352 : ∀ i : Fin 128,
    columnCheck ⟨4352+i.1, by omega⟩ := by decide +kernel
private theorem checked_4480 : ∀ i : Fin 128,
    columnCheck ⟨4480+i.1, by omega⟩ := by decide +kernel

theorem columns_4096 (i : Fin 512) : columnCheck ⟨4096+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨4096+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4096 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨4224+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4224 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨4352+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4352 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨4480+j.1, by omega⟩ : Fin 5820) = ⟨4096+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_4480 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
