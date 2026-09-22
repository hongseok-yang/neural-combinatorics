import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_3072 : ∀ i : Fin 128,
    columnCheck ⟨3072+i.1, by omega⟩ := by decide +kernel
private theorem checked_3200 : ∀ i : Fin 128,
    columnCheck ⟨3200+i.1, by omega⟩ := by decide +kernel
private theorem checked_3328 : ∀ i : Fin 128,
    columnCheck ⟨3328+i.1, by omega⟩ := by decide +kernel
private theorem checked_3456 : ∀ i : Fin 128,
    columnCheck ⟨3456+i.1, by omega⟩ := by decide +kernel

theorem columns_3072 (i : Fin 512) : columnCheck ⟨3072+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3072 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨3200+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3200 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨3328+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3328 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨3456+j.1, by omega⟩ : Fin 5820) = ⟨3072+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3456 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
