import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_3584 : ∀ i : Fin 128,
    columnCheck ⟨3584+i.1, by omega⟩ := by decide +kernel
private theorem checked_3712 : ∀ i : Fin 128,
    columnCheck ⟨3712+i.1, by omega⟩ := by decide +kernel
private theorem checked_3840 : ∀ i : Fin 128,
    columnCheck ⟨3840+i.1, by omega⟩ := by decide +kernel
private theorem checked_3968 : ∀ i : Fin 128,
    columnCheck ⟨3968+i.1, by omega⟩ := by decide +kernel

theorem columns_3584 (i : Fin 512) : columnCheck ⟨3584+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨3584+j.1, by omega⟩ : Fin 5820) = ⟨3584+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3584 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨3712+j.1, by omega⟩ : Fin 5820) = ⟨3584+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3712 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨3840+j.1, by omega⟩ : Fin 5820) = ⟨3584+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3840 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨3968+j.1, by omega⟩ : Fin 5820) = ⟨3584+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_3968 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
