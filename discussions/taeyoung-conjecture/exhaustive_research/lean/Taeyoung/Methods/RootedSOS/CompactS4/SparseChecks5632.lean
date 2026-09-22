import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_5632 : ∀ i : Fin 128,
    columnCheck ⟨5632+i.1, by omega⟩ := by decide +kernel
private theorem checked_5760 : ∀ i : Fin 60,
    columnCheck ⟨5760+i.1, by omega⟩ := by decide +kernel

theorem columns_5632 (i : Fin 188) : columnCheck ⟨5632+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨5632+j.1, by omega⟩ : Fin 5820) = ⟨5632+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_5632 j
  by_cases h : i.1 < 188
  · let j : Fin 60 := ⟨i.1-(128), by omega⟩
    have he : (⟨5760+j.1, by omega⟩ : Fin 5820) = ⟨5632+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_5760 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
