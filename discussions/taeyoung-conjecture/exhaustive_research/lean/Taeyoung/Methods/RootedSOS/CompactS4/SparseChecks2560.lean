import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem checked_2560 : ∀ i : Fin 128,
    columnCheck ⟨2560+i.1, by omega⟩ := by decide +kernel
private theorem checked_2688 : ∀ i : Fin 128,
    columnCheck ⟨2688+i.1, by omega⟩ := by decide +kernel
private theorem checked_2816 : ∀ i : Fin 128,
    columnCheck ⟨2816+i.1, by omega⟩ := by decide +kernel
private theorem checked_2944 : ∀ i : Fin 128,
    columnCheck ⟨2944+i.1, by omega⟩ := by decide +kernel

theorem columns_2560 (i : Fin 512) : columnCheck ⟨2560+i.1, by omega⟩ := by
  by_cases h : i.1 < 128
  · let j : Fin 128 := ⟨i.1-(0), by omega⟩
    have he : (⟨2560+j.1, by omega⟩ : Fin 5820) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2560 j
  by_cases h : i.1 < 256
  · let j : Fin 128 := ⟨i.1-(128), by omega⟩
    have he : (⟨2688+j.1, by omega⟩ : Fin 5820) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2688 j
  by_cases h : i.1 < 384
  · let j : Fin 128 := ⟨i.1-(256), by omega⟩
    have he : (⟨2816+j.1, by omega⟩ : Fin 5820) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2816 j
  by_cases h : i.1 < 512
  · let j : Fin 128 := ⟨i.1-(384), by omega⟩
    have he : (⟨2944+j.1, by omega⟩ : Fin 5820) = ⟨2560+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_2944 j
  omega
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
