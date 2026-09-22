import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private theorem check_3584 : ∀ i : Fin 48,
    Sparse.columnCheck ⟨3584+i.1, by omega⟩ := by decide +kernel
theorem SparseChecks_3584 (i : Fin 48) : Sparse.columnCheck ⟨3584+i.1, by omega⟩ := by
  by_cases h : i.1 < 48
  · let j : Fin 48 := ⟨i.1-0, by omega⟩
    have he : (⟨3584+j.1, by omega⟩ : Fin 3632) = ⟨3584+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_3584 j
  omega
end Taeyoung.Methods.RootedSOS.Induced.Six
