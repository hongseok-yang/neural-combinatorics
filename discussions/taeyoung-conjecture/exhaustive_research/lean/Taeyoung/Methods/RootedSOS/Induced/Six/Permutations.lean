import Taeyoung.Methods.RootedSOS.Induced.Six.PermutationChecks0000
import Taeyoung.Methods.RootedSOS.Induced.Six.PermutationChecks0240
import Taeyoung.Methods.RootedSOS.Induced.Six.PermutationChecks0480
namespace Taeyoung.Methods.RootedSOS.Induced.Six
theorem permutationCheck_all (k : Fin 720) : permutationCheck k := by
  by_cases h : k.1 < 240
  · let j : Fin 240 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 720) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using PermutationChecks_0000 j
  by_cases h : k.1 < 480
  · let j : Fin 240 := ⟨k.1-240, by omega⟩
    have he : (⟨240+j.1, by omega⟩ : Fin 720) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using PermutationChecks_0240 j
  by_cases h : k.1 < 720
  · let j : Fin 240 := ⟨k.1-480, by omega⟩
    have he : (⟨480+j.1, by omega⟩ : Fin 720) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using PermutationChecks_0480 j
  omega

def vertexEquiv (p : Fin 720) : Fin 6 ≃ Fin 6 where
  toFun := vertex p
  invFun := vertex (inverse p)
  left_inv i := ((permutationCheck_all p).1 i).1
  right_inv i := ((permutationCheck_all p).1 i).2
def edgeEquiv (p : Fin 720) : Fin 15 ≃ Fin 15 where
  toFun := edge p
  invFun := edge (inverse p)
  left_inv i := ((permutationCheck_all p).2.1 i).1
  right_inv i := ((permutationCheck_all p).2.1 i).2
end Taeyoung.Methods.RootedSOS.Induced.Six
