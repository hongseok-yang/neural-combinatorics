import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0000
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0013
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0026
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0039
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0052
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0065
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0078
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0091
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0104
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0117
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.ContractionChecks0130
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
theorem contractionCheck_all (k : Fin 143) : contractionCheck k := by
  by_cases h : k.1 < 13
  · let j : Fin 13 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0000 j
  by_cases h : k.1 < 26
  · let j : Fin 13 := ⟨k.1-13, by omega⟩
    have he : (⟨13+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0013 j
  by_cases h : k.1 < 39
  · let j : Fin 13 := ⟨k.1-26, by omega⟩
    have he : (⟨26+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0026 j
  by_cases h : k.1 < 52
  · let j : Fin 13 := ⟨k.1-39, by omega⟩
    have he : (⟨39+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0039 j
  by_cases h : k.1 < 65
  · let j : Fin 13 := ⟨k.1-52, by omega⟩
    have he : (⟨52+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0052 j
  by_cases h : k.1 < 78
  · let j : Fin 13 := ⟨k.1-65, by omega⟩
    have he : (⟨65+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0065 j
  by_cases h : k.1 < 91
  · let j : Fin 13 := ⟨k.1-78, by omega⟩
    have he : (⟨78+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0078 j
  by_cases h : k.1 < 104
  · let j : Fin 13 := ⟨k.1-91, by omega⟩
    have he : (⟨91+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0091 j
  by_cases h : k.1 < 117
  · let j : Fin 13 := ⟨k.1-104, by omega⟩
    have he : (⟨104+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0104 j
  by_cases h : k.1 < 130
  · let j : Fin 13 := ⟨k.1-117, by omega⟩
    have he : (⟨117+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0117 j
  by_cases h : k.1 < 143
  · let j : Fin 13 := ⟨k.1-130, by omega⟩
    have he : (⟨130+j.1, by omega⟩ : Fin 143) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using ContractionChecks_0130 j
  omega

theorem groupTotal_exact (g : Fin 143) (u : Fin 4) :
    groupTotal g u = ∑ k : Fin 5820, Sparse.pulled g k * right k u := by
  have h := packed_rect_product_exact
    (fun i j => Sparse.pulled ⟨i%143,Nat.mod_lt _ (by decide)⟩ ⟨j%5820,Nat.mod_lt _ (by decide)⟩)
    right groupTotal 576 189427751138304 635022438695959265280 1270044877391918530561 rightEncoded
    (by
      intro i j
      exact decodeSignedDigit_bound (by decide) (Sparse.flatCode _) _)
    (fun k u => ((rightCheck_all k).1 u).1)
    (fun g u => (contractionCheck_all g).1 u)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun k => (rightCheck_all k).2)
    (by
      intro g
      have hoff : (635022438695959265280 : Int) * geometricEncoding 1270044877391918530561 4 = 1300907066918656587330794077728380750873068646131675453746682922228767288141330513920 := by decide +kernel
      simp only [Nat.cast_ofNat, Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)]
      rw [hoff, Sparse.contraction]
      exact (contractionCheck_all g).2)
    g u
  simpa only [Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)] using h

#print axioms groupTotal_exact
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
