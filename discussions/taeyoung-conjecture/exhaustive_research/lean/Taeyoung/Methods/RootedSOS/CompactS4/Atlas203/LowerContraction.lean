import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.LowerContractionChecks0000
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.LowerContractionChecks0052
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.LowerContractionChecks0104
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
theorem Lower.contractionCheck_all (k : Fin 156) : Lower.contractionCheck k := by
  by_cases h : k.1 < 52
  · let j : Fin 52 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using LowerContractionChecks_0000 j
  by_cases h : k.1 < 104
  · let j : Fin 52 := ⟨k.1-52, by omega⟩
    have he : (⟨52+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using LowerContractionChecks_0052 j
  by_cases h : k.1 < 156
  · let j : Fin 52 := ⟨k.1-104, by omega⟩
    have he : (⟨104+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using LowerContractionChecks_0104 j
  omega

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Lower
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
theorem groupTotal_exact (g : Fin 156) (u : Fin 3) :
    groupTotal g u = ∑ k : Fin 3632, Induced.Six.Sparse.pulled g k*right k u := by
  have h := packed_rect_product_exact
    (fun i j => Induced.Six.Sparse.pulled ⟨i%156,Nat.mod_lt _ (by decide)⟩ ⟨j%3632,Nat.mod_lt _ (by decide)⟩)
    right groupTotal 32768 3722556762000188481484800 443034047597270943817819540684800 886068095194541887635639081369601 rightEncoded
    (by
      intro i j
      exact decodeSignedDigit_bound (by decide) (Induced.Six.Sparse.flatCode _) _)
    (fun k u => ((rightCheck_all k).1 u).1)
    (fun g u => (contractionCheck_all g).1 u)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun k => (rightCheck_all k).2)
    (by
      intro g
      have hoff : (443034047597270943817819540684800 : Int)*geometricEncoding 886068095194541887635639081369601 3 = 347833415845673668311746068275639638767741768237322866557409982489128847172129696243318065096294400 := by decide +kernel
      simp only [Nat.cast_ofNat, Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)]
      rw [hoff, Induced.Six.Sparse.contraction]
      exact (contractionCheck_all g).2)
    g u
  simpa only [Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)] using h
#print axioms groupTotal_exact
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Lower
