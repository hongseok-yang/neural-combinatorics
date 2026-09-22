import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block00Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block05Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Right
import Taeyoung.Methods.RootedSOS.CompactS4.FlatBlocks

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas169
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem blockRight0 (i j : Fin 32) (u : Fin 4) :
    right (blockIndex0 i j) u =
      if u.1 = 0 then 24*Block00.H i j
      else if u.1 = 1 then 24*(Block00.H i (32+j)+Block00.H (32+i) j)
      else if u.1 = 2 then 24*Block00.H (32+i) (32+j)
      else 24*Block05.H i j := by
  rw [((rightCheck_all (blockIndex0 i j)).1 u).2]
  unfold expandedRight
  have h0 : (blockIndex0 i j).1 < 1024 := by rw [blockIndex0_val]; omega
  rw [if_pos h0]
  have hi : ((blockIndex0 i j).1-0)/32 = i.1 := by rw [blockIndex0_val]; omega
  have hj : ((blockIndex0 i j).1-0)%32 = j.1 := by rw [blockIndex0_val]; omega
  dsimp only
  rw [hi,hj]

theorem blockSum0_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 32, ∑ j : Fin 32,
      ((right (blockIndex0 i j) 0 : Real)+(right (blockIndex0 i j) 1 : Real)*s+
        (right (blockIndex0 i j) 2 : Real)*s^2+
        (right (blockIndex0 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex0 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) := by
  have he : (∑ i : Fin 32, ∑ j : Fin 32,
      ((right (blockIndex0 i j) 0 : Real)+(right (blockIndex0 i j) 1 : Real)*s+
        (right (blockIndex0 i j) 2 : Real)*s^2+
        (right (blockIndex0 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex0 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W))) =
      24*Block00.density W s + 24*s*(1-s)*Block05.density W s := by
    simp only [Block00.density, Block05.density, Finset.mul_sum,
      ← Finset.sum_add_distrib, blockPulled0]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro g _
    have h0 := blockRight0 i j 0
    have h1 := blockRight0 i j 1
    have h2 := blockRight0 i j 2
    have h3 := blockRight0 i j 3
    norm_num at h0 h1 h2 h3 ⊢
    rw [h0,h1,h2,h3]
    push_cast
    ring
  rw [he]
  have h0 := Block00.density_nonneg W s
  have h1 := Block05.density_nonneg W s
  have hc : 0 ≤ 1-s := by linarith
  positivity

#print axioms blockSum0_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas169
