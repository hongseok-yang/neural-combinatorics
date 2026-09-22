import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block03Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block08Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Right
import Taeyoung.Methods.RootedSOS.CompactS4.FlatBlocks

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem blockRight3 (i j : Fin 30) (u : Fin 4) :
    right (blockIndex3 i j) u =
      if u.1 = 0 then 24*Block03.H i j
      else if u.1 = 1 then 24*(Block03.H i (30+j)+Block03.H (30+i) j)
      else if u.1 = 2 then 24*Block03.H (30+i) (30+j)
      else 24*Block08.H i j := by
  rw [((rightCheck_all (blockIndex3 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (blockIndex3 i j).1 < 1024 := by rw [blockIndex3_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex3 i j).1 < 3728 := by rw [blockIndex3_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex3 i j).1 < 4884 := by rw [blockIndex3_val]; omega
  rw [if_neg h2]
  have h3 : (blockIndex3 i j).1 < 5784 := by rw [blockIndex3_val]; omega
  rw [if_pos h3]
  have hi : ((blockIndex3 i j).1-4884)/30 = i.1 := by rw [blockIndex3_val]; omega
  have hj : ((blockIndex3 i j).1-4884)%30 = j.1 := by rw [blockIndex3_val]; omega
  dsimp only
  rw [hi,hj]

theorem blockSum3_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 30, ∑ j : Fin 30,
      ((right (blockIndex3 i j) 0 : Real)+(right (blockIndex3 i j) 1 : Real)*s+
        (right (blockIndex3 i j) 2 : Real)*s^2+
        (right (blockIndex3 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex3 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) := by
  have he : (∑ i : Fin 30, ∑ j : Fin 30,
      ((right (blockIndex3 i j) 0 : Real)+(right (blockIndex3 i j) 1 : Real)*s+
        (right (blockIndex3 i j) 2 : Real)*s^2+
        (right (blockIndex3 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex3 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W))) =
      24*Block03.density W s + 24*s*(1-s)*Block08.density W s := by
    simp only [Block03.density, Block08.density, Finset.mul_sum,
      ← Finset.sum_add_distrib, blockPulled3]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro g _
    have h0 := blockRight3 i j 0
    have h1 := blockRight3 i j 1
    have h2 := blockRight3 i j 2
    have h3 := blockRight3 i j 3
    norm_num at h0 h1 h2 h3 ⊢
    rw [h0,h1,h2,h3]
    push_cast
    ring
  rw [he]
  have h0 := Block03.density_nonneg W s
  have h1 := Block08.density_nonneg W s
  have hc : 0 ≤ 1-s := by linarith
  positivity

#print axioms blockSum3_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas118
