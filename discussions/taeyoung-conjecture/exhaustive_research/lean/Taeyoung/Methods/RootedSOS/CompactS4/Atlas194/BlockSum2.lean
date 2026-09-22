import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block02Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block07Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Right
import Taeyoung.Methods.RootedSOS.CompactS4.FlatBlocks

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas194
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem blockRight2 (i j : Fin 34) (u : Fin 4) :
    right (blockIndex2 i j) u =
      if u.1 = 0 then 24*Block02.H i j
      else if u.1 = 1 then 24*(Block02.H i (34+j)+Block02.H (34+i) j)
      else if u.1 = 2 then 24*Block02.H (34+i) (34+j)
      else 24*Block07.H i j := by
  rw [((rightCheck_all (blockIndex2 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (blockIndex2 i j).1 < 1024 := by rw [blockIndex2_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex2 i j).1 < 3728 := by rw [blockIndex2_val]; omega
  rw [if_neg h1]
  have h2 : (blockIndex2 i j).1 < 4884 := by rw [blockIndex2_val]; omega
  rw [if_pos h2]
  have hi : ((blockIndex2 i j).1-3728)/34 = i.1 := by rw [blockIndex2_val]; omega
  have hj : ((blockIndex2 i j).1-3728)%34 = j.1 := by rw [blockIndex2_val]; omega
  dsimp only
  rw [hi,hj]

theorem blockSum2_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 34, ∑ j : Fin 34,
      ((right (blockIndex2 i j) 0 : Real)+(right (blockIndex2 i j) 1 : Real)*s+
        (right (blockIndex2 i j) 2 : Real)*s^2+
        (right (blockIndex2 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex2 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) := by
  have he : (∑ i : Fin 34, ∑ j : Fin 34,
      ((right (blockIndex2 i j) 0 : Real)+(right (blockIndex2 i j) 1 : Real)*s+
        (right (blockIndex2 i j) 2 : Real)*s^2+
        (right (blockIndex2 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex2 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W))) =
      24*Block02.density W s + 24*s*(1-s)*Block07.density W s := by
    simp only [Block02.density, Block07.density, Finset.mul_sum,
      ← Finset.sum_add_distrib, blockPulled2]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro g _
    have h0 := blockRight2 i j 0
    have h1 := blockRight2 i j 1
    have h2 := blockRight2 i j 2
    have h3 := blockRight2 i j 3
    norm_num at h0 h1 h2 h3 ⊢
    rw [h0,h1,h2,h3]
    push_cast
    ring
  rw [he]
  have h0 := Block02.density_nonneg W s
  have h1 := Block07.density_nonneg W s
  have hc : 0 ≤ 1-s := by linarith
  positivity

#print axioms blockSum2_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas194
