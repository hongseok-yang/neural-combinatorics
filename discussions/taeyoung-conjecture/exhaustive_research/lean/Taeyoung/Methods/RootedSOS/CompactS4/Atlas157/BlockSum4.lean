import Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block04Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block09Density
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Right
import Taeyoung.Methods.RootedSOS.CompactS4.FlatBlocks

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas157
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem blockRight4 (i j : Fin 6) (u : Fin 4) :
    right (blockIndex4 i j) u =
      if u.1 = 0 then 24*Block04.H i j
      else if u.1 = 1 then 24*(Block04.H i (6+j)+Block04.H (6+i) j)
      else if u.1 = 2 then 24*Block04.H (6+i) (6+j)
      else 24*Block09.H i j := by
  rw [((rightCheck_all (blockIndex4 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (blockIndex4 i j).1 < 1024 := by rw [blockIndex4_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex4 i j).1 < 3728 := by rw [blockIndex4_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex4 i j).1 < 4884 := by rw [blockIndex4_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex4 i j).1 < 5784 := by rw [blockIndex4_val]; omega
  rw [if_neg h3]
  have hi : ((blockIndex4 i j).1-5784)/6 = i.1 := by rw [blockIndex4_val]; omega
  have hj : ((blockIndex4 i j).1-5784)%6 = j.1 := by rw [blockIndex4_val]; omega
  dsimp only
  rw [hi,hj]

theorem blockSum4_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 6, ∑ j : Fin 6,
      ((right (blockIndex4 i j) 0 : Real)+(right (blockIndex4 i j) 1 : Real)*s+
        (right (blockIndex4 i j) 2 : Real)*s^2+
        (right (blockIndex4 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex4 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) := by
  have he : (∑ i : Fin 6, ∑ j : Fin 6,
      ((right (blockIndex4 i j) 0 : Real)+(right (blockIndex4 i j) 1 : Real)*s+
        (right (blockIndex4 i j) 2 : Real)*s^2+
        (right (blockIndex4 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex4 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W))) =
      24*Block04.density W s + 24*s*(1-s)*Block09.density W s := by
    simp only [Block04.density, Block09.density, Finset.mul_sum,
      ← Finset.sum_add_distrib, blockPulled4]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro g _
    have h0 := blockRight4 i j 0
    have h1 := blockRight4 i j 1
    have h2 := blockRight4 i j 2
    have h3 := blockRight4 i j 3
    norm_num at h0 h1 h2 h3 ⊢
    rw [h0,h1,h2,h3]
    push_cast
    ring
  rw [he]
  have h0 := Block04.density_nonneg W s
  have h1 := Block09.density_nonneg W s
  have hc : 0 ≤ 1-s := by linarith
  positivity

#print axioms blockSum4_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas157
