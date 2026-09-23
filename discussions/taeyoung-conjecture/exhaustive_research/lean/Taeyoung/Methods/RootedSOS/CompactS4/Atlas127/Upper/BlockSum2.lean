import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block02
import Taeyoung.Methods.RootedSOS.CompactS4.Young22
import Taeyoung.Methods.RootedSOS.MatrixFlagDensity
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block07
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.FlatBlocks

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block02
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def density (W : Taeyoung.Graphon Ω μ) (s : Real) : Real :=
  ∑ i : Fin 34, ∑ j : Fin 34, ((H i j : Real) + ((H i (34+j) : Real)+(H (34+i) j : Real))*s + (H (34+i) (34+j) : Real)*s^2) *
    (∑ g : Fin 143, (Young22.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W))

theorem density_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real) : 0 ≤ density W s := by
  have h := integer_flag_density_nonneg (order := 2) (n := 62)
    S4Flags.flagLabelGraph S4Flags.flagBranchNeighbors
    (fun a i => (Young22.TInt a i : Real))
    (fun ui k => N (finProdFinEquiv ui) k) (fun i j => G i j)
    (fun ui vj => H (finProdFinEquiv ui) (finProdFinEquiv vj))
    gram_nonneg (fun a b => expanded_entries_exact (finProdFinEquiv a) (finProdFinEquiv b)) W s
  change 0 ≤ ∑ ui : Fin 2 × Fin 34, ∑ vj : Fin 2 × Fin 34,
    (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) * s^(ui.1.1+vj.1.1) *
      (∑ a : Fin 352, ∑ b : Fin 352,
        (Young22.TInt a ui.2 : Real)*(Young22.TInt b vj.2 : Real)*
          Taeyoung.homDensity (S4Flags.gluedGraph a b) W) at h
  simp_rw [Young22.pair_basis_density] at h
  rw [two_layer_sum H
    (fun i j : Fin 34 => ∑ g : Fin 143, (Young22.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) s] at h
  exact h

#print axioms density_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block02

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block07
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def density (W : Taeyoung.Graphon Ω μ) (s : Real) : Real :=
  ∑ i : Fin 34, ∑ j : Fin 34, ((H i j : Real)) *
    (∑ g : Fin 143, (Young22.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W))

theorem density_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real) : 0 ≤ density W s := by
  have h := integer_flag_density_nonneg (order := 1) (n := 30)
    S4Flags.flagLabelGraph S4Flags.flagBranchNeighbors
    (fun a i => (Young22.TInt a i : Real))
    (fun ui k => N (finProdFinEquiv ui) k) (fun i j => G i j)
    (fun ui vj => H (finProdFinEquiv ui) (finProdFinEquiv vj))
    gram_nonneg (fun a b => expanded_entries_exact (finProdFinEquiv a) (finProdFinEquiv b)) W s
  change 0 ≤ ∑ ui : Fin 1 × Fin 34, ∑ vj : Fin 1 × Fin 34,
    (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) * s^(ui.1.1+vj.1.1) *
      (∑ a : Fin 352, ∑ b : Fin 352,
        (Young22.TInt a ui.2 : Real)*(Young22.TInt b vj.2 : Real)*
          Taeyoung.homDensity (S4Flags.gluedGraph a b) W) at h
  simp_rw [Young22.pair_basis_density] at h
  rw [one_layer_sum H
    (fun i j : Fin 34 => ∑ g : Fin 143, (Young22.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) s] at h
  exact h

#print axioms density_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block07

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper
