import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block01
import Taeyoung.Methods.RootedSOS.CompactS4.Young31
import Taeyoung.Methods.RootedSOS.MatrixFlagDensity
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block06
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Right
import Taeyoung.Methods.RootedSOS.CompactS4.FlatBlocks

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block01
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def density (W : Taeyoung.Graphon Ω μ) (s : Real) : Real :=
  ∑ i : Fin 52, ∑ j : Fin 52, ((H i j : Real) + ((H i (52+j) : Real)+(H (52+i) j : Real))*s + (H (52+i) (52+j) : Real)*s^2) *
    (∑ g : Fin 143, (Young31.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W))

theorem density_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real) : 0 ≤ density W s := by
  have h := integer_flag_density_nonneg (order := 2) (n := 98)
    S4Flags.flagLabelGraph S4Flags.flagBranchNeighbors
    (fun a i => (Young31.TInt a i : Real))
    (fun ui k => N (finProdFinEquiv ui) k) (fun i j => G i j)
    (fun ui vj => H (finProdFinEquiv ui) (finProdFinEquiv vj))
    gram_nonneg (fun a b => expanded_entries_exact (finProdFinEquiv a) (finProdFinEquiv b)) W s
  change 0 ≤ ∑ ui : Fin 2 × Fin 52, ∑ vj : Fin 2 × Fin 52,
    (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) * s^(ui.1.1+vj.1.1) *
      (∑ a : Fin 352, ∑ b : Fin 352,
        (Young31.TInt a ui.2 : Real)*(Young31.TInt b vj.2 : Real)*
          Taeyoung.homDensity (S4Flags.gluedGraph a b) W) at h
  simp_rw [Young31.pair_basis_density] at h
  rw [two_layer_sum H
    (fun i j : Fin 52 => ∑ g : Fin 143, (Young31.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) s] at h
  exact h

#print axioms density_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block01

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block06
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def density (W : Taeyoung.Graphon Ω μ) (s : Real) : Real :=
  ∑ i : Fin 52, ∑ j : Fin 52, ((H i j : Real)) *
    (∑ g : Fin 143, (Young31.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W))

theorem density_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real) : 0 ≤ density W s := by
  have h := integer_flag_density_nonneg (order := 1) (n := 48)
    S4Flags.flagLabelGraph S4Flags.flagBranchNeighbors
    (fun a i => (Young31.TInt a i : Real))
    (fun ui k => N (finProdFinEquiv ui) k) (fun i j => G i j)
    (fun ui vj => H (finProdFinEquiv ui) (finProdFinEquiv vj))
    gram_nonneg (fun a b => expanded_entries_exact (finProdFinEquiv a) (finProdFinEquiv b)) W s
  change 0 ≤ ∑ ui : Fin 1 × Fin 52, ∑ vj : Fin 1 × Fin 52,
    (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) * s^(ui.1.1+vj.1.1) *
      (∑ a : Fin 352, ∑ b : Fin 352,
        (Young31.TInt a ui.2 : Real)*(Young31.TInt b vj.2 : Real)*
          Taeyoung.homDensity (S4Flags.gluedGraph a b) W) at h
  simp_rw [Young31.pair_basis_density] at h
  rw [one_layer_sum H
    (fun i j : Fin 52 => ∑ g : Fin 143, (Young31.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) s] at h
  exact h

#print axioms density_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block06

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
open Finset MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem blockRight1 (i j : Fin 52) (u : Fin 4) :
    right (blockIndex1 i j) u =
      if u.1 = 0 then 24*Block01.H i j
      else if u.1 = 1 then 24*(Block01.H i (52+j)+Block01.H (52+i) j)
      else if u.1 = 2 then 24*Block01.H (52+i) (52+j)
      else 24*Block06.H i j := by
  rw [((rightCheck_all (blockIndex1 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (blockIndex1 i j).1 < 1024 := by rw [blockIndex1_val]; omega
  rw [if_neg h0]
  have h1 : (blockIndex1 i j).1 < 3728 := by rw [blockIndex1_val]; omega
  rw [if_pos h1]
  have hi : ((blockIndex1 i j).1-1024)/52 = i.1 := by rw [blockIndex1_val]; omega
  have hj : ((blockIndex1 i j).1-1024)%52 = j.1 := by rw [blockIndex1_val]; omega
  dsimp only
  rw [hi,hj]

theorem blockSum1_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 52, ∑ j : Fin 52,
      ((right (blockIndex1 i j) 0 : Real)+(right (blockIndex1 i j) 1 : Real)*s+
        (right (blockIndex1 i j) 2 : Real)*s^2+
        (right (blockIndex1 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex1 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) := by
  have he : (∑ i : Fin 52, ∑ j : Fin 52,
      ((right (blockIndex1 i j) 0 : Real)+(right (blockIndex1 i j) 1 : Real)*s+
        (right (blockIndex1 i j) 2 : Real)*s^2+
        (right (blockIndex1 i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex1 i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W))) =
      24*Block01.density W s + 24*s*(1-s)*Block06.density W s := by
    simp only [Block01.density, Block06.density, Finset.mul_sum,
      ← Finset.sum_add_distrib, blockPulled1]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro g _
    have h0 := blockRight1 i j 0
    have h1 := blockRight1 i j 1
    have h2 := blockRight1 i j 2
    have h3 := blockRight1 i j 3
    norm_num at h0 h1 h2 h3 ⊢
    rw [h0,h1,h2,h3]
    push_cast
    ring
  rw [he]
  have h0 := Block01.density_nonneg W s
  have h1 := Block06.density_nonneg W s
  have hc : 0 ≤ 1-s := by linarith
  positivity

#print axioms blockSum1_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper
