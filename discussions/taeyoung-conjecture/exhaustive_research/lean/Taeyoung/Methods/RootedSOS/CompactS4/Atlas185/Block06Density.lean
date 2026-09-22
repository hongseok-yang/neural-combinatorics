import Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Block06PSD
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Block06Expansion
import Taeyoung.Methods.RootedSOS.CompactS4.Young31
import Taeyoung.Methods.RootedSOS.MatrixFlagDensity

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Block06
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Block06
