import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block02PSD
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block02Expansion
import Taeyoung.Methods.RootedSOS.CompactS4.Young22
import Taeyoung.Methods.RootedSOS.MatrixFlagDensity

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block02
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block02
