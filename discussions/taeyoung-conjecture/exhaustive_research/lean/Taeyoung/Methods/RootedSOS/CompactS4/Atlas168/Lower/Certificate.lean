import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.BlockSum0
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.BlockSum1
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.BlockSum2
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.BlockSum3
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.BlockSum4
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Contraction
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Interval
import Taeyoung.Methods.RootedSOS.MatrixContraction

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower

open Finset MeasureTheory Taeyoung
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem dense_nonneg (W : Graphon Ω μ) (s : Real) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ k : Fin 5820,
      ((right k 0 : Real)+(right k 1 : Real)*s+(right k 2 : Real)*s^2+
        (right k 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g k : Real) *
        (cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          homDensity (S4Classification.coreGraph6 g) W)) := by
  rw [sum_five_blocks]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (blockSum0_nonneg W s hs hs1) (blockSum1_nonneg W s hs hs1))
    (blockSum2_nonneg W s hs hs1)) (blockSum3_nonneg W s hs hs1))
    (blockSum4_nonneg W s hs hs1)

theorem group_nonneg (W : Graphon Ω μ) (s : Real) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ g : Fin 143,
      ((groupTotal g 0 : Real)+(groupTotal g 1 : Real)*s+(groupTotal g 2 : Real)*s^2+
        (groupTotal g 3 : Real)*s*(1-s)) *
      (cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        homDensity (S4Classification.coreGraph6 g) W) := by
  let w : Fin 4 → Real := fun u =>
    if u.1 = 0 then 1 else if u.1 = 1 then s else if u.1 = 2 then s^2 else s*(1-s)
  have hw0 : w 0 = 1 := rfl
  have hw1 : w 1 = s := rfl
  have hw2 : w 2 = s^2 := rfl
  have hw3 : w 3 = s*(1-s) := rfl
  have he := integer_contraction_eval (U := Fin 4) Sparse.pulled (fun k u => right k u)
    (fun g u => groupTotal g u) groupTotal_exact w
    (fun g => cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
      homDensity (S4Classification.coreGraph6 g) W)
  simp only [Fin.sum_univ_four, hw0, hw1, hw2, hw3, mul_one] at he
  norm_num at he
  have h := dense_nonneg W s hs hs1
  simp only [mul_assoc] at h ⊢
  rwa [← he]

private theorem density_eq_of_graph_eq {n : Nat}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) : homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

theorem graphon_bound (W : Graphon Ω μ)
    (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) (hp1 : cliqueDensity 2 W ≤ (2 : Real)/3) :
    target168 (cliqueDensity 2 W) ≤ homDensity graph168 W := by
  let s := (6*cliqueDensity 2 W-3)/1
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hp' : (3+1*s)/6 = cliqueDensity 2 W := by dsimp [s]; ring
  have h := group_nonneg W s hs hs1
  have he := group_identity s (fun g => homDensity (S4Classification.coreGraph6 g) W)
  have hc (g : Fin 143) : homDensity (S4Classification.coreGraph6 g) W =
      homDensity (S4Classification.coreGraph6 (representative g)) W :=
    density_eq_of_graph_eq _ _ W (core_eq g)
  simp_rw [← hc] at he
  rw [hp', density_eq_of_graph_eq _ _ W target_core,
    density_eq_of_graph_eq _ _ W empty_core, homDensity_bot_fin] at he
  have ht : 7776*target168 (cliqueDensity 2 W) = (0)*s^0 + (0)*s^1 + (108)*s^2 + (-36)*s^3 + (36)*s^4 + (20)*s^5 := by
    rw [← hp']
    unfold target168
    ring
  nlinarith

#print axioms graphon_bound
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower
