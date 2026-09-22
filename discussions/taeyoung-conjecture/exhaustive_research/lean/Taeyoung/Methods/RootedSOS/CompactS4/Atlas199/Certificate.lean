import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.BlockSum0
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.BlockSum1
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.BlockSum2
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.BlockSum3
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.BlockSum4
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Contraction
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Interval
import Taeyoung.Methods.RootedSOS.MatrixContraction

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas199

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

theorem graphon_bound (W : Graphon Ω μ) (hp : (2 : Real)/3 ≤ cliqueDensity 2 W) :
    target199 (cliqueDensity 2 W) ≤ homDensity graph199 W := by
  let s := 3*cliqueDensity 2 W-2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by
    have h := cliqueDensity_le_one 2 W
    dsimp [s]
    linarith
  have hp' : (2+s)/3 = cliqueDensity 2 W := by dsimp [s]; ring
  have h := group_nonneg W s hs hs1
  have he := group_identity s (fun g => homDensity (S4Classification.coreGraph6 g) W)
  have hc (g : Fin 143) : homDensity (S4Classification.coreGraph6 g) W =
      homDensity (S4Classification.coreGraph6 (representative g)) W :=
    density_eq_of_graph_eq _ _ W (core_eq g)
  simp_rw [← hc] at he
  rw [hp', density_eq_of_graph_eq _ _ W target_core,
    density_eq_of_graph_eq _ _ W empty_core, homDensity_bot_fin] at he
  have ht := target199_interval s
  rw [hp'] at ht
  have ht' : 81*target199 (cliqueDensity 2 W) = (0)*s^0 + (4)*s^1 + (8)*s^2 + (15)*s^3 + (38)*s^4 + (16)*s^5 := by
    rw [ht]
    ring
  nlinarith

theorem satisfiesLowerBound_199 : Taeyoung.SatisfiesLowerBound graph199 :=
  satisfiesLowerBound_199_of_bound (fun W hp => graphon_bound W hp)

#print axioms satisfiesLowerBound_199
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas199
