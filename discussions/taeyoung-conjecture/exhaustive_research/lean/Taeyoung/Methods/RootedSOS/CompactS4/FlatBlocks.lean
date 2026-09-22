import Taeyoung.Methods.RootedSOS.CompactS4.SparseBase
namespace Taeyoung.Methods.RootedSOS.CompactS4
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem sum_square {M : Type*} [AddCommMonoid M] (d : Nat) (f : Fin (d*d) → M) :
    (∑ k, f k) = ∑ i : Fin d, ∑ j : Fin d, f (finProdFinEquiv (i,j)) := by
  rw [← (finProdFinEquiv.sum_comp f)]
  exact Fintype.sum_prod_type _

theorem sum_five_squares {M : Type*} [AddCommMonoid M]
    (a b c d e : Nat) (f : Fin (a*a+(b*b+(c*c+(d*d+e*e)))) → M) :
    (∑ k, f k) =
      (∑ i : Fin a, ∑ j : Fin a, f (Fin.castAdd _ (finProdFinEquiv (i,j)))) +
      (∑ i : Fin b, ∑ j : Fin b, f (Fin.natAdd (a*a) (Fin.castAdd _ (finProdFinEquiv (i,j))))) +
      (∑ i : Fin c, ∑ j : Fin c, f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.castAdd _ (finProdFinEquiv (i,j)))))) +
      (∑ i : Fin d, ∑ j : Fin d, f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.castAdd _ (finProdFinEquiv (i,j))))))) +
      (∑ i : Fin e, ∑ j : Fin e, f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.natAdd (d*d) (finProdFinEquiv (i,j))))))) := by
  rw [Fin.sum_univ_add (a := a*a) (b := b*b+(c*c+(d*d+e*e)))]
  rw [Fin.sum_univ_add (a := b*b) (b := c*c+(d*d+e*e))]
  rw [Fin.sum_univ_add (a := c*c) (b := d*d+e*e)]
  rw [Fin.sum_univ_add (a := d*d) (b := e*e)]
  rw [sum_square a (fun k => f (Fin.castAdd _ k))]
  rw [sum_square b (fun k => f (Fin.natAdd (a*a) (Fin.castAdd _ k)))]
  rw [sum_square c (fun k => f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.castAdd _ k))))]
  rw [sum_square d (fun k => f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.castAdd _ k)))))]
  rw [sum_square e (fun k => f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.natAdd (d*d) k)))))]
  simp only [add_assoc]

#print axioms sum_five_squares

def blockIndex0 (i j : Fin 32) : Fin 5820 :=
  Fin.castAdd 4796 (finProdFinEquiv (i,j))

@[simp] theorem blockIndex0_val (i j : Fin 32) :
    (blockIndex0 i j).1 = 0+j.1+32*i.1 := by
  simp [blockIndex0, finProdFinEquiv, Nat.add_assoc] <;> omega

theorem blockCode0 (i j : Fin 32) :
    Sparse.flatCode (blockIndex0 i j) = Young4.code i j := by
  unfold Sparse.flatCode
  split_ifs
  all_goals try (exfalso; simp only [blockIndex0_val] at *; omega)
  apply congrArg₂ Young4.code <;> apply Fin.ext <;>
    simp only [blockIndex0_val] <;> omega

#print axioms blockCode0

theorem blockPulled0 (g : Fin 143) (i j : Fin 32) :
    Sparse.pulled g (blockIndex0 i j) = Young4.pulled g i j := by
  simp only [Sparse.pulled, Young4.pulled, blockCode0]

def blockIndex1 (i j : Fin 52) : Fin 5820 :=
  Fin.natAdd 1024 (Fin.castAdd 2092 (finProdFinEquiv (i,j)))

@[simp] theorem blockIndex1_val (i j : Fin 52) :
    (blockIndex1 i j).1 = 1024+j.1+52*i.1 := by
  simp [blockIndex1, finProdFinEquiv, Nat.add_assoc] <;> omega

theorem blockCode1 (i j : Fin 52) :
    Sparse.flatCode (blockIndex1 i j) = Young31.code i j := by
  unfold Sparse.flatCode
  split_ifs
  all_goals try (exfalso; simp only [blockIndex1_val] at *; omega)
  apply congrArg₂ Young31.code <;> apply Fin.ext <;>
    simp only [blockIndex1_val] <;> omega

#print axioms blockCode1

theorem blockPulled1 (g : Fin 143) (i j : Fin 52) :
    Sparse.pulled g (blockIndex1 i j) = Young31.pulled g i j := by
  simp only [Sparse.pulled, Young31.pulled, blockCode1]

def blockIndex2 (i j : Fin 34) : Fin 5820 :=
  Fin.natAdd 1024 (Fin.natAdd 2704 (Fin.castAdd 936 (finProdFinEquiv (i,j))))

@[simp] theorem blockIndex2_val (i j : Fin 34) :
    (blockIndex2 i j).1 = 3728+j.1+34*i.1 := by
  simp [blockIndex2, finProdFinEquiv, Nat.add_assoc] <;> omega

theorem blockCode2 (i j : Fin 34) :
    Sparse.flatCode (blockIndex2 i j) = Young22.code i j := by
  unfold Sparse.flatCode
  split_ifs
  all_goals try (exfalso; simp only [blockIndex2_val] at *; omega)
  apply congrArg₂ Young22.code <;> apply Fin.ext <;>
    simp only [blockIndex2_val] <;> omega

#print axioms blockCode2

theorem blockPulled2 (g : Fin 143) (i j : Fin 34) :
    Sparse.pulled g (blockIndex2 i j) = Young22.pulled g i j := by
  simp only [Sparse.pulled, Young22.pulled, blockCode2]

def blockIndex3 (i j : Fin 30) : Fin 5820 :=
  Fin.natAdd 1024 (Fin.natAdd 2704 (Fin.natAdd 1156 (Fin.castAdd 36 (finProdFinEquiv (i,j)))))

@[simp] theorem blockIndex3_val (i j : Fin 30) :
    (blockIndex3 i j).1 = 4884+j.1+30*i.1 := by
  simp [blockIndex3, finProdFinEquiv, Nat.add_assoc] <;> omega

theorem blockCode3 (i j : Fin 30) :
    Sparse.flatCode (blockIndex3 i j) = Young211.code i j := by
  unfold Sparse.flatCode
  split_ifs
  all_goals try (exfalso; simp only [blockIndex3_val] at *; omega)
  apply congrArg₂ Young211.code <;> apply Fin.ext <;>
    simp only [blockIndex3_val] <;> omega

#print axioms blockCode3

theorem blockPulled3 (g : Fin 143) (i j : Fin 30) :
    Sparse.pulled g (blockIndex3 i j) = Young211.pulled g i j := by
  simp only [Sparse.pulled, Young211.pulled, blockCode3]

def blockIndex4 (i j : Fin 6) : Fin 5820 :=
  Fin.natAdd 1024 (Fin.natAdd 2704 (Fin.natAdd 1156 (Fin.natAdd 900 (finProdFinEquiv (i,j)))))

@[simp] theorem blockIndex4_val (i j : Fin 6) :
    (blockIndex4 i j).1 = 5784+j.1+6*i.1 := by
  simp [blockIndex4, finProdFinEquiv, Nat.add_assoc] <;> omega

theorem blockCode4 (i j : Fin 6) :
    Sparse.flatCode (blockIndex4 i j) = Young1111.code i j := by
  unfold Sparse.flatCode
  split_ifs
  all_goals try (exfalso; simp only [blockIndex4_val] at *; omega)
  apply congrArg₂ Young1111.code <;> apply Fin.ext <;>
    simp only [blockIndex4_val] <;> omega

#print axioms blockCode4

theorem blockPulled4 (g : Fin 143) (i j : Fin 6) :
    Sparse.pulled g (blockIndex4 i j) = Young1111.pulled g i j := by
  simp only [Sparse.pulled, Young1111.pulled, blockCode4]

theorem sum_five_blocks {M : Type*} [AddCommMonoid M] (f : Fin 5820 → M) :
    (∑ k, f k) =
      (∑ i : Fin 32, ∑ j : Fin 32, f (blockIndex0 i j)) +
      (∑ i : Fin 52, ∑ j : Fin 52, f (blockIndex1 i j)) +
      (∑ i : Fin 34, ∑ j : Fin 34, f (blockIndex2 i j)) +
      (∑ i : Fin 30, ∑ j : Fin 30, f (blockIndex3 i j)) +
      (∑ i : Fin 6, ∑ j : Fin 6, f (blockIndex4 i j)) := by
  exact sum_five_squares 32 52 34 30 6 f

#print axioms sum_five_blocks

end Taeyoung.Methods.RootedSOS.CompactS4
