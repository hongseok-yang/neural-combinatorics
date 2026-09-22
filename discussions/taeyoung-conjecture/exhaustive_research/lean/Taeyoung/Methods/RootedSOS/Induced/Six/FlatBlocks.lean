import Taeyoung.Methods.RootedSOS.Induced.Six.SparseBase
namespace Taeyoung.Methods.RootedSOS.Induced.Six
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
theorem sum_square {M : Type*} [AddCommMonoid M] (d : Nat) (f : Fin (d*d) → M) :
    (∑ k, f k) = ∑ i : Fin d, ∑ j : Fin d, f (finProdFinEquiv (i,j)) := by
  rw [← finProdFinEquiv.sum_comp f]
  exact Fintype.sum_prod_type _
theorem sum_fourteen_squares {M : Type*} [AddCommMonoid M]
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : Nat) (f : Fin (d0*d0+(d1*d1+(d2*d2+(d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))))))) → M) :
    (∑ k, f k) =
      (∑ a : Fin d0, ∑ b : Fin d0, f (Fin.castAdd ((d1*d1+(d2*d2+(d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))))))) (finProdFinEquiv (a,b)))) +
      (∑ a : Fin d1, ∑ b : Fin d1, f (Fin.natAdd (d0*d0) (Fin.castAdd ((d2*d2+(d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))))))) (finProdFinEquiv (a,b))))) +
      (∑ a : Fin d2, ∑ b : Fin d2, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.castAdd ((d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))))) (finProdFinEquiv (a,b)))))) +
      (∑ a : Fin d3, ∑ b : Fin d3, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.castAdd ((d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))))) (finProdFinEquiv (a,b))))))) +
      (∑ a : Fin d4, ∑ b : Fin d4, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.castAdd ((d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))) (finProdFinEquiv (a,b)))))))) +
      (∑ a : Fin d5, ∑ b : Fin d5, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.castAdd ((d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))) (finProdFinEquiv (a,b))))))))) +
      (∑ a : Fin d6, ∑ b : Fin d6, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.castAdd ((d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))) (finProdFinEquiv (a,b)))))))))) +
      (∑ a : Fin d7, ∑ b : Fin d7, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.castAdd ((d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))) (finProdFinEquiv (a,b))))))))))) +
      (∑ a : Fin d8, ∑ b : Fin d8, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.castAdd ((d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))) (finProdFinEquiv (a,b)))))))))))) +
      (∑ a : Fin d9, ∑ b : Fin d9, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.castAdd ((d10*d10+(d11*d11+(d12*d12+d13*d13)))) (finProdFinEquiv (a,b))))))))))))) +
      (∑ a : Fin d10, ∑ b : Fin d10, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.castAdd ((d11*d11+(d12*d12+d13*d13))) (finProdFinEquiv (a,b)))))))))))))) +
      (∑ a : Fin d11, ∑ b : Fin d11, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.natAdd (d10*d10) (Fin.castAdd ((d12*d12+d13*d13)) (finProdFinEquiv (a,b))))))))))))))) +
      (∑ a : Fin d12, ∑ b : Fin d12, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.natAdd (d10*d10) (Fin.natAdd (d11*d11) (Fin.castAdd (d13*d13) (finProdFinEquiv (a,b)))))))))))))))) +
      (∑ a : Fin d13, ∑ b : Fin d13, f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.natAdd (d10*d10) (Fin.natAdd (d11*d11) (Fin.natAdd (d12*d12) (finProdFinEquiv (a,b)))))))))))))))) := by
  rw [Fin.sum_univ_add (a := d0*d0) (b := (d1*d1+(d2*d2+(d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))))))))]
  rw [Fin.sum_univ_add (a := d1*d1) (b := (d2*d2+(d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))))))]
  rw [Fin.sum_univ_add (a := d2*d2) (b := (d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))))))]
  rw [Fin.sum_univ_add (a := d3*d3) (b := (d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))))]
  rw [Fin.sum_univ_add (a := d4*d4) (b := (d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))))]
  rw [Fin.sum_univ_add (a := d5*d5) (b := (d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))]
  rw [Fin.sum_univ_add (a := d6*d6) (b := (d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))]
  rw [Fin.sum_univ_add (a := d7*d7) (b := (d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))]
  rw [Fin.sum_univ_add (a := d8*d8) (b := (d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))]
  rw [Fin.sum_univ_add (a := d9*d9) (b := (d10*d10+(d11*d11+(d12*d12+d13*d13))))]
  rw [Fin.sum_univ_add (a := d10*d10) (b := (d11*d11+(d12*d12+d13*d13)))]
  rw [Fin.sum_univ_add (a := d11*d11) (b := (d12*d12+d13*d13))]
  rw [Fin.sum_univ_add (a := d12*d12) (b := d13*d13)]
  rw [sum_square d0 (fun k => f (Fin.castAdd ((d1*d1+(d2*d2+(d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))))))) (k)))]
  rw [sum_square d1 (fun k => f (Fin.natAdd (d0*d0) (Fin.castAdd ((d2*d2+(d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))))))) (k))))]
  rw [sum_square d2 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.castAdd ((d3*d3+(d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))))) (k)))))]
  rw [sum_square d3 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.castAdd ((d4*d4+(d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))))) (k))))))]
  rw [sum_square d4 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.castAdd ((d5*d5+(d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))))) (k)))))))]
  rw [sum_square d5 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.castAdd ((d6*d6+(d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))))) (k))))))))]
  rw [sum_square d6 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.castAdd ((d7*d7+(d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))))) (k)))))))))]
  rw [sum_square d7 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.castAdd ((d8*d8+(d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13)))))) (k))))))))))]
  rw [sum_square d8 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.castAdd ((d9*d9+(d10*d10+(d11*d11+(d12*d12+d13*d13))))) (k)))))))))))]
  rw [sum_square d9 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.castAdd ((d10*d10+(d11*d11+(d12*d12+d13*d13)))) (k))))))))))))]
  rw [sum_square d10 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.castAdd ((d11*d11+(d12*d12+d13*d13))) (k)))))))))))))]
  rw [sum_square d11 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.natAdd (d10*d10) (Fin.castAdd ((d12*d12+d13*d13)) (k))))))))))))))]
  rw [sum_square d12 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.natAdd (d10*d10) (Fin.natAdd (d11*d11) (Fin.castAdd (d13*d13) (k)))))))))))))))]
  rw [sum_square d13 (fun k => f (Fin.natAdd (d0*d0) (Fin.natAdd (d1*d1) (Fin.natAdd (d2*d2) (Fin.natAdd (d3*d3) (Fin.natAdd (d4*d4) (Fin.natAdd (d5*d5) (Fin.natAdd (d6*d6) (Fin.natAdd (d7*d7) (Fin.natAdd (d8*d8) (Fin.natAdd (d9*d9) (Fin.natAdd (d10*d10) (Fin.natAdd (d11*d11) (Fin.natAdd (d12*d12) (k)))))))))))))))]
  simp only [add_assoc]

def blockIndex00 (a b : Fin 4) : Fin 3632 :=
  Fin.castAdd ((400+(400+(256+(256+(256+(256+(256+(256+(256+(256+(256+(256+256))))))))))))) (finProdFinEquiv (a,b))
@[simp] theorem blockIndex00_val (a b : Fin 4) :
    (blockIndex00 a b).1 = 0+b.1+4*a.1 := by
  simp [blockIndex00, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode00 (a b : Fin 4) :
    Sparse.flatCode (blockIndex00 a b) = Family00.countCode a b := by
  unfold Sparse.flatCode
  have hi : (blockIndex00 a b).1 < 16 := by rw [blockIndex00_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family00.countCode <;> apply Fin.ext <;>
    simp only [blockIndex00_val] <;> omega
theorem blockPulled00 (g : Fin 156) (a b : Fin 4) :
    Sparse.pulled g (blockIndex00 a b) = Family00.coefficient a b g := by
  simp only [Sparse.pulled, Family00.coefficient, blockCode00]
def blockIndex01 (a b : Fin 20) : Fin 3632 :=
  Fin.natAdd (16) (Fin.castAdd ((400+(256+(256+(256+(256+(256+(256+(256+(256+(256+(256+256)))))))))))) (finProdFinEquiv (a,b)))
@[simp] theorem blockIndex01_val (a b : Fin 20) :
    (blockIndex01 a b).1 = 16+b.1+20*a.1 := by
  simp [blockIndex01, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode01 (a b : Fin 20) :
    Sparse.flatCode (blockIndex01 a b) = Family01.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex01 a b).1 < 16 := by rw [blockIndex01_val]; omega
  rw [if_neg h0]
  have hi : (blockIndex01 a b).1 < 416 := by rw [blockIndex01_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family01.countCode <;> apply Fin.ext <;>
    simp only [blockIndex01_val] <;> omega
theorem blockPulled01 (g : Fin 156) (a b : Fin 20) :
    Sparse.pulled g (blockIndex01 a b) = Family01.coefficient a b g := by
  simp only [Sparse.pulled, Family01.coefficient, blockCode01]
def blockIndex02 (a b : Fin 20) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.castAdd ((256+(256+(256+(256+(256+(256+(256+(256+(256+(256+256))))))))))) (finProdFinEquiv (a,b))))
@[simp] theorem blockIndex02_val (a b : Fin 20) :
    (blockIndex02 a b).1 = 416+b.1+20*a.1 := by
  simp [blockIndex02, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode02 (a b : Fin 20) :
    Sparse.flatCode (blockIndex02 a b) = Family02.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex02 a b).1 < 16 := by rw [blockIndex02_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex02 a b).1 < 416 := by rw [blockIndex02_val]; omega
  rw [if_neg h1]
  have hi : (blockIndex02 a b).1 < 816 := by rw [blockIndex02_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family02.countCode <;> apply Fin.ext <;>
    simp only [blockIndex02_val] <;> omega
theorem blockPulled02 (g : Fin 156) (a b : Fin 20) :
    Sparse.pulled g (blockIndex02 a b) = Family02.coefficient a b g := by
  simp only [Sparse.pulled, Family02.coefficient, blockCode02]
def blockIndex03 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.castAdd ((256+(256+(256+(256+(256+(256+(256+(256+(256+256)))))))))) (finProdFinEquiv (a,b)))))
@[simp] theorem blockIndex03_val (a b : Fin 16) :
    (blockIndex03 a b).1 = 816+b.1+16*a.1 := by
  simp [blockIndex03, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode03 (a b : Fin 16) :
    Sparse.flatCode (blockIndex03 a b) = Family03.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex03 a b).1 < 16 := by rw [blockIndex03_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex03 a b).1 < 416 := by rw [blockIndex03_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex03 a b).1 < 816 := by rw [blockIndex03_val]; omega
  rw [if_neg h2]
  have hi : (blockIndex03 a b).1 < 1072 := by rw [blockIndex03_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family03.countCode <;> apply Fin.ext <;>
    simp only [blockIndex03_val] <;> omega
theorem blockPulled03 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex03 a b) = Family03.coefficient a b g := by
  simp only [Sparse.pulled, Family03.coefficient, blockCode03]
def blockIndex04 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.castAdd ((256+(256+(256+(256+(256+(256+(256+(256+256))))))))) (finProdFinEquiv (a,b))))))
@[simp] theorem blockIndex04_val (a b : Fin 16) :
    (blockIndex04 a b).1 = 1072+b.1+16*a.1 := by
  simp [blockIndex04, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode04 (a b : Fin 16) :
    Sparse.flatCode (blockIndex04 a b) = Family04.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex04 a b).1 < 16 := by rw [blockIndex04_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex04 a b).1 < 416 := by rw [blockIndex04_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex04 a b).1 < 816 := by rw [blockIndex04_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex04 a b).1 < 1072 := by rw [blockIndex04_val]; omega
  rw [if_neg h3]
  have hi : (blockIndex04 a b).1 < 1328 := by rw [blockIndex04_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family04.countCode <;> apply Fin.ext <;>
    simp only [blockIndex04_val] <;> omega
theorem blockPulled04 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex04 a b) = Family04.coefficient a b g := by
  simp only [Sparse.pulled, Family04.coefficient, blockCode04]
def blockIndex05 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd ((256+(256+(256+(256+(256+(256+(256+256)))))))) (finProdFinEquiv (a,b)))))))
@[simp] theorem blockIndex05_val (a b : Fin 16) :
    (blockIndex05 a b).1 = 1328+b.1+16*a.1 := by
  simp [blockIndex05, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode05 (a b : Fin 16) :
    Sparse.flatCode (blockIndex05 a b) = Family05.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex05 a b).1 < 16 := by rw [blockIndex05_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex05 a b).1 < 416 := by rw [blockIndex05_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex05 a b).1 < 816 := by rw [blockIndex05_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex05 a b).1 < 1072 := by rw [blockIndex05_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex05 a b).1 < 1328 := by rw [blockIndex05_val]; omega
  rw [if_neg h4]
  have hi : (blockIndex05 a b).1 < 1584 := by rw [blockIndex05_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family05.countCode <;> apply Fin.ext <;>
    simp only [blockIndex05_val] <;> omega
theorem blockPulled05 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex05 a b) = Family05.coefficient a b g := by
  simp only [Sparse.pulled, Family05.coefficient, blockCode05]
def blockIndex06 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd ((256+(256+(256+(256+(256+(256+256))))))) (finProdFinEquiv (a,b))))))))
@[simp] theorem blockIndex06_val (a b : Fin 16) :
    (blockIndex06 a b).1 = 1584+b.1+16*a.1 := by
  simp [blockIndex06, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode06 (a b : Fin 16) :
    Sparse.flatCode (blockIndex06 a b) = Family06.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex06 a b).1 < 16 := by rw [blockIndex06_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex06 a b).1 < 416 := by rw [blockIndex06_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex06 a b).1 < 816 := by rw [blockIndex06_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex06 a b).1 < 1072 := by rw [blockIndex06_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex06 a b).1 < 1328 := by rw [blockIndex06_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex06 a b).1 < 1584 := by rw [blockIndex06_val]; omega
  rw [if_neg h5]
  have hi : (blockIndex06 a b).1 < 1840 := by rw [blockIndex06_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family06.countCode <;> apply Fin.ext <;>
    simp only [blockIndex06_val] <;> omega
theorem blockPulled06 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex06 a b) = Family06.coefficient a b g := by
  simp only [Sparse.pulled, Family06.coefficient, blockCode06]
def blockIndex07 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd ((256+(256+(256+(256+(256+256)))))) (finProdFinEquiv (a,b)))))))))
@[simp] theorem blockIndex07_val (a b : Fin 16) :
    (blockIndex07 a b).1 = 1840+b.1+16*a.1 := by
  simp [blockIndex07, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode07 (a b : Fin 16) :
    Sparse.flatCode (blockIndex07 a b) = Family07.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex07 a b).1 < 16 := by rw [blockIndex07_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex07 a b).1 < 416 := by rw [blockIndex07_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex07 a b).1 < 816 := by rw [blockIndex07_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex07 a b).1 < 1072 := by rw [blockIndex07_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex07 a b).1 < 1328 := by rw [blockIndex07_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex07 a b).1 < 1584 := by rw [blockIndex07_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (blockIndex07 a b).1 < 1840 := by rw [blockIndex07_val]; omega
  rw [if_neg h6]
  have hi : (blockIndex07 a b).1 < 2096 := by rw [blockIndex07_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family07.countCode <;> apply Fin.ext <;>
    simp only [blockIndex07_val] <;> omega
theorem blockPulled07 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex07 a b) = Family07.coefficient a b g := by
  simp only [Sparse.pulled, Family07.coefficient, blockCode07]
def blockIndex08 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd ((256+(256+(256+(256+256))))) (finProdFinEquiv (a,b))))))))))
@[simp] theorem blockIndex08_val (a b : Fin 16) :
    (blockIndex08 a b).1 = 2096+b.1+16*a.1 := by
  simp [blockIndex08, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode08 (a b : Fin 16) :
    Sparse.flatCode (blockIndex08 a b) = Family08.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex08 a b).1 < 16 := by rw [blockIndex08_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex08 a b).1 < 416 := by rw [blockIndex08_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex08 a b).1 < 816 := by rw [blockIndex08_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex08 a b).1 < 1072 := by rw [blockIndex08_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex08 a b).1 < 1328 := by rw [blockIndex08_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex08 a b).1 < 1584 := by rw [blockIndex08_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (blockIndex08 a b).1 < 1840 := by rw [blockIndex08_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (blockIndex08 a b).1 < 2096 := by rw [blockIndex08_val]; omega
  rw [if_neg h7]
  have hi : (blockIndex08 a b).1 < 2352 := by rw [blockIndex08_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family08.countCode <;> apply Fin.ext <;>
    simp only [blockIndex08_val] <;> omega
theorem blockPulled08 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex08 a b) = Family08.coefficient a b g := by
  simp only [Sparse.pulled, Family08.coefficient, blockCode08]
def blockIndex09 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd ((256+(256+(256+256)))) (finProdFinEquiv (a,b)))))))))))
@[simp] theorem blockIndex09_val (a b : Fin 16) :
    (blockIndex09 a b).1 = 2352+b.1+16*a.1 := by
  simp [blockIndex09, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode09 (a b : Fin 16) :
    Sparse.flatCode (blockIndex09 a b) = Family09.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex09 a b).1 < 16 := by rw [blockIndex09_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex09 a b).1 < 416 := by rw [blockIndex09_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex09 a b).1 < 816 := by rw [blockIndex09_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex09 a b).1 < 1072 := by rw [blockIndex09_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex09 a b).1 < 1328 := by rw [blockIndex09_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex09 a b).1 < 1584 := by rw [blockIndex09_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (blockIndex09 a b).1 < 1840 := by rw [blockIndex09_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (blockIndex09 a b).1 < 2096 := by rw [blockIndex09_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (blockIndex09 a b).1 < 2352 := by rw [blockIndex09_val]; omega
  rw [if_neg h8]
  have hi : (blockIndex09 a b).1 < 2608 := by rw [blockIndex09_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family09.countCode <;> apply Fin.ext <;>
    simp only [blockIndex09_val] <;> omega
theorem blockPulled09 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex09 a b) = Family09.coefficient a b g := by
  simp only [Sparse.pulled, Family09.coefficient, blockCode09]
def blockIndex10 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd ((256+(256+256))) (finProdFinEquiv (a,b))))))))))))
@[simp] theorem blockIndex10_val (a b : Fin 16) :
    (blockIndex10 a b).1 = 2608+b.1+16*a.1 := by
  simp [blockIndex10, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode10 (a b : Fin 16) :
    Sparse.flatCode (blockIndex10 a b) = Family10.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex10 a b).1 < 16 := by rw [blockIndex10_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex10 a b).1 < 416 := by rw [blockIndex10_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex10 a b).1 < 816 := by rw [blockIndex10_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex10 a b).1 < 1072 := by rw [blockIndex10_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex10 a b).1 < 1328 := by rw [blockIndex10_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex10 a b).1 < 1584 := by rw [blockIndex10_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (blockIndex10 a b).1 < 1840 := by rw [blockIndex10_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (blockIndex10 a b).1 < 2096 := by rw [blockIndex10_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (blockIndex10 a b).1 < 2352 := by rw [blockIndex10_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (blockIndex10 a b).1 < 2608 := by rw [blockIndex10_val]; omega
  rw [if_neg h9]
  have hi : (blockIndex10 a b).1 < 2864 := by rw [blockIndex10_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family10.countCode <;> apply Fin.ext <;>
    simp only [blockIndex10_val] <;> omega
theorem blockPulled10 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex10 a b) = Family10.coefficient a b g := by
  simp only [Sparse.pulled, Family10.coefficient, blockCode10]
def blockIndex11 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd ((256+256)) (finProdFinEquiv (a,b)))))))))))))
@[simp] theorem blockIndex11_val (a b : Fin 16) :
    (blockIndex11 a b).1 = 2864+b.1+16*a.1 := by
  simp [blockIndex11, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode11 (a b : Fin 16) :
    Sparse.flatCode (blockIndex11 a b) = Family11.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex11 a b).1 < 16 := by rw [blockIndex11_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex11 a b).1 < 416 := by rw [blockIndex11_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex11 a b).1 < 816 := by rw [blockIndex11_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex11 a b).1 < 1072 := by rw [blockIndex11_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex11 a b).1 < 1328 := by rw [blockIndex11_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex11 a b).1 < 1584 := by rw [blockIndex11_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (blockIndex11 a b).1 < 1840 := by rw [blockIndex11_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (blockIndex11 a b).1 < 2096 := by rw [blockIndex11_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (blockIndex11 a b).1 < 2352 := by rw [blockIndex11_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (blockIndex11 a b).1 < 2608 := by rw [blockIndex11_val]; omega
  rw [if_neg h9]
  have h10 : ¬ (blockIndex11 a b).1 < 2864 := by rw [blockIndex11_val]; omega
  rw [if_neg h10]
  have hi : (blockIndex11 a b).1 < 3120 := by rw [blockIndex11_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family11.countCode <;> apply Fin.ext <;>
    simp only [blockIndex11_val] <;> omega
theorem blockPulled11 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex11 a b) = Family11.coefficient a b g := by
  simp only [Sparse.pulled, Family11.coefficient, blockCode11]
def blockIndex12 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.castAdd (256) (finProdFinEquiv (a,b))))))))))))))
@[simp] theorem blockIndex12_val (a b : Fin 16) :
    (blockIndex12 a b).1 = 3120+b.1+16*a.1 := by
  simp [blockIndex12, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode12 (a b : Fin 16) :
    Sparse.flatCode (blockIndex12 a b) = Family12.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex12 a b).1 < 16 := by rw [blockIndex12_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex12 a b).1 < 416 := by rw [blockIndex12_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex12 a b).1 < 816 := by rw [blockIndex12_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex12 a b).1 < 1072 := by rw [blockIndex12_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex12 a b).1 < 1328 := by rw [blockIndex12_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex12 a b).1 < 1584 := by rw [blockIndex12_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (blockIndex12 a b).1 < 1840 := by rw [blockIndex12_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (blockIndex12 a b).1 < 2096 := by rw [blockIndex12_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (blockIndex12 a b).1 < 2352 := by rw [blockIndex12_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (blockIndex12 a b).1 < 2608 := by rw [blockIndex12_val]; omega
  rw [if_neg h9]
  have h10 : ¬ (blockIndex12 a b).1 < 2864 := by rw [blockIndex12_val]; omega
  rw [if_neg h10]
  have h11 : ¬ (blockIndex12 a b).1 < 3120 := by rw [blockIndex12_val]; omega
  rw [if_neg h11]
  have hi : (blockIndex12 a b).1 < 3376 := by rw [blockIndex12_val]; omega
  rw [if_pos hi]
  apply congrArg₂ Family12.countCode <;> apply Fin.ext <;>
    simp only [blockIndex12_val] <;> omega
theorem blockPulled12 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex12 a b) = Family12.coefficient a b g := by
  simp only [Sparse.pulled, Family12.coefficient, blockCode12]
def blockIndex13 (a b : Fin 16) : Fin 3632 :=
  Fin.natAdd (16) (Fin.natAdd (400) (Fin.natAdd (400) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (Fin.natAdd (256) (finProdFinEquiv (a,b))))))))))))))
@[simp] theorem blockIndex13_val (a b : Fin 16) :
    (blockIndex13 a b).1 = 3376+b.1+16*a.1 := by
  simp [blockIndex13, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode13 (a b : Fin 16) :
    Sparse.flatCode (blockIndex13 a b) = Family13.countCode a b := by
  unfold Sparse.flatCode
  have h0 : ¬ (blockIndex13 a b).1 < 16 := by rw [blockIndex13_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (blockIndex13 a b).1 < 416 := by rw [blockIndex13_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (blockIndex13 a b).1 < 816 := by rw [blockIndex13_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (blockIndex13 a b).1 < 1072 := by rw [blockIndex13_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (blockIndex13 a b).1 < 1328 := by rw [blockIndex13_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (blockIndex13 a b).1 < 1584 := by rw [blockIndex13_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (blockIndex13 a b).1 < 1840 := by rw [blockIndex13_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (blockIndex13 a b).1 < 2096 := by rw [blockIndex13_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (blockIndex13 a b).1 < 2352 := by rw [blockIndex13_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (blockIndex13 a b).1 < 2608 := by rw [blockIndex13_val]; omega
  rw [if_neg h9]
  have h10 : ¬ (blockIndex13 a b).1 < 2864 := by rw [blockIndex13_val]; omega
  rw [if_neg h10]
  have h11 : ¬ (blockIndex13 a b).1 < 3120 := by rw [blockIndex13_val]; omega
  rw [if_neg h11]
  have h12 : ¬ (blockIndex13 a b).1 < 3376 := by rw [blockIndex13_val]; omega
  rw [if_neg h12]
  apply congrArg₂ Family13.countCode <;> apply Fin.ext <;>
    simp only [blockIndex13_val] <;> omega
theorem blockPulled13 (g : Fin 156) (a b : Fin 16) :
    Sparse.pulled g (blockIndex13 a b) = Family13.coefficient a b g := by
  simp only [Sparse.pulled, Family13.coefficient, blockCode13]
theorem sum_all_blocks {M : Type*} [AddCommMonoid M] (f : Fin 3632 → M) :
    (∑ k, f k) =
      (∑ a : Fin 4, ∑ b : Fin 4, f (blockIndex00 a b)) +
      (∑ a : Fin 20, ∑ b : Fin 20, f (blockIndex01 a b)) +
      (∑ a : Fin 20, ∑ b : Fin 20, f (blockIndex02 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex03 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex04 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex05 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex06 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex07 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex08 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex09 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex10 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex11 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex12 a b)) +
      (∑ a : Fin 16, ∑ b : Fin 16, f (blockIndex13 a b)) := by
  simpa only [blockIndex00, blockIndex01, blockIndex02, blockIndex03, blockIndex04, blockIndex05, blockIndex06, blockIndex07, blockIndex08, blockIndex09, blockIndex10, blockIndex11, blockIndex12, blockIndex13] using
    sum_fourteen_squares 4 20 20 16 16 16 16 16 16 16 16 16 16 16 f
#print axioms sum_all_blocks
end Taeyoung.Methods.RootedSOS.Induced.Six
