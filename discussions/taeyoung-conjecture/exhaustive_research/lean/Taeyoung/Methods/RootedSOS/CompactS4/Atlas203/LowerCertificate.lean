import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.LowerIntervalChecks0000
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.LowerIntervalChecks0078
import Taeyoung.Methods.RootedSOS.MatrixContraction
import Taeyoung.Methods.RootedSOS.Induced.Six.FlatBlocks

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203
theorem Lower.coefficientCheck_all (k : Fin 156) : Lower.coefficientCheck k := by
  by_cases h : k.1 < 78
  · let j : Fin 78 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using LowerIntervalChecks_0000 j
  by_cases h : k.1 < 156
  · let j : Fin 78 := ⟨k.1-78, by omega⟩
    have he : (⟨78+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using LowerIntervalChecks_0078 j
  omega

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Lower
open Finset MeasureTheory Taeyoung
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def weightedRight (k : Fin 3632) (s : Real) : Real :=
  (right k 0 : Real)*(1-s)^2+(right k 1 : Real)*s*(1-s)+(right k 2 : Real)*s^2
def weightedGroup (g : Fin 156) (s : Real) : Real :=
  (groupTotal g 0 : Real)*(1-s)^2+(groupTotal g 1 : Real)*s*(1-s)+(groupTotal g 2 : Real)*s^2
def residualValue (g : Fin 156) (s : Real) : Real :=
  ∑ k : Fin 6, (residualCoefficient g k : Real)*Induced.basis 5 s k.1
def multiplierValue (j : Fin 11) (s : Real) : Real :=
  Induced.bernstein4 (fun k => multiplier j k) s

theorem blockRight00 (i j : Fin 4) (u : Fin 3) :
    right (Induced.Six.blockIndex00 i j) u =
      if u.1 = 0 then Block00.H i j
      else if u.1 = 1 then Block00.H i (4+j.1)+Block00.H (4+i.1) j+Block01.H i j
      else Block00.H (4+i.1) (4+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex00 i j)).1 u).2]
  unfold expandedRight
  have hi : (Induced.Six.blockIndex00 i j).1 < 16 := by
    rw [Induced.Six.blockIndex00_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex00 i j).1-0)/4 = i.1 := by
    rw [Induced.Six.blockIndex00_val]; omega
  have hb : ((Induced.Six.blockIndex00 i j).1-0)%4 = j.1 := by
    rw [Induced.Six.blockIndex00_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix00 (i j : Fin 4) (s : Real) :
    weightedRight (Induced.Six.blockIndex00 i j) s = Type00.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block00.H Block01.H
    (fun u => right (Induced.Six.blockIndex00 i j) u) i j (blockRight00 i j) s

theorem blockNonneg00 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, weightedRight (Induced.Six.blockIndex00 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex00 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix00, Induced.Six.blockPulled00]
  exact Induced.Six.Family00.gram_nonneg W (Type00.matrix s)
    (Type00.matrix_nonneg hs0 hs1)

theorem blockRight01 (i j : Fin 20) (u : Fin 3) :
    right (Induced.Six.blockIndex01 i j) u =
      if u.1 = 0 then Block02.H i j
      else if u.1 = 1 then Block02.H i (20+j.1)+Block02.H (20+i.1) j+Block03.H i j
      else Block02.H (20+i.1) (20+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex01 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex01 i j).1 < 16 := by
    rw [Induced.Six.blockIndex01_val]; omega
  rw [if_neg h0]
  have hi : (Induced.Six.blockIndex01 i j).1 < 416 := by
    rw [Induced.Six.blockIndex01_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex01 i j).1-16)/20 = i.1 := by
    rw [Induced.Six.blockIndex01_val]; omega
  have hb : ((Induced.Six.blockIndex01 i j).1-16)%20 = j.1 := by
    rw [Induced.Six.blockIndex01_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix01 (i j : Fin 20) (s : Real) :
    weightedRight (Induced.Six.blockIndex01 i j) s = Type01.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block02.H Block03.H
    (fun u => right (Induced.Six.blockIndex01 i j) u) i j (blockRight01 i j) s

theorem blockNonneg01 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 20, ∑ j : Fin 20, weightedRight (Induced.Six.blockIndex01 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex01 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix01, Induced.Six.blockPulled01]
  exact Induced.Six.Family01.gram_nonneg W (Type01.matrix s)
    (Type01.matrix_nonneg hs0 hs1)

theorem blockRight02 (i j : Fin 20) (u : Fin 3) :
    right (Induced.Six.blockIndex02 i j) u =
      if u.1 = 0 then Block04.H i j
      else if u.1 = 1 then Block04.H i (20+j.1)+Block04.H (20+i.1) j+Block05.H i j
      else Block04.H (20+i.1) (20+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex02 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex02 i j).1 < 16 := by
    rw [Induced.Six.blockIndex02_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex02 i j).1 < 416 := by
    rw [Induced.Six.blockIndex02_val]; omega
  rw [if_neg h1]
  have hi : (Induced.Six.blockIndex02 i j).1 < 816 := by
    rw [Induced.Six.blockIndex02_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex02 i j).1-416)/20 = i.1 := by
    rw [Induced.Six.blockIndex02_val]; omega
  have hb : ((Induced.Six.blockIndex02 i j).1-416)%20 = j.1 := by
    rw [Induced.Six.blockIndex02_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix02 (i j : Fin 20) (s : Real) :
    weightedRight (Induced.Six.blockIndex02 i j) s = Type02.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block04.H Block05.H
    (fun u => right (Induced.Six.blockIndex02 i j) u) i j (blockRight02 i j) s

theorem blockNonneg02 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 20, ∑ j : Fin 20, weightedRight (Induced.Six.blockIndex02 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex02 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix02, Induced.Six.blockPulled02]
  exact Induced.Six.Family02.gram_nonneg W (Type02.matrix s)
    (Type02.matrix_nonneg hs0 hs1)

theorem blockRight03 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex03 i j) u =
      if u.1 = 0 then Block06.H i j
      else if u.1 = 1 then Block06.H i (16+j.1)+Block06.H (16+i.1) j+Block07.H i j
      else Block06.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex03 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex03 i j).1 < 16 := by
    rw [Induced.Six.blockIndex03_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex03 i j).1 < 416 := by
    rw [Induced.Six.blockIndex03_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex03 i j).1 < 816 := by
    rw [Induced.Six.blockIndex03_val]; omega
  rw [if_neg h2]
  have hi : (Induced.Six.blockIndex03 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex03_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex03 i j).1-816)/16 = i.1 := by
    rw [Induced.Six.blockIndex03_val]; omega
  have hb : ((Induced.Six.blockIndex03 i j).1-816)%16 = j.1 := by
    rw [Induced.Six.blockIndex03_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix03 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex03 i j) s = Type03.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block06.H Block07.H
    (fun u => right (Induced.Six.blockIndex03 i j) u) i j (blockRight03 i j) s

theorem blockNonneg03 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex03 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex03 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix03, Induced.Six.blockPulled03]
  exact Induced.Six.Family03.gram_nonneg W (Type03.matrix s)
    (Type03.matrix_nonneg hs0 hs1)

theorem blockRight04 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex04 i j) u =
      if u.1 = 0 then Block08.H i j
      else if u.1 = 1 then Block08.H i (16+j.1)+Block08.H (16+i.1) j+Block09.H i j
      else Block08.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex04 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex04 i j).1 < 16 := by
    rw [Induced.Six.blockIndex04_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex04 i j).1 < 416 := by
    rw [Induced.Six.blockIndex04_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex04 i j).1 < 816 := by
    rw [Induced.Six.blockIndex04_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex04 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex04_val]; omega
  rw [if_neg h3]
  have hi : (Induced.Six.blockIndex04 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex04_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex04 i j).1-1072)/16 = i.1 := by
    rw [Induced.Six.blockIndex04_val]; omega
  have hb : ((Induced.Six.blockIndex04 i j).1-1072)%16 = j.1 := by
    rw [Induced.Six.blockIndex04_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix04 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex04 i j) s = Type04.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block08.H Block09.H
    (fun u => right (Induced.Six.blockIndex04 i j) u) i j (blockRight04 i j) s

theorem blockNonneg04 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex04 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex04 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix04, Induced.Six.blockPulled04]
  exact Induced.Six.Family04.gram_nonneg W (Type04.matrix s)
    (Type04.matrix_nonneg hs0 hs1)

theorem blockRight05 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex05 i j) u =
      if u.1 = 0 then Block10.H i j
      else if u.1 = 1 then Block10.H i (16+j.1)+Block10.H (16+i.1) j+Block11.H i j
      else Block10.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex05 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex05 i j).1 < 16 := by
    rw [Induced.Six.blockIndex05_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex05 i j).1 < 416 := by
    rw [Induced.Six.blockIndex05_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex05 i j).1 < 816 := by
    rw [Induced.Six.blockIndex05_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex05 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex05_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex05 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex05_val]; omega
  rw [if_neg h4]
  have hi : (Induced.Six.blockIndex05 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex05_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex05 i j).1-1328)/16 = i.1 := by
    rw [Induced.Six.blockIndex05_val]; omega
  have hb : ((Induced.Six.blockIndex05 i j).1-1328)%16 = j.1 := by
    rw [Induced.Six.blockIndex05_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix05 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex05 i j) s = Type05.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block10.H Block11.H
    (fun u => right (Induced.Six.blockIndex05 i j) u) i j (blockRight05 i j) s

theorem blockNonneg05 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex05 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex05 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix05, Induced.Six.blockPulled05]
  exact Induced.Six.Family05.gram_nonneg W (Type05.matrix s)
    (Type05.matrix_nonneg hs0 hs1)

theorem blockRight06 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex06 i j) u =
      if u.1 = 0 then Block12.H i j
      else if u.1 = 1 then Block12.H i (16+j.1)+Block12.H (16+i.1) j+Block13.H i j
      else Block12.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex06 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex06 i j).1 < 16 := by
    rw [Induced.Six.blockIndex06_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex06 i j).1 < 416 := by
    rw [Induced.Six.blockIndex06_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex06 i j).1 < 816 := by
    rw [Induced.Six.blockIndex06_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex06 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex06_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex06 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex06_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex06 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex06_val]; omega
  rw [if_neg h5]
  have hi : (Induced.Six.blockIndex06 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex06_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex06 i j).1-1584)/16 = i.1 := by
    rw [Induced.Six.blockIndex06_val]; omega
  have hb : ((Induced.Six.blockIndex06 i j).1-1584)%16 = j.1 := by
    rw [Induced.Six.blockIndex06_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix06 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex06 i j) s = Type06.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block12.H Block13.H
    (fun u => right (Induced.Six.blockIndex06 i j) u) i j (blockRight06 i j) s

theorem blockNonneg06 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex06 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex06 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix06, Induced.Six.blockPulled06]
  exact Induced.Six.Family06.gram_nonneg W (Type06.matrix s)
    (Type06.matrix_nonneg hs0 hs1)

theorem blockRight07 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex07 i j) u =
      if u.1 = 0 then Block14.H i j
      else if u.1 = 1 then Block14.H i (16+j.1)+Block14.H (16+i.1) j+Block15.H i j
      else Block14.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex07 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex07 i j).1 < 16 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex07 i j).1 < 416 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex07 i j).1 < 816 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex07 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex07 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex07 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (Induced.Six.blockIndex07 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_neg h6]
  have hi : (Induced.Six.blockIndex07 i j).1 < 2096 := by
    rw [Induced.Six.blockIndex07_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex07 i j).1-1840)/16 = i.1 := by
    rw [Induced.Six.blockIndex07_val]; omega
  have hb : ((Induced.Six.blockIndex07 i j).1-1840)%16 = j.1 := by
    rw [Induced.Six.blockIndex07_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix07 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex07 i j) s = Type07.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block14.H Block15.H
    (fun u => right (Induced.Six.blockIndex07 i j) u) i j (blockRight07 i j) s

theorem blockNonneg07 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex07 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex07 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix07, Induced.Six.blockPulled07]
  exact Induced.Six.Family07.gram_nonneg W (Type07.matrix s)
    (Type07.matrix_nonneg hs0 hs1)

theorem blockRight08 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex08 i j) u =
      if u.1 = 0 then Block16.H i j
      else if u.1 = 1 then Block16.H i (16+j.1)+Block16.H (16+i.1) j+Block17.H i j
      else Block16.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex08 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex08 i j).1 < 16 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex08 i j).1 < 416 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex08 i j).1 < 816 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex08 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex08 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex08 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (Induced.Six.blockIndex08 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (Induced.Six.blockIndex08 i j).1 < 2096 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_neg h7]
  have hi : (Induced.Six.blockIndex08 i j).1 < 2352 := by
    rw [Induced.Six.blockIndex08_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex08 i j).1-2096)/16 = i.1 := by
    rw [Induced.Six.blockIndex08_val]; omega
  have hb : ((Induced.Six.blockIndex08 i j).1-2096)%16 = j.1 := by
    rw [Induced.Six.blockIndex08_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix08 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex08 i j) s = Type08.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block16.H Block17.H
    (fun u => right (Induced.Six.blockIndex08 i j) u) i j (blockRight08 i j) s

theorem blockNonneg08 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex08 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex08 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix08, Induced.Six.blockPulled08]
  exact Induced.Six.Family08.gram_nonneg W (Type08.matrix s)
    (Type08.matrix_nonneg hs0 hs1)

theorem blockRight09 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex09 i j) u =
      if u.1 = 0 then Block18.H i j
      else if u.1 = 1 then Block18.H i (16+j.1)+Block18.H (16+i.1) j+Block19.H i j
      else Block18.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex09 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex09 i j).1 < 16 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex09 i j).1 < 416 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex09 i j).1 < 816 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex09 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex09 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex09 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (Induced.Six.blockIndex09 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (Induced.Six.blockIndex09 i j).1 < 2096 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (Induced.Six.blockIndex09 i j).1 < 2352 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_neg h8]
  have hi : (Induced.Six.blockIndex09 i j).1 < 2608 := by
    rw [Induced.Six.blockIndex09_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex09 i j).1-2352)/16 = i.1 := by
    rw [Induced.Six.blockIndex09_val]; omega
  have hb : ((Induced.Six.blockIndex09 i j).1-2352)%16 = j.1 := by
    rw [Induced.Six.blockIndex09_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix09 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex09 i j) s = Type09.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block18.H Block19.H
    (fun u => right (Induced.Six.blockIndex09 i j) u) i j (blockRight09 i j) s

theorem blockNonneg09 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex09 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex09 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix09, Induced.Six.blockPulled09]
  exact Induced.Six.Family09.gram_nonneg W (Type09.matrix s)
    (Type09.matrix_nonneg hs0 hs1)

theorem blockRight10 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex10 i j) u =
      if u.1 = 0 then Block20.H i j
      else if u.1 = 1 then Block20.H i (16+j.1)+Block20.H (16+i.1) j+Block21.H i j
      else Block20.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex10 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex10 i j).1 < 16 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex10 i j).1 < 416 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex10 i j).1 < 816 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex10 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex10 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex10 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (Induced.Six.blockIndex10 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (Induced.Six.blockIndex10 i j).1 < 2096 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (Induced.Six.blockIndex10 i j).1 < 2352 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (Induced.Six.blockIndex10 i j).1 < 2608 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_neg h9]
  have hi : (Induced.Six.blockIndex10 i j).1 < 2864 := by
    rw [Induced.Six.blockIndex10_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex10 i j).1-2608)/16 = i.1 := by
    rw [Induced.Six.blockIndex10_val]; omega
  have hb : ((Induced.Six.blockIndex10 i j).1-2608)%16 = j.1 := by
    rw [Induced.Six.blockIndex10_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix10 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex10 i j) s = Type10.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block20.H Block21.H
    (fun u => right (Induced.Six.blockIndex10 i j) u) i j (blockRight10 i j) s

theorem blockNonneg10 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex10 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex10 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix10, Induced.Six.blockPulled10]
  exact Induced.Six.Family10.gram_nonneg W (Type10.matrix s)
    (Type10.matrix_nonneg hs0 hs1)

theorem blockRight11 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex11 i j) u =
      if u.1 = 0 then Block22.H i j
      else if u.1 = 1 then Block22.H i (16+j.1)+Block22.H (16+i.1) j+Block23.H i j
      else Block22.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex11 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex11 i j).1 < 16 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex11 i j).1 < 416 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex11 i j).1 < 816 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex11 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex11 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex11 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (Induced.Six.blockIndex11 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (Induced.Six.blockIndex11 i j).1 < 2096 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (Induced.Six.blockIndex11 i j).1 < 2352 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (Induced.Six.blockIndex11 i j).1 < 2608 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h9]
  have h10 : ¬ (Induced.Six.blockIndex11 i j).1 < 2864 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_neg h10]
  have hi : (Induced.Six.blockIndex11 i j).1 < 3120 := by
    rw [Induced.Six.blockIndex11_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex11 i j).1-2864)/16 = i.1 := by
    rw [Induced.Six.blockIndex11_val]; omega
  have hb : ((Induced.Six.blockIndex11 i j).1-2864)%16 = j.1 := by
    rw [Induced.Six.blockIndex11_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix11 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex11 i j) s = Type11.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block22.H Block23.H
    (fun u => right (Induced.Six.blockIndex11 i j) u) i j (blockRight11 i j) s

theorem blockNonneg11 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex11 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex11 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix11, Induced.Six.blockPulled11]
  exact Induced.Six.Family11.gram_nonneg W (Type11.matrix s)
    (Type11.matrix_nonneg hs0 hs1)

theorem blockRight12 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex12 i j) u =
      if u.1 = 0 then Block24.H i j
      else if u.1 = 1 then Block24.H i (16+j.1)+Block24.H (16+i.1) j+Block25.H i j
      else Block24.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex12 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex12 i j).1 < 16 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex12 i j).1 < 416 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex12 i j).1 < 816 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex12 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex12 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex12 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (Induced.Six.blockIndex12 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (Induced.Six.blockIndex12 i j).1 < 2096 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (Induced.Six.blockIndex12 i j).1 < 2352 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (Induced.Six.blockIndex12 i j).1 < 2608 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h9]
  have h10 : ¬ (Induced.Six.blockIndex12 i j).1 < 2864 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h10]
  have h11 : ¬ (Induced.Six.blockIndex12 i j).1 < 3120 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_neg h11]
  have hi : (Induced.Six.blockIndex12 i j).1 < 3376 := by
    rw [Induced.Six.blockIndex12_val]; omega
  rw [if_pos hi]
  have ha : ((Induced.Six.blockIndex12 i j).1-3120)/16 = i.1 := by
    rw [Induced.Six.blockIndex12_val]; omega
  have hb : ((Induced.Six.blockIndex12 i j).1-3120)%16 = j.1 := by
    rw [Induced.Six.blockIndex12_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix12 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex12 i j) s = Type12.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block24.H Block25.H
    (fun u => right (Induced.Six.blockIndex12 i j) u) i j (blockRight12 i j) s

theorem blockNonneg12 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex12 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex12 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix12, Induced.Six.blockPulled12]
  exact Induced.Six.Family12.gram_nonneg W (Type12.matrix s)
    (Type12.matrix_nonneg hs0 hs1)

theorem blockRight13 (i j : Fin 16) (u : Fin 3) :
    right (Induced.Six.blockIndex13 i j) u =
      if u.1 = 0 then Block26.H i j
      else if u.1 = 1 then Block26.H i (16+j.1)+Block26.H (16+i.1) j+Block27.H i j
      else Block26.H (16+i.1) (16+j.1) := by
  rw [((rightCheck_all (Induced.Six.blockIndex13 i j)).1 u).2]
  unfold expandedRight
  have h0 : ¬ (Induced.Six.blockIndex13 i j).1 < 16 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h0]
  have h1 : ¬ (Induced.Six.blockIndex13 i j).1 < 416 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h1]
  have h2 : ¬ (Induced.Six.blockIndex13 i j).1 < 816 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h2]
  have h3 : ¬ (Induced.Six.blockIndex13 i j).1 < 1072 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h3]
  have h4 : ¬ (Induced.Six.blockIndex13 i j).1 < 1328 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h4]
  have h5 : ¬ (Induced.Six.blockIndex13 i j).1 < 1584 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h5]
  have h6 : ¬ (Induced.Six.blockIndex13 i j).1 < 1840 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h6]
  have h7 : ¬ (Induced.Six.blockIndex13 i j).1 < 2096 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h7]
  have h8 : ¬ (Induced.Six.blockIndex13 i j).1 < 2352 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h8]
  have h9 : ¬ (Induced.Six.blockIndex13 i j).1 < 2608 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h9]
  have h10 : ¬ (Induced.Six.blockIndex13 i j).1 < 2864 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h10]
  have h11 : ¬ (Induced.Six.blockIndex13 i j).1 < 3120 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h11]
  have h12 : ¬ (Induced.Six.blockIndex13 i j).1 < 3376 := by
    rw [Induced.Six.blockIndex13_val]; omega
  rw [if_neg h12]
  have ha : ((Induced.Six.blockIndex13 i j).1-3376)/16 = i.1 := by
    rw [Induced.Six.blockIndex13_val]; omega
  have hb : ((Induced.Six.blockIndex13 i j).1-3376)%16 = j.1 := by
    rw [Induced.Six.blockIndex13_val]; omega
  dsimp only
  rw [ha, hb]

theorem blockMatrix13 (i j : Fin 16) (s : Real) :
    weightedRight (Induced.Six.blockIndex13 i j) s = Type13.matrix s i j :=
  Induced.intervalMatrix_entry_of_coefficients Block26.H Block27.H
    (fun u => right (Induced.Six.blockIndex13 i j) u) i j (blockRight13 i j) s

theorem blockNonneg13 (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin 16, ∑ j : Fin 16, weightedRight (Induced.Six.blockIndex13 i j) s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g (Induced.Six.blockIndex13 i j) : Real)*Induced.Six.density g W) := by
  simp_rw [blockMatrix13, Induced.Six.blockPulled13]
  exact Induced.Six.Family13.gram_nonneg W (Type13.matrix s)
    (Type13.matrix_nonneg hs0 hs1)

theorem dense_nonneg (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ k : Fin 3632, weightedRight k s *
      (∑ g : Fin 156, (Induced.Six.Sparse.pulled g k : Real)*Induced.Six.density g W) := by
  rw [Induced.Six.sum_all_blocks]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (blockNonneg00 W s hs0 hs1) (blockNonneg01 W s hs0 hs1)) (blockNonneg02 W s hs0 hs1)) (blockNonneg03 W s hs0 hs1)) (blockNonneg04 W s hs0 hs1)) (blockNonneg05 W s hs0 hs1)) (blockNonneg06 W s hs0 hs1)) (blockNonneg07 W s hs0 hs1)) (blockNonneg08 W s hs0 hs1)) (blockNonneg09 W s hs0 hs1)) (blockNonneg10 W s hs0 hs1)) (blockNonneg11 W s hs0 hs1)) (blockNonneg12 W s hs0 hs1)) (blockNonneg13 W s hs0 hs1))

theorem group_nonneg (W : Graphon Ω μ) (s : Real) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ g : Fin 156, weightedGroup g s*Induced.Six.density g W := by
  let w : Fin 3 → Real := fun u => if u.1 = 0 then (1-s)^2 else if u.1 = 1 then s*(1-s) else s^2
  have hw0 : w 0 = (1-s)^2 := rfl
  have hw1 : w 1 = s*(1-s) := rfl
  have hw2 : w 2 = s^2 := rfl
  have he := integer_contraction_eval (U := Fin 3) Induced.Six.Sparse.pulled
    (fun k u => right k u) (fun g u => groupTotal g u) groupTotal_exact w
    (fun g => Induced.Six.density g W)
  simp only [Fin.sum_univ_three, hw0, hw1, hw2] at he
  norm_num at he
  have h := dense_nonneg W s hs0 hs1
  unfold weightedRight at h
  unfold weightedGroup
  simp only [mul_assoc] at h ⊢
  rwa [← he]

theorem coefficient_identity (g : Fin 156) (s : Real) :
    (denominator : Real)*(Target.coefficient g : Real) -
      (denominator : Real)*target203 ((8+s)/12)*(Induced.Six.HomIdentities.plainCoefficient 0 g : Real) =
      weightedGroup g s+residualValue g s+
        ∑ j : Fin 11, multiplierValue j s*((Induced.Six.HomIdentities.edgeCoefficient j g : Real)-
          (8+s)/12*(Induced.Six.HomIdentities.plainCoefficient j g : Real)) := by
  have he := congrArg (fun f : Fin 6 → Int => ∑ k : Fin 6, (f k : Real)*Induced.basis 5 s k.1)
    (funext (fun k => (coefficientCheck_all g k).2))
  simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib] at he
  have hc :
      (∑ k : Fin 6, (((Nat.choose 5 k.1 : Int)*(denominator*Target.coefficient g) : Int) : Real)*
        Induced.basis 5 s k.1) = ((denominator*Target.coefficient g : Int) : Real) := by
    simpa only [Int.cast_mul] using Induced.constantCoefficient_eval (denominator*Target.coefficient g) s
  rw [hc] at he
  have ht :
      (∑ k : Fin 6, ((targetNumerator k*Induced.Six.HomIdentities.plainCoefficient 0 g : Int) : Real)*Induced.basis 5 s k.1) =
        (denominator : Real)*target203 ((8+s)/12)*(Induced.Six.HomIdentities.plainCoefficient 0 g : Real) := by
    rw [← targetNumerator_eval]
    simp only [Int.cast_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_right_comm _ _ _
  rw [ht] at he
  simp only [Int.cast_add, add_mul, Finset.sum_add_distrib] at he
  rw [Induced.quadraticCoefficient_eval] at he
  have hp :
      (∑ k : Fin 6, ((∑ j : Fin 11, Induced.penaltyCoefficient
        (Induced.Six.HomIdentities.plainCoefficient j g) (Induced.Six.HomIdentities.edgeCoefficient j g)
        (fun k => multiplier j k) (fun k => leftMultiplier j k) (fun k => rightMultiplier j k) k : Int) : Real)*
          Induced.basis 5 s k.1) =
        ∑ j : Fin 11, multiplierValue j s*((Induced.Six.HomIdentities.edgeCoefficient j g : Real)-
          (8+s)/12*(Induced.Six.HomIdentities.plainCoefficient j g : Real)) := by
    simp only [Int.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Induced.penaltyCoefficient_eval_twoThirdsThreeQuarters _ _ _ _ _
      (fun k => (multiplier_relations j k).1) (fun k => (multiplier_relations j k).2) s
  rw [hp] at he
  simpa only [Int.cast_mul, weightedGroup, residualValue] using he

private theorem density_eq_of_graph_eq {n : Nat}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) : homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

theorem interval_identity (W : Graphon Ω μ) (s : Real) (hp : (8+s)/12 = cliqueDensity 2 W) :
    (denominator : Real)*(homDensity graph203 W-target203 ((8+s)/12)) =
      (∑ g : Fin 156, weightedGroup g s*Induced.Six.density g W)+
        ∑ g : Fin 156, residualValue g s*Induced.Six.density g W := by
  have he := Induced.evaluated_coefficient_identity
    (fun g : Fin 156 => (Target.coefficient g : Real))
    (fun g => (Induced.Six.HomIdentities.plainCoefficient 0 g : Real))
    (fun g => weightedGroup g s) (fun g => residualValue g s)
    (fun g => Induced.Six.density g W) (fun j : Fin 11 => multiplierValue j s)
    (fun j g => (Induced.Six.HomIdentities.plainCoefficient j g : Real))
    (fun j g => (Induced.Six.HomIdentities.edgeCoefficient j g : Real))
    (denominator : Real) ((denominator : Real)*target203 ((8+s)/12)) ((8+s)/12)
    (fun g => coefficient_identity g s)
  have ht : (∑ g : Fin 156, (Target.coefficient g : Real)*Induced.Six.density g W) =
      homDensity graph203 W := by
    calc
      _ = homDensity Target.graph W := (Target.density_expansion W).symm
      _ = homDensity graph203 W := density_eq_of_graph_eq _ _ W rfl
  rw [ht, Induced.Six.HomIdentities.plain_expansion, Induced.Six.HomIdentities.empty_density, mul_one] at he
  simp_rw [Induced.Six.HomIdentities.edge_expansion, Induced.Six.HomIdentities.plain_expansion,
    Induced.Six.HomIdentities.fixed_density, ← hp] at he
  simpa only [sub_self, mul_zero, Finset.sum_const_zero, add_zero, mul_sub] using he

theorem lower_graphon_bound (W : Graphon Ω μ) (hp0 : (2 : Real)/3 ≤ cliqueDensity 2 W)
    (hp1 : cliqueDensity 2 W ≤ (3 : Real)/4) :
    target203 (cliqueDensity 2 W) ≤ homDensity graph203 W := by
  let s := 12*cliqueDensity 2 W-8
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hp : (8+s)/12 = cliqueDensity 2 W := by dsimp [s]; ring
  have he := interval_identity W s hp
  rw [hp] at he
  have hr : 0 ≤ ∑ g : Fin 156, residualValue g s*Induced.Six.density g W := by
    apply Finset.sum_nonneg
    intro g _
    apply mul_nonneg _ (Induced.Six.density_nonneg g W)
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg _ (Induced.basis_nonneg 5 k.1 hs0 hs1)
    exact_mod_cast (coefficientCheck_all g k).1
  have hn : 0 ≤ (denominator : Real)*(homDensity graph203 W-target203 (cliqueDensity 2 W)) := by
    rw [he]
    exact add_nonneg (group_nonneg W s hs0 hs1) hr
  have hd : (0 : Real) < (denominator : Real) := by norm_num [denominator]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp hn)
#print axioms lower_graphon_bound
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Lower
