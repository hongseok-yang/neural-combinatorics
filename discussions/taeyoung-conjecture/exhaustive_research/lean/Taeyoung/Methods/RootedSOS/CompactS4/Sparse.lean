import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks0000
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks0512
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks1024
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks1536
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks2048
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks2560
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks3072
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks3584
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks4096
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks4608
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks5120
import Taeyoung.Methods.RootedSOS.CompactS4.SparseChecks5632
namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem column_check (k : Fin 5820) : columnCheck k := by
  by_cases h : k.1 < 512
  · let j : Fin 512 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_0000 j
  by_cases h : k.1 < 1024
  · let j : Fin 512 := ⟨k.1-512, by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_0512 j
  by_cases h : k.1 < 1536
  · let j : Fin 512 := ⟨k.1-1024, by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_1024 j
  by_cases h : k.1 < 2048
  · let j : Fin 512 := ⟨k.1-1536, by omega⟩
    have he : (⟨1536+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_1536 j
  by_cases h : k.1 < 2560
  · let j : Fin 512 := ⟨k.1-2048, by omega⟩
    have he : (⟨2048+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_2048 j
  by_cases h : k.1 < 3072
  · let j : Fin 512 := ⟨k.1-2560, by omega⟩
    have he : (⟨2560+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_2560 j
  by_cases h : k.1 < 3584
  · let j : Fin 512 := ⟨k.1-3072, by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_3072 j
  by_cases h : k.1 < 4096
  · let j : Fin 512 := ⟨k.1-3584, by omega⟩
    have he : (⟨3584+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_3584 j
  by_cases h : k.1 < 4608
  · let j : Fin 512 := ⟨k.1-4096, by omega⟩
    have he : (⟨4096+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_4096 j
  by_cases h : k.1 < 5120
  · let j : Fin 512 := ⟨k.1-4608, by omega⟩
    have he : (⟨4608+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_4608 j
  by_cases h : k.1 < 5632
  · let j : Fin 512 := ⟨k.1-5120, by omega⟩
    have he : (⟨5120+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_5120 j
  by_cases h : k.1 < 5820
  · let j : Fin 188 := ⟨k.1-5632, by omega⟩
    have he : (⟨5632+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_5632 j
  omega

theorem key_toRow (x : ColumnTerm) : rowKey (toRow x) = (x.1.1,x.2.1) :=
  (column_check x.1).1 x.2

theorem toRow_injective : Function.Injective toRow := by
  intro x y h
  have he : (x.1.1,x.2.1) = (y.1.1,y.2.1) := by
    rw [← key_toRow x, ← key_toRow y, h]
  rcases x with ⟨x,k⟩
  rcases y with ⟨y,l⟩
  have hxy : x = y := Fin.ext (congrArg Prod.fst he)
  subst y
  have hkl : k = l := Fin.ext (congrArg Prod.snd he)
  subst l
  rfl

noncomputable def transposeEquiv : ColumnTerm ≃ RowTerm :=
  Equiv.ofBijective toRow ((Fintype.bijective_iff_injective_and_card toRow).2
    ⟨toRow_injective, term_card⟩)

theorem transpose_column (x : ColumnTerm) : rowColumn (transposeEquiv x) = x.1 := by
  apply Fin.ext
  exact congrArg Prod.fst (key_toRow x)

theorem pulled_eq_list (g : Fin 143) (k : Fin 5820) :
    pulled g k = ∑ j : Fin (columnSize k),
      if (toRow ⟨k,j⟩).1 = g then rowValue (toRow ⟨k,j⟩) else 0 := by
  apply listedCoefficient_of_encoding (base := 1153) (bound := 576) (code := flatCode k)
    (fun j : Fin (columnSize k) => (toRow ⟨k,j⟩).1)
    (fun j => rowValue (toRow ⟨k,j⟩)) (by decide) (column_check k).2.1
  have hoff : (576 : Int) * geometricEncoding 1153 143 = 347184995284419152579010608988621640285959390865668050177258020656213911144921270691292057289534798035430816543802166330100688072804082881928004452894645942632869813590577031638420356825878444106618613999556010957929901144582020745618655076144699989213335331780477915688791626158192837700732897691296813628026173725694433681621753611652857280206182452831864650984262291962108015857933847640246172336562870877459027969159565557574678897088 := by decide +kernel
  simp only [Nat.cast_ofNat]
  rw [hoff]
  simpa only [Young4.groupPower_exact] using (column_check k).2.2

theorem contraction (g : Fin 143) (v : Fin 5820 → Int) :
    (∑ k, pulled g k * v k) =
      ∑ j : Fin (rowSize g), rowValue ⟨g,j⟩ * v (rowColumn ⟨g,j⟩) := by
  simp_rw [pulled_eq_list]
  exact sparse_contraction rowSize columnSize rowColumn rowValue transposeEquiv transpose_column v g

#print axioms contraction
end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
