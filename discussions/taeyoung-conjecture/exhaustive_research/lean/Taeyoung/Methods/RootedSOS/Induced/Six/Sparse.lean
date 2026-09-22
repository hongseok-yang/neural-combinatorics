import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks0000
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks0512
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks1024
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks1536
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks2048
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks2560
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks3072
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseChecks3584
namespace Taeyoung.Methods.RootedSOS.Induced.Six
theorem Sparse.columnCheck_all (k : Fin 3632) : Sparse.columnCheck k := by
  by_cases h : k.1 < 512
  · let j : Fin 512 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_0000 j
  by_cases h : k.1 < 1024
  · let j : Fin 512 := ⟨k.1-512, by omega⟩
    have he : (⟨512+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_0512 j
  by_cases h : k.1 < 1536
  · let j : Fin 512 := ⟨k.1-1024, by omega⟩
    have he : (⟨1024+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_1024 j
  by_cases h : k.1 < 2048
  · let j : Fin 512 := ⟨k.1-1536, by omega⟩
    have he : (⟨1536+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_1536 j
  by_cases h : k.1 < 2560
  · let j : Fin 512 := ⟨k.1-2048, by omega⟩
    have he : (⟨2048+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_2048 j
  by_cases h : k.1 < 3072
  · let j : Fin 512 := ⟨k.1-2560, by omega⟩
    have he : (⟨2560+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_2560 j
  by_cases h : k.1 < 3584
  · let j : Fin 512 := ⟨k.1-3072, by omega⟩
    have he : (⟨3072+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_3072 j
  by_cases h : k.1 < 3632
  · let j : Fin 48 := ⟨k.1-3584, by omega⟩
    have he : (⟨3584+j.1, by omega⟩ : Fin 3632) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using SparseChecks_3584 j
  omega

end Taeyoung.Methods.RootedSOS.Induced.Six
namespace Taeyoung.Methods.RootedSOS.Induced.Six.Sparse
theorem column_check (k : Fin 3632) : columnCheck k := columnCheck_all k
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

theorem pulled_eq_list (g : Fin 156) (k : Fin 3632) :
    pulled g k = ∑ j : Fin (columnSize k),
      if (toRow ⟨k,j⟩).1 = g then rowValue (toRow ⟨k,j⟩) else 0 := by
  apply listedCoefficient_of_encoding (base := 65537) (bound := 32768) (code := flatCode k)
    (fun j : Fin (columnSize k) => (toRow ⟨k,j⟩).1)
    (fun j => rowValue (toRow ⟨k,j⟩)) (by decide) (column_check k).2.1
  have hoff : (32768 : Int) * geometricEncoding 65537 156 = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 := by decide +kernel
  simp only [Nat.cast_ofNat]
  rw [hoff]
  simpa only [groupPower_exact] using (column_check k).2.2

theorem contraction (g : Fin 156) (v : Fin 3632 → Int) :
    (∑ k, pulled g k * v k) =
      ∑ j : Fin (rowSize g), rowValue ⟨g,j⟩ * v (rowColumn ⟨g,j⟩) := by
  simp_rw [pulled_eq_list]
  exact sparse_contraction rowSize columnSize rowColumn rowValue transposeEquiv transpose_column v g

#print axioms contraction
end Taeyoung.Methods.RootedSOS.Induced.Six.Sparse
