import Taeyoung.Methods.RootedSOS.Induced.Six.SparseRowData
import Taeyoung.Methods.RootedSOS.Induced.Six.SparseColumnData
import Taeyoung.Methods.RootedSOS.SparseContraction
import Taeyoung.Methods.RootedSOS.Induced.Six.Family00
import Taeyoung.Methods.RootedSOS.Induced.Six.Family01
import Taeyoung.Methods.RootedSOS.Induced.Six.Family02
import Taeyoung.Methods.RootedSOS.Induced.Six.Family03
import Taeyoung.Methods.RootedSOS.Induced.Six.Family04
import Taeyoung.Methods.RootedSOS.Induced.Six.Family05
import Taeyoung.Methods.RootedSOS.Induced.Six.Family06
import Taeyoung.Methods.RootedSOS.Induced.Six.Family07
import Taeyoung.Methods.RootedSOS.Induced.Six.Family08
import Taeyoung.Methods.RootedSOS.Induced.Six.Family09
import Taeyoung.Methods.RootedSOS.Induced.Six.Family10
import Taeyoung.Methods.RootedSOS.Induced.Six.Family11
import Taeyoung.Methods.RootedSOS.Induced.Six.Family12
import Taeyoung.Methods.RootedSOS.Induced.Six.Family13
namespace Taeyoung.Methods.RootedSOS.Induced.Six.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
def rowSize (g : Fin 156) : Nat := (rowLength g).toNat
def columnSize (k : Fin 3632) : Nat := (columnLength k).toNat
abbrev RowTerm := Σ g, Fin (rowSize g)
abbrev ColumnTerm := Σ k, Fin (columnSize k)
theorem rowSize_pos : ∀ g, 0 < rowSize g := by decide +kernel
def rowEntry (x : RowTerm) : Nat := (rowData ((rowOffset x.1).toNat+x.2.1)).toNat
def rowColumn (x : RowTerm) : Fin 3632 := ⟨rowEntry x%3632, Nat.mod_lt _ (by decide)⟩
def rowPosition (x : RowTerm) : Nat := rowEntry x/3632%110
def rowValue (x : RowTerm) : Int := (rowEntry x/399520 : Nat)-(32768 : Int)
def rowKey (x : RowTerm) : Nat × Nat := (rowColumn x,rowPosition x)
def columnEntry (x : ColumnTerm) : Nat := (columnData ((columnOffset x.1).toNat+x.2.1)).toNat
def toRow (x : ColumnTerm) : RowTerm :=
  let g : Fin 156 := ⟨columnEntry x%156, Nat.mod_lt _ (by decide)⟩
  ⟨g,⟨(columnEntry x/156)%rowSize g,Nat.mod_lt _ (rowSize_pos g)⟩⟩
def flatCode (k : Fin 3632) : Nat :=
  if k.1 < 16 then
    Family00.countCode ⟨((k.1-0)/4)%4, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-0)%4, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 416 then
    Family01.countCode ⟨((k.1-16)/20)%20, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-16)%20, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 816 then
    Family02.countCode ⟨((k.1-416)/20)%20, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-416)%20, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 1072 then
    Family03.countCode ⟨((k.1-816)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-816)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 1328 then
    Family04.countCode ⟨((k.1-1072)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-1072)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 1584 then
    Family05.countCode ⟨((k.1-1328)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-1328)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 1840 then
    Family06.countCode ⟨((k.1-1584)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-1584)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 2096 then
    Family07.countCode ⟨((k.1-1840)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-1840)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 2352 then
    Family08.countCode ⟨((k.1-2096)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-2096)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 2608 then
    Family09.countCode ⟨((k.1-2352)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-2352)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 2864 then
    Family10.countCode ⟨((k.1-2608)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-2608)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 3120 then
    Family11.countCode ⟨((k.1-2864)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-2864)%16, Nat.mod_lt _ (by decide)⟩ else
  if k.1 < 3376 then
    Family12.countCode ⟨((k.1-3120)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-3120)%16, Nat.mod_lt _ (by decide)⟩ else
    Family13.countCode ⟨((k.1-3376)/16)%16, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-3376)%16, Nat.mod_lt _ (by decide)⟩

def pulled (g : Fin 156) (k : Fin 3632) : Int := decodeSignedDigit 65537 32768 (flatCode k) g
def columnCheck (k : Fin 3632) : Prop :=
  (∀ j : Fin (columnSize k), rowKey (toRow ⟨k,j⟩) = (k.1,j.1)) ∧
  (∑ j : Fin (columnSize k), (rowValue (toRow ⟨k,j⟩)).natAbs : Nat) ≤ 32768 ∧
  (flatCode k : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 +
    ∑ j : Fin (columnSize k), rowValue (toRow ⟨k,j⟩)*groupPower (toRow ⟨k,j⟩).1
instance (k : Fin 3632) : Decidable (columnCheck k) := by unfold columnCheck; infer_instance
theorem term_card : Fintype.card ColumnTerm = Fintype.card RowTerm := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  decide +kernel
end Taeyoung.Methods.RootedSOS.Induced.Six.Sparse
