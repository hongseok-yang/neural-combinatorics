import Taeyoung.Methods.RootedSOS.CompactS4.SparseRowData
import Taeyoung.Methods.RootedSOS.CompactS4.SparseColumnData
import Taeyoung.Methods.RootedSOS.SparseContraction
import Taeyoung.Methods.RootedSOS.CompactS4.Young4
import Taeyoung.Methods.RootedSOS.CompactS4.Young31
import Taeyoung.Methods.RootedSOS.CompactS4.Young22
import Taeyoung.Methods.RootedSOS.CompactS4.Young211
import Taeyoung.Methods.RootedSOS.CompactS4.Young1111

namespace Taeyoung.Methods.RootedSOS.CompactS4.Sparse
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

def rowSize (g : Fin 143) : Nat := (rowLength g).toNat
def columnSize (k : Fin 5820) : Nat := (columnLength k).toNat
abbrev RowTerm := Σ g, Fin (rowSize g)
abbrev ColumnTerm := Σ k, Fin (columnSize k)

theorem rowSize_pos : ∀ g, 0 < rowSize g := by decide +kernel

def rowEntry (x : RowTerm) : Nat := (rowData ((rowOffset x.1).toNat+x.2.1)).toNat
def rowColumn (x : RowTerm) : Fin 5820 := ⟨rowEntry x % 5820, Nat.mod_lt _ (by decide)⟩
def rowPosition (x : RowTerm) : Nat := rowEntry x / 5820 % 18
def rowValue (x : RowTerm) : Int := (rowEntry x / 104760 : Nat) - (576 : Int)
def rowKey (x : RowTerm) : Nat × Nat := (rowColumn x, rowPosition x)

def columnEntry (x : ColumnTerm) : Nat := (columnData ((columnOffset x.1).toNat+x.2.1)).toNat
def toRow (x : ColumnTerm) : RowTerm :=
  let g : Fin 143 := ⟨columnEntry x % 143, Nat.mod_lt _ (by decide)⟩
  ⟨g, ⟨(columnEntry x / 143) % rowSize g, Nat.mod_lt _ (rowSize_pos g)⟩⟩

def flatCode (k : Fin 5820) : Nat :=
  if h : k.1 < 1024 then
    Young4.code ⟨((k.1-0)/32)%32, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-0)%32, Nat.mod_lt _ (by decide)⟩ else
  if h : k.1 < 3728 then
    Young31.code ⟨((k.1-1024)/52)%52, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-1024)%52, Nat.mod_lt _ (by decide)⟩ else
  if h : k.1 < 4884 then
    Young22.code ⟨((k.1-3728)/34)%34, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-3728)%34, Nat.mod_lt _ (by decide)⟩ else
  if h : k.1 < 5784 then
    Young211.code ⟨((k.1-4884)/30)%30, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-4884)%30, Nat.mod_lt _ (by decide)⟩ else
    Young1111.code ⟨((k.1-5784)/6)%6, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-5784)%6, Nat.mod_lt _ (by decide)⟩

def pulled (g : Fin 143) (k : Fin 5820) : Int :=
  decodeSignedDigit 1153 576 (flatCode k) g

def columnCheck (k : Fin 5820) : Prop :=
  (∀ j : Fin (columnSize k), rowKey (toRow ⟨k,j⟩) = (k.1,j.1)) ∧
  (∑ j : Fin (columnSize k), (rowValue (toRow ⟨k,j⟩)).natAbs : Nat) ≤ 576 ∧
  (flatCode k : Int) = 347184995284419152579010608988621640285959390865668050177258020656213911144921270691292057289534798035430816543802166330100688072804082881928004452894645942632869813590577031638420356825878444106618613999556010957929901144582020745618655076144699989213335331780477915688791626158192837700732897691296813628026173725694433681621753611652857280206182452831864650984262291962108015857933847640246172336562870877459027969159565557574678897088 +
    ∑ j : Fin (columnSize k), rowValue (toRow ⟨k,j⟩) * Young4.groupPower (toRow ⟨k,j⟩).1

instance (k : Fin 5820) : Decidable (columnCheck k) := by unfold columnCheck; infer_instance

theorem term_card : Fintype.card ColumnTerm = Fintype.card RowTerm := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  decide +kernel

end Taeyoung.Methods.RootedSOS.CompactS4.Sparse
