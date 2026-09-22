"""Generate a kernel-checked sparse transpose of the shared Young pullback.

Only a left inverse and equal finite cardinalities are needed. The column
listing is then a proved bijection onto the row listing, including multiplicity.
"""

import json
from pathlib import Path

from generate_compact_s4_psd import PREFIX, table


ROOT = Path('lean/Taeyoung/Methods/RootedSOS/CompactS4')
NS = f'{PREFIX}.CompactS4.Sparse'


def write(name, body):
    (ROOT/f'{name}.lean').write_text(body, encoding='utf-8')


def vector(name, values):
    return f'private def {name}Data : PackedTable :=\n{table(values)}\n\ndef {name} (i : Nat) : Int := {name}Data.get i\n'


def main():
    s = json.loads(Path('experiments/s4_compact_sparse_witness.json').read_text())
    c = json.loads(Path('experiments/s4_lean_common.json').read_text())
    row_offsets, col_offsets = [0], [0]
    row_data, col_data = [], []
    for g, row in enumerate(s['rows']):
        for pos, (k, value) in enumerate(row):
            row_data.append(k+5820*(s['row_to_column_positions'][g][pos]+18*(value+576)))
        row_offsets.append(len(row_data))
    for col in s['columns']:
        col_data.extend(g+143*pos for g,pos,_ in col)
        col_offsets.append(len(col_data))
    assert row_offsets[-1] == col_offsets[-1] == 34842
    write('SparseRowData', f'import {PREFIX}.PackedMatrix\n\nnamespace {NS}\n'
          'set_option maxRecDepth 1000000\nset_option maxHeartbeats 40000000\n'
          + vector('rowOffset', row_offsets) + vector('rowLength', list(map(len,s['rows'])))
          + vector('rowData', row_data)
          + f'\nend {NS}\n')
    write('SparseColumnData', f'import {PREFIX}.PackedMatrix\n\nnamespace {NS}\n'
          'set_option maxRecDepth 1000000\nset_option maxHeartbeats 40000000\n'
          + vector('columnOffset', col_offsets) + vector('columnLength', list(map(len,s['columns'])))
          + vector('columnData', col_data)
          + f'\nend {NS}\n')
    imports = '\n'.join(f'import {PREFIX}.CompactS4.Young{tag}' for tag in c['names'])
    branch = ''
    for b,(tag,d) in enumerate(zip(c['names'],s['block_dimensions'])):
        offset,stop=s['block_offsets'][b:b+2]
        branch+=f'''  {'if' if b<4 else 'let'} {'h : k.1 < '+str(stop)+' then' if b<4 else '_last := ()'}
    Young{tag}.code ⟨((k.1-{offset})/{d})%{d}, Nat.mod_lt _ (by decide)⟩
      ⟨(k.1-{offset})%{d}, Nat.mod_lt _ (by decide)⟩{' else' if b<4 else ''}
'''
    # The final branch needs no dummy let.
    branch=branch.replace('  let _last := ()\n','')
    base=f'''import {PREFIX}.CompactS4.SparseRowData
import {PREFIX}.CompactS4.SparseColumnData
import {PREFIX}.SparseContraction
{imports}

namespace {NS}
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
{branch}
def pulled (g : Fin 143) (k : Fin 5820) : Int :=
  decodeSignedDigit 1153 576 (flatCode k) g

def columnCheck (k : Fin 5820) : Prop :=
  (∀ j : Fin (columnSize k), rowKey (toRow ⟨k,j⟩) = (k.1,j.1)) ∧
  (∑ j : Fin (columnSize k), (rowValue (toRow ⟨k,j⟩)).natAbs : Nat) ≤ 576 ∧
  (flatCode k : Int) = {576*sum(1153**g for g in range(143))} +
    ∑ j : Fin (columnSize k), rowValue (toRow ⟨k,j⟩) * Young4.groupPower (toRow ⟨k,j⟩).1

instance (k : Fin 5820) : Decidable (columnCheck k) := by unfold columnCheck; infer_instance

theorem term_card : Fintype.card ColumnTerm = Fintype.card RowTerm := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  decide +kernel

end {NS}
'''
    write('SparseBase',base)
    chunks=[]
    # 128 columns per theorem, 512 per source, to release evaluator caches.
    for start in range(0,5820,512):
        stop=min(start+512,5820)
        name=f'SparseChecks{start:04d}'
        declarations=[]
        cases=''
        for a in range(start,stop,128):
            z=min(a+128,stop)
            declarations.append(f'''private theorem checked_{a:04d} : ∀ i : Fin {z-a},
    columnCheck ⟨{a}+i.1, by omega⟩ := by decide +kernel
''')
            cases+=f'''  by_cases h : i.1 < {z-start}
  · let j : Fin {z-a} := ⟨i.1-({a-start}), by omega⟩
    have he : (⟨{a}+j.1, by omega⟩ : Fin 5820) = ⟨{start}+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using checked_{a:04d} j
'''
        write(name,f'''import {PREFIX}.CompactS4.SparseBase
namespace {NS}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
{''.join(declarations)}
theorem columns_{start:04d} (i : Fin {stop-start}) : columnCheck ⟨{start}+i.1, by omega⟩ := by
{cases}  omega
end {NS}
''')
        chunks.append((start,stop,name))
    cases=''
    for start,stop,_ in chunks:
        cases+=f'''  by_cases h : k.1 < {stop}
  · let j : Fin {stop-start} := ⟨k.1-{start}, by omega⟩
    have he : (⟨{start}+j.1, by omega⟩ : Fin 5820) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using columns_{start:04d} j
'''
    final='\n'.join(f'import {PREFIX}.CompactS4.{n}' for _,_,n in chunks)
    final+=f'''
namespace {NS}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem column_check (k : Fin 5820) : columnCheck k := by
{cases}  omega

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
  have hoff : (576 : Int) * geometricEncoding 1153 143 = {576*sum(1153**g for g in range(143))} := by decide +kernel
  simp only [Nat.cast_ofNat]
  rw [hoff]
  simpa only [Young4.groupPower_exact] using (column_check k).2.2

theorem contraction (g : Fin 143) (v : Fin 5820 → Int) :
    (∑ k, pulled g k * v k) =
      ∑ j : Fin (rowSize g), rowValue ⟨g,j⟩ * v (rowColumn ⟨g,j⟩) := by
  simp_rw [pulled_eq_list]
  exact sparse_contraction rowSize columnSize rowColumn rowValue transposeEquiv transpose_column v g

#print axioms contraction
end {NS}
'''
    write('Sparse',final)
    print('Generated',4+len(chunks),'shared sparse modules')


if __name__=='__main__':
    main()
