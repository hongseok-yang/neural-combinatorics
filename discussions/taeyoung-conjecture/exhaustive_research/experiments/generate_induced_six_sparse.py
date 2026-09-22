"""Build and certify the sparse transpose of the 14 induced flag families."""

import json
from pathlib import Path
import re

import generate_compact_s4_group_totals as chunks
from generate_compact_s4_psd import table

ROOT = Path('lean/Taeyoung/Methods/RootedSOS/Induced/Six')
PARENT = 'Taeyoung.Methods.RootedSOS.Induced.Six'
NS = PARENT+'.Sparse'
PREFIX = 'Taeyoung.Methods.RootedSOS'


def vector(name, values):
    parts=[]
    text=''
    for start in range(0,len(values),512):
        p=f'{name}Part{start}'
        subset=values[start:start+512]
        text+=f'private def {p} : PackedTable := {table(subset)}\n'
        parts.append((len(subset),p))
    def tree(parts):
        if len(parts)==1:
            return parts[0][1]
        mid=len(parts)//2
        return f'(.node {sum(n for n,_ in parts[:mid])} {tree(parts[:mid])} {tree(parts[mid:])})'
    text+=f'private def {name}Data : PackedTable := {tree(parts)}\ndef {name} (i : Nat) : Int := {name}Data.get i\n'
    return text


def write(name, body):
    (ROOT/f'{name}.lean').write_text(body,encoding='utf-8')


def main():
    common=json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    base,bound=common['histogram_base'],common['histogram_bound']
    columns=[]; rows=[[] for _ in range(156)]; offsets=[0]
    dims=[]
    for t in common['types']:
        dims.append(t['flag_count'])
        for row in t['encoded_counts']:
            for encoded in row:
                encoded=int(encoded); k=len(columns); col=[]
                for g in range(156):
                    value=encoded%base;encoded//=base
                    if value:
                        col.append([g,len(rows[g]),value]);rows[g].append([k,value])
                assert encoded==0
                columns.append(col)
        offsets.append(len(columns))
    count=len(columns)
    inv=[[None]*len(row) for row in rows]
    for k,col in enumerate(columns):
        assert sum(v for _,_,v in col)<=bound
        for pos,(g,rpos,v) in enumerate(col):inv[g][rpos]=pos
    width=max(map(len,columns))
    sparse=dict(row_count=156,column_count=count,entry_count=sum(map(len,rows)),
                block_dimensions=dims,block_offsets=offsets,rows=rows,columns=columns,
                row_to_column_positions=inv,histogram_base=base,histogram_bound=bound,
                status='Untrusted transpose witness; requires Lean checking')
    Path('experiments/induced_six_sparse_witness.json').write_text(json.dumps(sparse,separators=(',',':'))+'\n',encoding='utf-8')
    row_data=[]; col_data=[]; row_offsets=[0]; col_offsets=[0]
    for g,row in enumerate(rows):
        row_data.extend(k+count*(inv[g][pos]+width*(value+bound)) for pos,(k,value) in enumerate(row))
        row_offsets.append(len(row_data))
    for col in columns:
        col_data.extend(g+156*pos for g,pos,_ in col)
        col_offsets.append(len(col_data))
    for kind,items in [('Row',[('rowOffset',row_offsets),('rowLength',list(map(len,rows))),('rowData',row_data)]),
                       ('Column',[('columnOffset',col_offsets),('columnLength',list(map(len,columns))),('columnData',col_data)])]:
        write(f'Sparse{kind}Data',f'import {PREFIX}.PackedMatrix\nnamespace {NS}\n'
              'set_option maxRecDepth 1000000\nset_option maxHeartbeats 40000000\n'+
              ''.join(vector(name,values) for name,values in items)+f'end {NS}\n')
    flat=''
    for ti,d in enumerate(dims):
        first,stop=offsets[ti:ti+2]
        if ti<13:flat+=f'  if k.1 < {stop} then\n'
        flat+=f'    Family{ti:02d}.countCode ⟨((k.1-{first})/{d})%{d}, Nat.mod_lt _ (by decide)⟩\n'
        flat+=f'      ⟨(k.1-{first})%{d}, Nat.mod_lt _ (by decide)⟩'+(' else\n' if ti<13 else '\n')
    offset=bound*sum(base**g for g in range(156))
    imports='\n'.join(f'import {PARENT}.Family{ti:02d}' for ti in range(14))
    write('SparseBase',f'''import {PARENT}.SparseRowData
import {PARENT}.SparseColumnData
import {PREFIX}.SparseContraction
{imports}
namespace {NS}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
def rowSize (g : Fin 156) : Nat := (rowLength g).toNat
def columnSize (k : Fin {count}) : Nat := (columnLength k).toNat
abbrev RowTerm := Σ g, Fin (rowSize g)
abbrev ColumnTerm := Σ k, Fin (columnSize k)
theorem rowSize_pos : ∀ g, 0 < rowSize g := by decide +kernel
def rowEntry (x : RowTerm) : Nat := (rowData ((rowOffset x.1).toNat+x.2.1)).toNat
def rowColumn (x : RowTerm) : Fin {count} := ⟨rowEntry x%{count}, Nat.mod_lt _ (by decide)⟩
def rowPosition (x : RowTerm) : Nat := rowEntry x/{count}%{width}
def rowValue (x : RowTerm) : Int := (rowEntry x/{count*width} : Nat)-({bound} : Int)
def rowKey (x : RowTerm) : Nat × Nat := (rowColumn x,rowPosition x)
def columnEntry (x : ColumnTerm) : Nat := (columnData ((columnOffset x.1).toNat+x.2.1)).toNat
def toRow (x : ColumnTerm) : RowTerm :=
  let g : Fin 156 := ⟨columnEntry x%156, Nat.mod_lt _ (by decide)⟩
  ⟨g,⟨(columnEntry x/156)%rowSize g,Nat.mod_lt _ (rowSize_pos g)⟩⟩
def flatCode (k : Fin {count}) : Nat :=
{flat}
def pulled (g : Fin 156) (k : Fin {count}) : Int := decodeSignedDigit {base} {bound} (flatCode k) g
def columnCheck (k : Fin {count}) : Prop :=
  (∀ j : Fin (columnSize k), rowKey (toRow ⟨k,j⟩) = (k.1,j.1)) ∧
  (∑ j : Fin (columnSize k), (rowValue (toRow ⟨k,j⟩)).natAbs : Nat) ≤ {bound} ∧
  (flatCode k : Int) = {offset} +
    ∑ j : Fin (columnSize k), rowValue (toRow ⟨k,j⟩)*groupPower (toRow ⟨k,j⟩).1
instance (k : Fin {count}) : Decidable (columnCheck k) := by unfold columnCheck; infer_instance
theorem term_card : Fintype.card ColumnTerm = Fintype.card RowTerm := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  decide +kernel
end {NS}
''')
    # Chunk helper separates module paths and declaration namespaces here.
    chunks.ROOT=ROOT;chunks.NS=PARENT
    imports,thm=chunks.chunks('SparseChecks','SparseBase','Sparse.columnCheck',count,512,64)
    # Its generated theorem name contains the namespace prefix deliberately.
    template=Path('lean/Taeyoung/Methods/RootedSOS/CompactS4/Sparse.lean').read_text(encoding='utf-8')
    tail=template[template.index('theorem key_toRow'):]
    tail=tail[:tail.rindex('end Taeyoung')]
    old_offset=re.search(r'have hoff.*?= (\d+) := by decide',tail,flags=re.S).group(1)
    tail=tail.replace(old_offset,str(offset)).replace('Young4.groupPower_exact','groupPower_exact')
    for old,new in [('5820',str(count)),('143','156'),('1153',str(base)),('576',str(bound))]:
        tail=re.sub(r'\b'+old+r'\b',new,tail)
    write('Sparse',imports+f'\nnamespace {PARENT}\n'+thm+f'\nend {PARENT}\nnamespace {NS}\n'+
          f'theorem column_check (k : Fin {count}) : columnCheck k := columnCheck_all k\n'+tail+f'end {NS}\n')
    print(f'Generated sparse transpose: {count} columns, {len(row_data)} nonzeros, width {width}.',flush=True)


if __name__ == '__main__':
    main()
