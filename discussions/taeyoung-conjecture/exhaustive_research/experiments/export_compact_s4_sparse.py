"""Produce mutually inverse row/column listings of the shared sparse pullback.

The proposed equivalence is data, not a proof. Lean must check both inverse
equations, the entry bounds, and every packed column before it is used.
"""

import json
from pathlib import Path


def main():
    common = json.loads(Path("experiments/s4_lean_common.json").read_text(encoding="utf-8"))
    dimensions = [len(common["young_bases"][name][0]) for name in common["names"]]
    offsets = [0]
    for d in dimensions:
        offsets.append(offsets[-1]+d*d)
    rows = []
    columns = [[] for _ in range(offsets[-1])]
    for g, blocks in enumerate(common["pulled_groups"]):
        row = []
        for b, entries in enumerate(blocks):
            for i,j,value in entries:
                k=offsets[b]+dimensions[b]*i+j
                row.append([k,int(value)])
        row.sort()
        assert len({k for k,_ in row}) == len(row)
        rows.append(row)
        for pos,(k,value) in enumerate(row):
            columns[k].append([g,pos,value])
    inverse_positions = [[None for _ in row] for row in rows]
    for k,col in enumerate(columns):
        assert sum(abs(value) for _,_,value in col) <= 576
        for pos,(g,row_pos,value) in enumerate(col):
            assert rows[g][row_pos]==[k,value]
            inverse_positions[g][row_pos]=pos
    assert all(p is not None for row in inverse_positions for p in row)
    payload = {
        "row_count":len(rows), "column_count":len(columns),
        "entry_count":sum(map(len,rows)), "block_dimensions":dimensions,
        "block_offsets":offsets, "rows":rows, "columns":columns,
        "row_to_column_positions":inverse_positions,
        "status":"untrusted transpose witness; requires Lean checking",
    }
    output=Path("experiments/s4_compact_sparse_witness.json")
    output.write_text(json.dumps(payload,separators=(",",":"))+"\n",encoding="utf-8")
    print(output,"entries",payload["entry_count"],"bytes",output.stat().st_size,
          "max row",max(map(len,rows)),"max column",max(map(len,columns)))


if __name__=="__main__":
    main()
