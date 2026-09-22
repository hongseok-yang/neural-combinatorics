"""Derive small integer group totals and sparse four-slot contraction witnesses."""

import argparse
import json
from math import comb, lcm
from pathlib import Path

from flint import fmpz_mat
import sympy as sp


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate')
    args=parser.parse_args()
    c=json.loads(Path(args.certificate).read_text(encoding='utf-8'))
    common=json.loads(Path('experiments/s4_lean_common.json').read_text(encoding='utf-8'))
    sparse=json.loads(Path('experiments/s4_compact_sparse_witness.json').read_text(encoding='utf-8'))
    suffix=c.get('lean_namespace_suffix', '')
    lower,upper=map(sp.Rational,c['interval'])
    affine_step=1
    if suffix:
        assert 0 <= lower < upper <= 1
        step=upper-lower
        affine_denominator=lcm(int(lower.q),int(step.q))
        offset_numerator=int(lower*affine_denominator)
        affine_step=int(step*affine_denominator)
        scale=affine_denominator**5
    else:
        assert c['interval'] in [['1/2','1'],['2/3','1'],['3/4','1']]
        offset_numerator,affine_denominator=int(lower.p),int(lower.q)
        scale=affine_denominator**4
    atlas=int(c['atlas'])
    t=sp.Symbol('t')
    target=sp.Poly(sp.expand(scale*sp.sympify(c['phi'])),t)
    if any(target.nth(j).q != 1 for j in range(6)):
        scale=affine_denominator**5
        target=sp.Poly(sp.expand(scale*sp.sympify(c['phi'])),t)
    assert target.degree() <= 5
    target_coefficients=[target.nth(j) for j in range(6)]
    assert all(x.q==1 for x in target_coefficients)
    target_coefficients=list(map(int,target_coefficients))
    assert c['young_bases']==common['young_bases']
    full=[]
    for n,g in zip(c['face_bases'],c['gram_scaled']):
        n=fmpz_mat(n)
        full.append(n*fmpz_mat(g)*n.transpose())
    right=[]
    for b,d in enumerate(sparse['block_dimensions']):
        for i in range(d):
            for j in range(d):
                right.append([24*int(full[b][i,j]),
                              24*int(full[b][i,d+j]+full[b][d+i,j]),
                              24*int(full[b][d+i,d+j]),24*int(full[b+5][i,j])])
    assert len(right)==5820
    totals=[[sum(value*right[k][slot] for k,value in row) for slot in range(4)]
            for row in sparse['rows']]
    right_bound=max(abs(x) for row in right for x in row)
    bound=5820*576*right_bound
    base=2*bound+1
    offset=bound*sum(base**s for s in range(4))
    right_encoded=[sum(x*base**s for s,x in enumerate(row)) for row in right]
    total_encoded=[offset+sum(x*base**s for s,x in enumerate(row)) for row in totals]
    assert all(abs(x)<=bound for row in totals for x in row)
    for g,row in enumerate(sparse['rows']):
        assert total_encoded[g]==offset+sum(value*right_encoded[k] for k,value in row)
    by_core={}
    representatives=[]
    for g,(core,isolated) in enumerate(common['raw_group_keys']):
        representatives.append(by_core.setdefault(core,g))
    coefficients=[[0]*6 for _ in totals]
    for g,(core,isolated) in enumerate(common['raw_group_keys']):
        polynomial=[totals[g][0],totals[g][1]+totals[g][3],totals[g][2]-totals[g][3]]
        for i in range(isolated+1):
            multiplier=(comb(isolated,i)*(scale//affine_denominator**isolated)*
                        offset_numerator**(isolated-i)*affine_step**i)
            for j,value in enumerate(polynomial):
                coefficients[representatives[g]][i+j]+=multiplier*value
    expected=[[0]*6 for _ in totals]
    expected[by_core[atlas]][0]=scale*c['gram_denominator']
    for j,value in enumerate(target_coefficients):
        expected[by_core[0]][j]-=value*c['gram_denominator']
    assert coefficients==expected
    payload={'atlas':atlas,'denominator':c['gram_denominator'],'right':right,
             'interval':c['interval'],'scale':scale,
             'affine_offset':offset_numerator,'affine_denominator':affine_denominator,
             'target_coefficients':target_coefficients,
             'right_bound':right_bound,'bound':bound,'base':base,
             'right_encoded':right_encoded,'group_totals':totals,
             'group_encoded':total_encoded,'representatives':representatives,
             'target_group':by_core[atlas],'empty_group':by_core[0],
             'coefficient_target':expected,'status':'untrusted Lean witness; exact Python arithmetic passed'}
    if suffix:
        from generate_compact_s4_psd import row_tag
        row_tag(c)  # Validate the suffix before constructing paths.
        payload.update(lean_namespace_suffix=suffix, affine_step=affine_step,
                       coefficient_kind='affine_degree_five')
    suffix_label='_'+suffix.lower() if suffix else ''
    output=Path(f'experiments/atlas{atlas}_compact{suffix_label}_group_witness.json')
    output.write_text(json.dumps(payload,separators=(',',':'))+'\n',encoding='utf-8')
    print(output,'bytes',output.stat().st_size,'right bound',right_bound,
          'target group',by_core[atlas],'empty group',by_core[0])


if __name__=='__main__':
    main()
