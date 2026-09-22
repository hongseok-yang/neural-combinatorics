"""Generate single-interval coloring and catalogue assembly from exact data.

Atlas118 supplies the accepted proof templates. The resulting modules import
only their own row data and shared machinery; all new counts and identities
are checked again in Lean. The live example is left for the acceptance driver.
"""

import argparse
import ast
import itertools
import json
from pathlib import Path
import re

import sympy as sp


def lean_polynomial(poly,var):
    assert poly.degree()<=5
    values=[poly.nth(j) for j in range(6)]
    assert all(v.q==1 for v in values)
    return ' + '.join(f'({int(v)})*{var}^{j}' for j,v in enumerate(values))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate')
    parser.add_argument('--upper-piece', action='store_true',
                        help='Emit only an upper-interval bound; never stage a complete example.')
    parser.add_argument('--coloring-only', action='store_true',
                        help='Emit the root coloring module for separately assembled interval pieces.')
    args=parser.parse_args()
    c=json.loads(Path(args.certificate).read_text(encoding='utf-8'))
    atlas=int(c['atlas'])
    assert atlas not in [118,122,124], 'Preserve the accepted template-family sources.'
    assert c['interval'] in [['1/2','1'],['2/3','1'],['3/4','1']]
    lower=sp.Rational(c['interval'][0])
    offset,divisor=int(lower.p),int(lower.q)
    scale=divisor**4
    t,p=sp.symbols('t p')
    phi=sp.sympify(c['phi'])
    if any(sp.Poly(sp.expand(scale*phi),t).nth(j).q != 1 for j in range(6)):
        scale=divisor**5
    numerator=lean_polynomial(sp.Poly(sp.expand(scale*phi),t),'s')
    target=lean_polynomial(sp.Poly(sp.expand(phi.subs(t,divisor*p-offset)),p),'p')
    base=Path('lean/Taeyoung/Methods/RootedSOS/CompactS4')
    root=base/f'Atlas{atlas}'
    root.mkdir(parents=True,exist_ok=True)
    example=Path(f'lean/Taeyoung/Examples/Graph{atlas}.lean').read_text(encoding='utf-8')
    edge_text=re.search(r'graphFromEdges 6 (\[[^\n]+\])',example).group(1)
    edges=ast.literal_eval(edge_text)
    counts=[sum(len(set(y))==j and all(y[a]!=y[b] for a,b in edges)
                for y in itertools.product(range(j),repeat=6)) for j in range(7)]
    chromatic=next(j for j,n in enumerate(counts) if n)
    admissible_lower=1-sp.Rational(1,chromatic-1)
    if args.upper_piece or args.coloring_only:
        assert admissible_lower < lower, 'An upper piece must leave a lower interval to prove.'
    else:
        assert lower==admissible_lower, 'This generator requires full admissible coverage.'
    source=(base/'Atlas118/Coloring.lean').read_text(encoding='utf-8')
    source=source.replace('118',str(atlas)).replace('₁₁₈',str(atlas))
    source=re.sub(r'/-- Atlas\d+: the house with a leaf attached at a vertex of degree three\. -/',
                  f'/-- Atlas{atlas}, with exactly the catalogue edge list. -/',source)
    source=re.sub(r'graphFromEdges 6 \[[^\n]+\]',f'graphFromEdges 6 {edge_text}',source)
    source=re.sub(r'/\-! ### Chromatic data.*?-/',
                  '/-! ### Chromatic data, checked by surjective coloring counts. -/',source,flags=re.S)
    source=source.replace('Check the seven edges directly','Check the catalogue edges directly')
    predicate=' ∧ '.join(f'y {a} ≠ y {b}' for a,b in edges)
    source,n=re.subn(r'(private def fastProper\d+.*? : Prop :=\n).*?(\n\nprivate instance)',
                    lambda m:m[1]+'  '+predicate+m[2],source,flags=re.S)
    assert n==1
    constructor='    exact ⟨'+','.join(f'h {a} {b} (by decide)' for a,b in edges)+'⟩'
    source,n=re.subn(r'    exact ⟨h .*?⟩',lambda _:constructor,source,count=1,flags=re.S)
    assert n==1
    for j,count in enumerate(counts):
        source,n=re.subn(fr'(theorem s{atlas}_{j} : surjCount graph{atlas} {j} = )\d+',
                        lambda m:m[1]+str(count),source)
        assert n==1
    count_expression=' + '.join(f'{count} * k.choose {j}' for j,count in enumerate(counts) if count)
    source,n=re.subn(fr'(theorem count{atlas}.*?properAssignmentCount graph{atlas} k\s*=).*?(:= by)',
                    lambda m:m[1]+' '+count_expression+' '+m[2],source,flags=re.S)
    assert n==1
    source=source.replace(f'IsChromaticNumber graph{atlas} 3 where',
                          f'IsChromaticNumber graph{atlas} {chromatic} where')
    source=source.replace('have hreq : r = 3 :=',f'have hreq : r = {chromatic} :=')
    source=source.replace('(1 : ℝ) / 2',f'({int(admissible_lower.p)} : ℝ) / {int(admissible_lower.q)}')
    source=re.sub(r'/-- `Φ_.*?-/', '/-- The exact catalogue target polynomial. -/',source)
    source,n=re.subn(fr'(noncomputable def target{atlas} \(p : ℝ\) : ℝ :=\n).*?(\n\nset_option)',
                    lambda m:m[1]+'  '+target+m[2],source,flags=re.S)
    assert n==1
    source=source.replace(f'target{atlas} ((1+s)/2) = s*(s+1)^2*(3*s^2+1)/16',
                          f'target{atlas} (({offset}+s)/{divisor}) = ({numerator})/{scale}')
    (root/'Coloring.lean').write_text(source,encoding='utf-8')
    if args.coloring_only:
        print(f'Prepared Atlas{atlas} coloring, chromatic number {chromatic}, counts {counts}.')
        return
    source=(base/'Atlas118/Certificate.lean').read_text(encoding='utf-8')
    source=source.replace('118',str(atlas))
    source=source.replace('(1 : Real)/2',f'({offset} : Real)/{divisor}')
    source=source.replace('let s := 2*cliqueDensity 2 W-1',
                          f'let s := {divisor}*cliqueDensity 2 W-{offset}')
    source=source.replace('(1+s)/2',f'({offset}+s)/{divisor}')
    source=source.replace(f"16*target{atlas} (cliqueDensity 2 W) = s+2*s^2+4*s^3+6*s^4+3*s^5",
                          f'{scale}*target{atlas} (cliqueDensity 2 W) = {numerator}')
    if args.upper_piece:
        source,n=re.subn(fr'theorem satisfiesLowerBound_{atlas}.*?(?=end Taeyoung)', '', source, flags=re.S)
        assert n==1
        source=source.replace('graphon_bound','upper_graphon_bound')
        (root/'UpperCertificate.lean').write_text(source,encoding='utf-8')
        print(f'Prepared Atlas{atlas} upper piece only, chromatic number {chromatic}, counts {counts}.')
        return
    (root/'Certificate.lean').write_text(source,encoding='utf-8')
    example=example.replace('import Taeyoung.Foundation',
        f'import Taeyoung.Methods.RootedSOS.CompactS4.Atlas{atlas}.Certificate')
    example=example.replace('formalization := .believed','formalization := .verified')
    example,n=re.subn(r'/-- Accepted mathematical result:.*?theorem status : SatisfiesLowerBound graph := by\n  sorry',
        f'/-- Complete compact integer SOS proof, including the graphon interpretation. -/\n'
        f'theorem status : SatisfiesLowerBound graph :=\n'
        f'  Taeyoung.Methods.RootedSOS.CompactS4.Atlas{atlas}.satisfiesLowerBound_{atlas}',
        example,flags=re.S)
    assert n==1
    example+=f'\n#print axioms Taeyoung.Examples.Graph{atlas}.status\n'
    prepared=Path(f'lean/verification_runs/atlas{atlas}/prepared')
    prepared.mkdir(parents=True,exist_ok=True)
    (prepared/f'Graph{atlas}.lean').write_text(example,encoding='utf-8')
    print(f'Prepared Atlas{atlas} assembly, chromatic number {chromatic}, counts {counts}.')


if __name__=='__main__':
    main()
