"""Assemble namespaced S4 interval bounds and, optionally, one complete row.

Every piece imports all of its own arithmetic and graphon interpretation.
The complete theorem is staged for the fresh acceptance driver, never installed.
"""

import argparse
import json
from pathlib import Path
import re

import sympy as sp

from generate_compact_s4_psd import PREFIX, row_tag


def rational(value):
    q = sp.Rational(value)
    return f'({int(q.p)} : Real)/{int(q.q)}'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('witnesses', nargs='+')
    parser.add_argument('--complete', action='store_true')
    args = parser.parse_args()
    witnesses = [json.loads(Path(p).read_text(encoding='utf-8')) for p in args.witnesses]
    atlas = int(witnesses[0]['atlas'])
    assert all(w['atlas'] == atlas for w in witnesses)
    example_path = Path(f'lean/Taeyoung/Examples/Graph{atlas}.lean')
    example = example_path.read_text(encoding='utf-8')
    assert 'formalization := .verified' not in example, 'Preserve accepted row sources.'
    parent = f'{PREFIX}.CompactS4.Atlas{atlas}'
    root = Path('lean')/Path(*parent.split('.'))
    template = Path('lean/Taeyoung/Methods/RootedSOS/CompactS4/Atlas118/Certificate.lean').read_text(encoding='utf-8')
    for w in witnesses:
        assert w.get('lean_namespace_suffix')
        ns = PREFIX+'.'+row_tag(w)
        a, b = map(rational, w['interval'])
        A, B, Q = w['affine_offset'], w['affine_step'], w['affine_denominator']
        assert B > 0 and Q > 0
        assert sp.Rational(A,Q) == sp.Rational(w['interval'][0])
        assert sp.Rational(A+B,Q) == sp.Rational(w['interval'][1])
        scale = w['scale']
        polynomial = ' + '.join(f'({v})*s^{j}' for j,v in enumerate(w['target_coefficients']))
        source = template.split('theorem graphon_bound', 1)[0]
        source = source.replace(f'{PREFIX}.CompactS4.Atlas118', ns)
        source += f'''theorem graphon_bound (W : Graphon Ω μ)
    (hp : {a} ≤ cliqueDensity 2 W) (hp1 : cliqueDensity 2 W ≤ {b}) :
    target{atlas} (cliqueDensity 2 W) ≤ homDensity graph{atlas} W := by
  let s := ({Q}*cliqueDensity 2 W-{A})/{B}
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hp' : ({A}+{B}*s)/{Q} = cliqueDensity 2 W := by dsimp [s]; ring
  have h := group_nonneg W s hs hs1
  have he := group_identity s (fun g => homDensity (S4Classification.coreGraph6 g) W)
  have hc (g : Fin 143) : homDensity (S4Classification.coreGraph6 g) W =
      homDensity (S4Classification.coreGraph6 (representative g)) W :=
    density_eq_of_graph_eq _ _ W (core_eq g)
  simp_rw [← hc] at he
  rw [hp', density_eq_of_graph_eq _ _ W target_core,
    density_eq_of_graph_eq _ _ W empty_core, homDensity_bot_fin] at he
  have ht : {scale}*target{atlas} (cliqueDensity 2 W) = {polynomial} := by
    rw [← hp']
    unfold target{atlas}
    ring
  nlinarith

#print axioms graphon_bound
end {ns}
'''
        output = Path('lean')/Path(*ns.split('.'))/'Certificate.lean'
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(source, encoding='utf-8')
        print(output)
    if not args.complete:
        return
    # Check exact interval coverage and derive the catalogue's admissible endpoint.
    witnesses.sort(key=lambda w:sp.Rational(w['interval'][0]))
    coloring = (root/'Coloring.lean').read_text(encoding='utf-8')
    chromatic = int(re.search(fr'IsChromaticNumber graph{atlas} (\d+) where', coloring)[1])
    lower = 1-sp.Rational(1,chromatic-1)
    assert sp.Rational(witnesses[0]['interval'][0]) == lower
    assert sp.Rational(witnesses[-1]['interval'][1]) == 1
    assert all(sp.Rational(u['interval'][1]) == sp.Rational(v['interval'][0])
               for u,v in zip(witnesses,witnesses[1:]))
    imports = '\n'.join(f"import {PREFIX}.{row_tag(w)}.Certificate" for w in witnesses)
    source = imports+f'''
namespace {parent}
open MeasureTheory Taeyoung
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]

theorem graphon_bound (W : Graphon Ω μ) (hp : {rational(lower)} ≤ cliqueDensity 2 W) :
    target{atlas} (cliqueDensity 2 W) ≤ homDensity graph{atlas} W := by
'''
    lo = 'hp'
    for i,w in enumerate(witnesses[:-1]):
        source += f'''  by_cases h{i} : cliqueDensity 2 W ≤ {rational(w['interval'][1])}
  · exact {w['lean_namespace_suffix']}.graphon_bound W {lo} h{i}
  have hlow{i} : {rational(w['interval'][1])} ≤ cliqueDensity 2 W := le_of_lt (lt_of_not_ge h{i})
'''
        lo = f'hlow{i}'
    source += f'''  exact {witnesses[-1]['lean_namespace_suffix']}.graphon_bound W {lo}
    (by simpa only [div_one] using cliqueDensity_le_one 2 W)

theorem satisfiesLowerBound_{atlas} : SatisfiesLowerBound graph{atlas} :=
  satisfiesLowerBound_{atlas}_of_bound (fun W hp => graphon_bound W hp)
#print axioms satisfiesLowerBound_{atlas}
end {parent}
'''
    (root/'Certificate.lean').write_text(source, encoding='utf-8')
    example = example.replace('import Taeyoung.Foundation', f'import {parent}.Certificate')
    example = example.replace('formalization := .believed', 'formalization := .verified')
    example,n = re.subn(r'/-- Accepted mathematical result:.*?theorem status : SatisfiesLowerBound graph := by\n  sorry',
        f'/-- Complete compact SOS proof across all admissible intervals. -/\n'
        f'theorem status : SatisfiesLowerBound graph :=\n  {parent}.satisfiesLowerBound_{atlas}',
        example, flags=re.S)
    assert n == 1
    example += f'\n#print axioms Taeyoung.Examples.Graph{atlas}.status\n'
    prepared = Path(f'lean/verification_runs/atlas{atlas}/prepared')
    prepared.mkdir(parents=True, exist_ok=True)
    (prepared/f'Graph{atlas}.lean').write_text(example, encoding='utf-8')
    print(f'Staged complete Atlas{atlas} example with {len(witnesses)} interval pieces.')


if __name__ == '__main__':
    main()
