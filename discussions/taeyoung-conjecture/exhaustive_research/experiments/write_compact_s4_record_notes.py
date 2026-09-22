"""Write explanatory notes and advance the plan for an already accepted row."""

import argparse
import hashlib
import json
from pathlib import Path
import re

import sympy as sp

from record_compact_s4_completed import duration


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--atlas',type=int,required=True)
    parser.add_argument('--next',type=int,required=True)
    args=parser.parse_args()
    atlas=args.atlas
    root=Path(__file__).resolve().parents[1]
    run=root/f'lean/verification_runs/atlas{atlas}'
    accepted=json.loads((run/'completed_row.json').read_text())
    assert accepted['atlas']==atlas and accepted['status']=='verified'
    example=root/f'lean/Taeyoung/Examples/Graph{atlas}.lean'
    assert hashlib.sha256(example.read_bytes()).hexdigest()==accepted['example_source_sha256']
    fresh=(run/accepted['fresh_report']).parent
    manifest=json.loads((fresh/'manifest.json').read_text())
    assert json.loads((fresh/'summary.json').read_text())['success']
    assert set(accepted['axioms'])=={'propext','Classical.choice','Quot.sound'}
    for module,digest in manifest['source_sha256'].items():
        source=root/'lean'/Path(*module.split('.')).with_suffix('.lean')
        assert hashlib.sha256(source.read_bytes()).hexdigest()==digest,module
    c=json.loads((root/f'experiments/atlas{atlas}_compact_face_candidate.json').read_text())
    discovery=json.loads((run/'face_discovery_1.json').read_text())
    audit=json.loads((run/'independent_audit_1.json').read_text())
    assert discovery['exit_code']==audit['exit_code']==0
    t,p=sp.symbols('t p')
    lo,hi=map(sp.Rational,c['interval'])
    target=sp.factor(sp.sympify(c['phi']).subs(t,(p-lo)/(hi-lo)))
    interval=f"[{c['interval'][0]},{c['interval'][1]}]"
    orders=', '.join(str(len(g)) for g in c['gram_scaled'])
    peak=accepted['peak_private_bytes']/2**30
    elapsed=accepted['fresh_elapsed_seconds']
    combined=accepted['combined_seconds']
    size=accepted['row_source_bytes']
    files=accepted['row_file_count']
    date=accepted['date']
    shared=accepted['shared_project_modules']
    extra_reports=accepted.get('additional_shared_component_reports',[])
    extra=''
    for ref in extra_reports:
        report_path=(run/ref).resolve()
        report_path.relative_to(root)
        report=json.loads(report_path.read_text())
        assert report['success']
        seconds=sum(item['elapsed_seconds'] for item in report['results'])
        extra+=(f'- `{report_path.relative_to(root).as_posix()}`: '
                f'{seconds:.3f} seconds summed compilation, '
                f'{report["peak_private_bytes"]/2**30:.2f} GiB peak private memory.\n')
    summary=(f'The fresh {files}-file build passed in **{duration(elapsed)}** '
             f'({elapsed:.3f} seconds), with **{peak:.2f} GiB** peak process-tree '
             'private memory. The installed-source recheck passed too, bringing '
             f'combined verification to **{duration(combined)}** ({combined:.3f} seconds).')
    note=f'''# Compact Atlas{atlas} certificate

Status ({date}): **verified**. {summary}
The catalogue example and classification are updated. The final theorem
reports only `propext`, `Classical.choice`, and `Quot.sound`.

The full required interval is `{interval}`. The catalogue target is
`{target}`. With `p={lo}+({hi-lo})*s`, the checked identity is

```
sum of positive flag-density blocks
  = {c['gram_denominator']} * (t(H{atlas},W) - ({c['phi'].replace('t','s')})).
```

Five blocks use constant and linear flag combinations; five have the
nonnegative multiplier `s*(1-s)`. The reduced integer matrix orders are
{orders}. Integer triangular congruences prove positivity, bounded positional
encodings prove the matrix products, and the shared sparse flag map supplies
the graphon interpretation. The method is explained in more detail in
[the Atlas118 note](atlas118_compact_certificate.md).

The external audit passed all 407 coefficient equations and ten positivity
witnesses. Lean independently checks the integer witnesses, graph
identifications, coloring counts, target polynomial, and full catalogue
conversion. Numerical discovery is not a premise of the theorem.

The row has {files} source files, totaling {size:,} bytes. It uses {shared}
prebuilt shared project modules. Source closure, hashes, measured build
costs, and the axiom audit are retained under
`lean/verification_runs/atlas{atlas}/`. See
[the verification record](../lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md).
'''
    progress=f'''# Atlas{atlas} compact verification record

Atlas{atlas} is **verified** ({date}). {summary}
All source hashes remained unchanged throughout the fresh build. The final
catalogue theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
The example and classification are updated; Atlas{args.next} is next.

The full interval is `{interval}`. The row contains {files} files and
{size:,} source bytes. Every row file was rebuilt sequentially against
{shared} prebuilt common project modules. Lean used one thread and a 12 GiB
heap cap; the process-tree watchdog enforced 16 GiB and a 3,600-second
whole-row deadline. Row artifacts were absent at the start of the fresh run.

The integer certificate has common denominator `{c['gram_denominator']}`.
Discovery took {discovery['elapsed_seconds']:.3f} seconds; the independent
exact audit took {audit['elapsed_seconds']:.3f} seconds. Those external
discovery checks are separate from Lean acceptance.

Shared costs are accounted for separately. The 57 reusable compact modules
recorded in `verification_runs/atlas118/shared_components.json` took 48m05s
summed across successful component runs, with a 12.32 GiB peak. This is not
a fresh rebuild measurement of the complete common closure. Mathlib and
the older shared classification infrastructure are prebuilt.

Additional shared component reports:

{extra if extra else 'No additional shared compilation was needed.\n'}
Accepted row records:

- `verification_runs/atlas{atlas}/{fresh.name}/summary.json` and `manifest.json`.
- `verification_runs/atlas{atlas}/installed_example_1.json` and its axiom log.
- `verification_runs/atlas{atlas}/completed_row.json`.

See [the certificate explanation](../../notes/atlas{atlas}_compact_certificate.md).
'''
    plan_path=root/'LEAN_REMAINING_VERIFICATION_PLAN.md'
    plan=plan_path.read_text(encoding='utf-8')
    rows=re.findall(r'^\| (\d+) \| (\d+) \| (.*?) \|$',plan,re.M)
    positions=[i for i,(_,n,_) in enumerate(rows) if int(n)==atlas]
    assert len(positions)==1
    position=positions[0]
    assert int(rows[position+1][1])==args.next
    assert '**Completed.**' not in rows[position][2]
    for _,n,description in rows[:position]:
        assert '**Completed.**' in description,n
    plan=re.sub(fr'Atlas{atlas}\s+is now the active row\.\s*','',plan)
    paragraph=(f'Atlas{atlas} completed on {date}. Its fresh {files}-file full '
               f'`{interval}` catalogue proof passed in {duration(elapsed)} at '
               f'{peak:.2f} GiB peak private memory; the installed recheck brings '
               f'combined verification to {duration(combined)}. The final theorem '
               'has only the standard axioms, and its example and classification '
               f'are updated. Atlas{args.next} is now the active row. See '
               f'[the verification record](lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md).\n\n')
    marker='| Priority | Atlas | Proposed route and reason |'
    assert plan.count(marker)==1
    plan=plan.replace(marker,paragraph+marker)
    replacement=(f'| {rows[position][0]} | {atlas} | **Completed.** Full `{interval}` '
                 f'compact catalogue proof; fresh {files}-file build in '
                 f'{duration(elapsed)} at {peak:.2f} GiB. |')
    plan,n=re.subn(fr'^\| {rows[position][0]} \| {atlas} \| .*? \|$',replacement,plan,flags=re.M)
    assert n==1
    (root/f'notes/atlas{atlas}_compact_certificate.md').write_text(note,encoding='utf-8')
    (root/f'lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md').write_text(progress,encoding='utf-8')
    plan_path.write_text(plan,encoding='utf-8')
    print(f'Recorded Atlas{atlas} notes and plan; Atlas{args.next} is now active.')


if __name__=='__main__':
    main()
