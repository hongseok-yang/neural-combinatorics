"""Record Atlas203's two-interval proof after complete resource acceptance."""

import hashlib
import json
from pathlib import Path
import re

from record_compact_s4_completed import duration


def main():
    root = Path(__file__).resolve().parents[1]
    run = root/'lean/verification_runs/atlas203'
    a = json.loads((run/'completed_row.json').read_text())
    assert a['atlas'] == 203 and a['status'] == 'verified'
    assert a['row_file_count'] == 100 and a['combined_seconds'] <= 3600
    assert a['peak_private_bytes'] <= 16*2**30
    example = root/'lean/Taeyoung/Examples/Graph203.lean'
    assert hashlib.sha256(example.read_bytes()).hexdigest() == a['example_source_sha256']
    fresh = (run/a['fresh_report']).parent
    manifest = json.loads((fresh/'manifest.json').read_text())
    assert json.loads((fresh/'summary.json').read_text())['success']
    for module, digest in manifest['source_sha256'].items():
        source = root/'lean'/Path(*module.split('.')).with_suffix('.lean')
        assert hashlib.sha256(source.read_bytes()).hexdigest() == digest, module
    shared = json.loads((run/'shared_intervals_1/summary.json').read_text())
    assert shared['success']
    seconds = sum(r['elapsed_seconds'] for r in shared['results'])
    peak = a['peak_private_bytes']/2**30
    summary = (f'The fresh **100-file** build passed in **{duration(a["fresh_elapsed_seconds"])}** '
               f'({a["fresh_elapsed_seconds"]:.3f} seconds), at **{peak:.2f} GiB** peak process-tree '
               f'private memory. The installed-source recheck brings combined verification to '
               f'**{duration(a["combined_seconds"])}** ({a["combined_seconds"]:.3f} seconds).')
    note = f'''# Compact Atlas203 certificate

Status ({a['date']}): **verified**. {summary}
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

Atlas203 is `K6` with edges `04`, `25`, and `35` removed. Its target is
`p*(2*p-1)*(3*p-2)*(10*p^2-14*p+5)`. The full admissible interval `[2/3,1]`
is covered by an induced certificate on `[2/3,3/4]` and a four-root
certificate on `[3/4,1]`.

The lower proof uses the [Atlas130 induced interpretation](atlas130_compact_certificate.md).
With `s=12*p-8` and `D=3181190920704000000000000`, the exact identity expresses
`D*(t(H203,W)-target(p))` as 14 nonnegative induced flag Gram expressions
plus nonnegative Bernstein residuals times induced densities. Its 28 reduced
positive integer Gram factors have order at most 38. All 936 coefficient
equations and their nonnegative residuals are checked in Lean. Eleven
fixed-density multipliers cancel by the disjoint-union density identity.

The upper proof has ten positive factors and common denominator
`2592000000000000`. The substitution `p=(3+s)/4` uses scale 256. Both pieces
use bounded integer encodings, exact matrix products, and generic positivity
lemmas; numerical discovery and the Python audits are not premises of the
Lean theorem.

The row uses 78 upper files, 20 lower files, one complete assembly, and one
catalogue example: 100 files and {a['row_source_bytes']:,} source bytes.
Both intervals and every row-specific data module are included in the fresh
measurement. See [the verification record](../lean/docs/ATLAS203_VERIFICATION_PROGRESS.md).
'''
    progress = f'''# Atlas203 compact verification record

Atlas203 is **verified** ({a['date']}). {summary}
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its live catalogue example and classification are updated;
Atlas147 is next.

The fresh run includes both `[2/3,3/4]` and `[3/4,1]`, the chromatic target,
graph identification, complete `SatisfiesLowerBound` theorem, and catalogue
example. Row artifacts were absent at the start. Compilation was sequential,
with `LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for all 100 row files.

The row has {a['row_source_bytes']:,} source bytes and uses
{a['shared_project_modules']} prebuilt shared project modules. The two new
reusable interval lemmas took {seconds:.3f} seconds summed compilation, at
{shared['peak_private_bytes']/2**30:.2f} GiB peak private memory; see
`verification_runs/atlas203/shared_intervals_1/summary.json`.

Earlier common component costs are recorded in
`verification_runs/atlas130/induced_shared_components.json` (138 modules,
2,438.453 seconds summed compilation, 11.70 GiB peak) and
`verification_runs/atlas118/shared_components.json` (57 modules,
2,884.982 seconds, 12.32 GiB peak). These are successful, source-matching
component measurements, not fresh builds of the complete shared closure.
Older common modules and Mathlib are prebuilt. No Atlas203-specific certificate
data are moved into that shared accounting.

Accepted records:

- `verification_runs/atlas203/{fresh.name}/manifest.json` and `summary.json`.
- `verification_runs/atlas203/{fresh.name}/catalogue_compile.log`.
- `verification_runs/atlas203/installed_example_1.json` and `.log`.
- `verification_runs/atlas203/completed_row.json`.

The separate discovery/audit reports are `induced_independent_audit_1`,
`lower_compact_export_1`, `upper_face_discovery_2`, and
`upper_independent_audit_1` under `verification_runs/atlas203/`.
The first upper discovery attempt only supplied an incorrect input filename.
Development component runs are retained separately from acceptance.

See [the certificate explanation](../../notes/atlas203_compact_certificate.md).
'''
    plan_path = root/'LEAN_REMAINING_VERIFICATION_PLAN.md'
    plan = plan_path.read_text(encoding='utf-8')
    for n in (126, 118, 122, 124, 181, 157, 169, 194, 185, 199, 130):
        assert re.search(fr'^\| \d+ \| {n} \| \*\*Completed\.\*\*', plan, re.M)
    plan = re.sub(r'Atlas203 is now the active row\.\s*', '', plan)
    plan, count = re.subn(r'Atlas203\x27s two interval pieces are generated.*?(?=\| Priority)', '', plan, flags=re.S)
    assert count == 1
    paragraph = (f'Atlas203 completed on {a["date"]}. Both interval pieces and its full catalogue '
                 f'proof passed in a fresh 100-file build: {duration(a["fresh_elapsed_seconds"])} '
                 f'at {peak:.2f} GiB. The installed recheck brings combined verification to '
                 f'{duration(a["combined_seconds"])}. The theorem has only the standard axioms; '
                 'its example and classification are updated. Atlas147 is now the active row. See '
                 '[the verification record](lean/docs/ATLAS203_VERIFICATION_PROGRESS.md).\n\n')
    marker = '| Priority | Atlas | Proposed route and reason |'
    assert plan.count(marker) == 1
    plan = plan.replace(marker, paragraph+marker)
    plan, count = re.subn(r'^\| 12 \| 203 \| .*? \|$',
                         f'| 12 | 203 | **Completed.** Induced lower interval and four-root upper interval; fresh full 100-file catalogue proof in {duration(a["fresh_elapsed_seconds"])} at {peak:.2f} GiB. |',
                         plan, flags=re.M)
    assert count == 1
    tex_path = root/'notes/atlas130_atlas203_complete_bounds.tex'
    tex = tex_path.read_text(encoding='utf-8')
    old = 'These new results are not yet formalized in Lean.'
    assert old in tex
    tex = tex.replace(old, 'Both full bounds now have complete Lean proofs. Fresh sequential builds\n'
                      'use 100 row-specific files each and meet the one-hour, 16 GiB limits;\n'
                      'the shared infrastructure is measured separately. The complete theorem\n'
                      'axiom audits admit only the three standard Lean axioms. See\n'
                      '\\path{lean/docs/ATLAS130_VERIFICATION_PROGRESS.md} and\n'
                      '\\path{lean/docs/ATLAS203_VERIFICATION_PROGRESS.md} for the records.')
    (root/'notes/atlas203_compact_certificate.md').write_text(note, encoding='utf-8')
    (root/'lean/docs/ATLAS203_VERIFICATION_PROGRESS.md').write_text(progress, encoding='utf-8')
    plan_path.write_text(plan, encoding='utf-8')
    tex_path.write_text(tex, encoding='utf-8')
    print('Recorded completed Atlas203; Atlas147 is next.')


if __name__ == '__main__':
    main()
