"""Document a completed row with namespaced S4 pieces, after acceptance only."""

import argparse
import hashlib
import json
from pathlib import Path
import re

from record_compact_s4_completed import duration


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--atlas', type=int, required=True)
    parser.add_argument('--next', type=int, required=True)
    args = parser.parse_args()
    atlas = args.atlas
    root = Path(__file__).resolve().parents[1]
    run = root/f'lean/verification_runs/atlas{atlas}'
    a = json.loads((run/'completed_row.json').read_text())
    assert a['atlas'] == atlas and a['status'] == 'verified'
    assert a['row_file_count'] <= 100 and a['combined_seconds'] <= 3600
    assert a['peak_private_bytes'] <= 16*2**30
    example = root/f'lean/Taeyoung/Examples/Graph{atlas}.lean'
    assert hashlib.sha256(example.read_bytes()).hexdigest() == a['example_source_sha256']
    fresh = (run/a['fresh_report']).parent
    manifest = json.loads((fresh/'manifest.json').read_text())
    assert json.loads((fresh/'summary.json').read_text())['success']
    for module, digest in manifest['source_sha256'].items():
        source = root/'lean'/Path(*module.split('.')).with_suffix('.lean')
        assert hashlib.sha256(source.read_bytes()).hexdigest() == digest, module
    pieces = []
    for suffix in ('Lower', 'Upper'):
        c = json.loads((root/f'experiments/atlas{atlas}_compact_{suffix.lower()}_namespaced.json').read_text())
        w = json.loads((root/f'experiments/atlas{atlas}_compact_{suffix.lower()}_group_witness.json').read_text())
        count = sum(f'.{suffix}.' in m for m in manifest['modules'])
        pieces.append((suffix,c,w,count))
    peak = a['peak_private_bytes']/2**30
    summary = (f'The fresh **{a["row_file_count"]}-file** build passed in '
               f'**{duration(a["fresh_elapsed_seconds"])}** ({a["fresh_elapsed_seconds"]:.3f} seconds), '
               f'at **{peak:.2f} GiB** peak process-tree private memory. The installed-source '
               f'recheck brings combined verification to **{duration(a["combined_seconds"])}** '
               f'({a["combined_seconds"]:.3f} seconds).')
    piece_details = []
    for suffix,c,w,count in pieces:
        orders = ', '.join(str(len(g)) for g in c['gram_scaled'])
        piece_details.append(
            f'- **{suffix}** interval `[{",".join(c["interval"])}]`: {count} files; '
            f'`p=({w["affine_offset"]}+{w["affine_step"]}*s)/{w["affine_denominator"]}`, '
            f'common denominator `{c["gram_denominator"]}` and interpolation scale `{w["scale"]}`. '
            f'The ten integer positive factors have orders `{orders}`.')
    detail = '\n'.join(piece_details)
    note = f'''# Compact Atlas{atlas} certificate

Status ({a['date']}): **verified**. {summary}
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

The full admissible interval is covered by two exact four-root SOS certificates:

{detail}

Each of the twenty Gram blocks retains its integer data, triangular-congruence
positivity proof, and exact basis-expansion proof in a single Lean module.
Ten density interpretation modules per piece are included verbatim in their
five corresponding block sums. Every proof is still checked. Sparse integer
contractions and affine coefficient identities assemble the graphon inequality;
the two interval bounds then prove the full catalogue `SatisfiesLowerBound` theorem.
Numerical certificate discovery and independent Python audits are not premises
of the Lean theorem.

The row has {a['row_source_bytes']:,} source bytes. All interval data, coloring,
assembly, and the catalogue example are counted in the fresh run. See
[the verification record](../lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md).
'''
    progress = f'''# Atlas{atlas} compact verification record

Atlas{atlas} is **verified** ({a['date']}). {summary}
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its catalogue example and classification are updated;
Atlas{args.next} is next.

The fresh run includes both interval pieces, chromatic counts, graph
identification, complete `SatisfiesLowerBound` theorem, and catalogue example.
Row artifacts were absent at the start. Compilation was sequential with
`LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for all {a['row_file_count']} row files.

{detail}

The row uses {a['shared_project_modules']} prebuilt shared project modules.
The reusable affine interval coefficient lemma is recorded in
`verification_runs/atlas147/shared_affine_1/summary.json` (8.875 seconds,
4.83 GiB peak private memory). Earlier compact common component costs are in
`verification_runs/atlas118/shared_components.json`: 57 modules, 2,884.982
seconds summed compilation, 12.32 GiB peak. These are successful, source-matching
component measurements, not fresh builds of the complete shared closure.
Older project dependencies and Mathlib are prebuilt. No row-specific
certificate data have been moved into the shared accounting.

Accepted records:

- `verification_runs/atlas{atlas}/{fresh.name}/manifest.json` and `summary.json`.
- `verification_runs/atlas{atlas}/{fresh.name}/catalogue_compile.log`.
- `verification_runs/atlas{atlas}/installed_example_1.json` and `.log`.
- `verification_runs/atlas{atlas}/completed_row.json`.

Separate discovery and arithmetic audit records are `lower_face_discovery_1`,
`upper_face_discovery_1`, `lower_independent_audit_1`, and
`upper_independent_audit_1`. Development runs and any unsuccessful fresh
attempts remain separate from the accepted measurement.

See [the certificate explanation](../../notes/atlas{atlas}_compact_certificate.md).
'''
    if atlas == 147:
        progress += '''
The first fresh attempt (`fresh_row_1`) finished both complete interval bounds
but failed the final assembly at 2,626.984 seconds: the upper endpoint `1/1`
needed explicit normalization to `1`. The one-line `div_one` repair passed
in `assembly_repair_1`, including a staged catalogue audit with only the
standard axioms. The accepted measurement rebuilt every row module again
from absent artifacts with the repaired source; no result from the failed
attempt substitutes for an accepted compilation.
'''
    plan_path = root/'LEAN_REMAINING_VERIFICATION_PLAN.md'
    plan = plan_path.read_text(encoding='utf-8')
    plan = re.sub(fr'Atlas{atlas} is now the active row\.\s*', '', plan)
    marker = '| Priority | Atlas | Proposed route and reason |'
    assert plan.count(marker) == 1
    paragraph = (f'Atlas{atlas} completed on {a["date"]}. Both four-root interval pieces '
                 f'and the full catalogue proof passed in a fresh {a["row_file_count"]}-file '
                 f'build: {duration(a["fresh_elapsed_seconds"])} at {peak:.2f} GiB. '
                 f'The installed recheck brings combined verification to {duration(a["combined_seconds"])}. '
                 'The theorem has only the standard axioms; its example and classification '
                 f'are updated. Atlas{args.next} is now the active row. See '
                 f'[the verification record](lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md).\n\n')
    assert f'Atlas{atlas} completed on' not in plan
    plan = plan.replace(marker, paragraph+marker)
    plan,n = re.subn(fr'^(\| \d+ \| {atlas} \| ).*? \|$',
        lambda m: m[1]+f'**Completed.** Two four-root pieces, full catalogue proof; fresh '
                  f'{a["row_file_count"]}-file build in {duration(a["fresh_elapsed_seconds"])} '
                  f'at {peak:.2f} GiB. |', plan, flags=re.M)
    assert n == 1
    (root/f'notes/atlas{atlas}_compact_certificate.md').write_text(note, encoding='utf-8')
    (root/f'lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md').write_text(progress, encoding='utf-8')
    plan_path.write_text(plan, encoding='utf-8')
    print(f'Recorded completed Atlas{atlas}; Atlas{args.next} is next.')


if __name__ == '__main__':
    main()
