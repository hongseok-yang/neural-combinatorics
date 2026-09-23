"""Document a completed row with namespaced S4 pieces, after acceptance only."""

import argparse
import hashlib
import json
from pathlib import Path
import re

from record_compact_s4_completed import duration

NUMBERS = {1:'one',2:'two',3:'three',4:'four',5:'five',6:'six',7:'seven',8:'eight',
           9:'nine',10:'ten',20:'twenty',30:'thirty',40:'forty',50:'fifty'}


def spell(n):
    return NUMBERS.get(n,str(n))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--atlas', type=int, required=True)
    parser.add_argument('--next', type=int,
                        help='The row to work on next; omit when this is the last believed row.')
    args = parser.parse_args()
    following = f'Atlas{args.next} is next.' if args.next else 'no believed row remains.'
    active = f'Atlas{args.next} is now the active row. ' if args.next else ''
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
    prefix = f'Taeyoung.Methods.RootedSOS.CompactS4.Atlas{atlas}.'
    suffixes, elementary = [], []
    for module in manifest['modules']:
        rest = module[len(prefix):]
        if rest.endswith('.Certificate'):
            suffixes.append(rest[:-len('.Certificate')])
        elif '.' not in rest and rest not in ('Coloring','Certificate'):
            elementary.append(rest)
    assert suffixes and len(elementary) <= 1, (suffixes,elementary)
    pieces = []
    for suffix in suffixes:
        c = json.loads((root/f'experiments/atlas{atlas}_compact_{suffix.lower()}_namespaced.json').read_text())
        w = json.loads((root/f'experiments/atlas{atlas}_compact_{suffix.lower()}_group_witness.json').read_text())
        count = sum(f'.{suffix}.' in m for m in manifest['modules'])
        pieces.append((suffix,c,w,count))
    certificate = (root/'lean'/Path(*(prefix+'Certificate').split('.'))
                   ).with_suffix('.lean').read_text(encoding='utf-8')
    admissible = re.search(r'hp : \((\d+) : Real\)/(\d+) ≤ cliqueDensity', certificate)
    admissible = f'{admissible[1]}/{admissible[2]}'
    bounds = len(pieces)+len(elementary)
    low_clause = f', above the elementary range proved in `{elementary[0]}.lean`' if elementary else ''
    peak = a['peak_private_bytes']/2**30
    summary = (f'The fresh **{a["row_file_count"]}-file** build passed in '
               f'**{duration(a["fresh_elapsed_seconds"])}** ({a["fresh_elapsed_seconds"]:.3f} seconds), '
               f'at **{peak:.2f} GiB** peak process-tree private memory. The installed-source '
               f'recheck brings combined verification to **{duration(a["combined_seconds"])}** '
               f'({a["combined_seconds"]:.3f} seconds).')
    piece_details = []
    if elementary:
        piece_details.append(
            f'- **{elementary[0]}** interval `[{admissible},{pieces[0][1]["interval"][0]}]`: one '
            f'hand-written file; the catalogue target is nonpositive there, so the bound is the '
            f'nonnegativity of the homomorphism density. No certificate data.')
    for suffix,c,w,count in pieces:
        orders = ', '.join(str(len(g)) for g in c['gram_scaled'])
        piece_details.append(
            f'- **{suffix}** interval `[{",".join(c["interval"])}]`: {count} files; '
            f'`p=({w["affine_offset"]}+{w["affine_step"]}*s)/{w["affine_denominator"]}`, '
            f'common denominator `{c["gram_denominator"]}` and interpolation scale `{w["scale"]}`. '
            f'The ten integer positive factors have orders `{orders}`.')
    detail = '\n'.join(piece_details)
    records = [f'`{s.lower()}_{kind}_1`'
               for kind in ('face_discovery','independent_audit') for s in suffixes]
    audits = ', '.join(records[:-1])+f', and {records[-1]}' if len(records) > 1 else records[0]
    note = f'''# Compact Atlas{atlas} certificate

Status ({a['date']}): **verified**. {summary}
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

The full admissible interval is covered by {spell(len(pieces))} exact four-root SOS certificates{low_clause}:

{detail}

Each of the {spell(sum(len(c['gram_scaled']) for _,c,_,_ in pieces))} Gram blocks retains its integer data, triangular-congruence
positivity proof, and exact basis-expansion proof in a single Lean module.
Ten density interpretation modules per piece are included verbatim in their
five corresponding block sums. Every proof is still checked. Sparse integer
contractions and affine coefficient identities assemble the graphon inequality;
the {spell(bounds)} interval bounds then prove the full catalogue `SatisfiesLowerBound` theorem.
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
{following}

The fresh run includes {'both' if bounds == 2 else f'all {spell(bounds)}'} interval bounds, chromatic counts, graph
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

Separate discovery and arithmetic audit records are {audits}.
Development runs and any unsuccessful fresh
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
    paragraph = (f'Atlas{atlas} completed on {a["date"]}. Its {spell(bounds)} interval bounds '
                 f'and the full catalogue proof passed in a fresh {a["row_file_count"]}-file '
                 f'build: {duration(a["fresh_elapsed_seconds"])} at {peak:.2f} GiB. '
                 f'The installed recheck brings combined verification to {duration(a["combined_seconds"])}. '
                 'The theorem has only the standard axioms; its example and classification '
                 f'are updated. {active}See '
                 f'[the verification record](lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md).\n\n')
    assert f'Atlas{atlas} completed on' not in plan
    plan = plan.replace(marker, paragraph+marker)
    plan,n = re.subn(fr'^(\| \d+ \| {atlas} \| ).*? \|$',
        lambda m: m[1]+f'**Completed.** {spell(bounds).capitalize()} interval bounds, full '
                  f'catalogue proof; fresh '
                  f'{a["row_file_count"]}-file build in {duration(a["fresh_elapsed_seconds"])} '
                  f'at {peak:.2f} GiB. |', plan, flags=re.M)
    assert n == 1
    (root/f'notes/atlas{atlas}_compact_certificate.md').write_text(note, encoding='utf-8')
    (root/f'lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md').write_text(progress, encoding='utf-8')
    plan_path.write_text(plan, encoding='utf-8')
    print(f'Recorded completed Atlas{atlas}; {following}')


if __name__ == '__main__':
    main()
