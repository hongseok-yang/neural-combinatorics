"""Publish Atlas130's two-interval record only after complete row acceptance."""

import hashlib
import json
from pathlib import Path
import re

from record_compact_s4_completed import duration


def main():
    root = Path(__file__).resolve().parents[1]
    run = root/'lean/verification_runs/atlas130'
    a = json.loads((run/'completed_row.json').read_text())
    assert a['atlas'] == 130 and a['status'] == 'verified'
    assert a['row_file_count'] == 100 and a['combined_seconds'] < 3600
    example = root/'lean/Taeyoung/Examples/Graph130.lean'
    assert hashlib.sha256(example.read_bytes()).hexdigest() == a['example_source_sha256']
    fresh = (run/a['fresh_report']).parent
    manifest = json.loads((fresh/'manifest.json').read_text())
    assert json.loads((fresh/'summary.json').read_text())['success']
    for module, digest in manifest['source_sha256'].items():
        source = root/'lean'/Path(*module.split('.')).with_suffix('.lean')
        assert hashlib.sha256(source.read_bytes()).hexdigest() == digest, module
    shared = json.loads((run/'induced_shared_components.json').read_text())
    peak = a['peak_private_bytes']/2**30
    summary = (f'The fresh **100-file** build passed in **{duration(a["fresh_elapsed_seconds"])}** '
               f'({a["fresh_elapsed_seconds"]:.3f} seconds), with **{peak:.2f} GiB** peak process-tree '
               f'private memory. The installed-source recheck brings combined verification to '
               f'**{duration(a["combined_seconds"])}** ({a["combined_seconds"]:.3f} seconds).')
    note = f'''# Compact Atlas130 certificate

Status ({a['date']}): **verified**. {summary}
The complete catalogue theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`. The example and classification are updated.

Atlas130 is two triangles joined by an edge. Its catalogue target is
`p^3*(2*p-1)^2`, and the full admissible interval is `[1/2,1]`. The proof
joins an induced certificate on `[1/2,2/3]` with a four-root certificate on
`[2/3,1]`. Both pieces are included in the measured row build.

## Lower interval

Let `s=6*p-3` and `D=272160000000000000`. The checked identity is

```
D*(t(H130,W)-p^3*(2*p-1)^2)
  = sum of 14 nonnegative induced flag Gram expressions
    + sum of nonnegative Bernstein residuals times induced densities.
```

The underlying 28 positive integer Gram factors have exact rectangular
pullbacks. For each flag family the interval matrix is a positive Gram
pullback plus `s*(1-s)` times another positive matrix. All 936 Bernstein
coefficient equations are checked over integers. Eleven fixed-density
constraints cancel using `t(F disjoint-union K2,W)=p*t(F,W)`.

The shared interpretation uses explicit sums of labelled branch patterns.
Summing over unspecified cross edges gives products of conditional flag
densities. There are 71,168 flag-pair completions, 3,632 matrix coordinates,
and 15,336 nonzero counting coefficients. Every labelled six-vertex graph
has a checked relabeling to one of 156 representatives. The proof uses
labelled induced densities, so it does not need a separate flag-orbit
classification theorem.

Finite arithmetic is compressed into bounded positional encodings and
checked by Lean's kernel. The Python exporters and numerical discovery
are not premises of the theorem. The original rational certificate also
passed an independent exact audit based on ordered host permutations.

## Upper interval and file budget

On `[2/3,1]`, the upper piece uses the same compact four-root machinery as
[Atlas118](atlas118_compact_certificate.md), with common Gram denominator
`23328000000000000`. Its 407 coefficient equations and ten positive matrices
passed the external audit and the corresponding kernel checks. The degree-five
target requires interpolation scale 243.

Ten density modules were inlined verbatim into five block-sum modules. This
preserves their proofs and leaves 78 upper-piece files. The lower piece uses
20 files; the complete assembly and catalogue example bring the total to 100.
The row contains {a['row_source_bytes']:,} source bytes and imports
{a['shared_project_modules']} prebuilt shared project modules.

See [the verification record](../lean/docs/ATLAS130_VERIFICATION_PROGRESS.md)
for source hashes, timing, memory measurements, and shared-cost accounting.
'''
    progress = f'''# Atlas130 compact verification record

Atlas130 is **verified** ({a['date']}). {summary}
The complete catalogue theorem has only the three standard axioms. All source
hashes remained unchanged during verification. The live example and
classification are updated; Atlas203 is next.

The fresh build covers both `[1/2,2/3]` and `[2/3,1]`, the chromatic target,
graph identification, complete `SatisfiesLowerBound` theorem, and catalogue
example. It includes all 100 row files ({a['row_source_bytes']:,} bytes).
Row artifacts were absent at the start. Compilation was sequential, with
`LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for the entire row.

## Shared infrastructure

The row uses {a['shared_project_modules']} prebuilt shared project modules.
The {shared['file_count']} new induced/interpolation modules have successful,
source-matching component measurements totaling
{shared['summed_component_seconds']:.3f} seconds
({duration(shared['summed_component_seconds'])}), with
{shared['peak_private_bytes']/2**30:.2f} GiB peak private memory. Their total
source size is {shared['source_bytes']:,} bytes. These are component
measurements, **not** a fresh build of the complete shared closure.
See `verification_runs/atlas130/induced_shared_components.json` for each
source hash and originating run.

The previously recorded 57 compact shared modules took 2,884.982 seconds
summed across successful component runs, with a 12.32 GiB peak; see
`verification_runs/atlas118/shared_components.json`. Older shared modules
and Mathlib are prebuilt. No row-specific certificate data are charged to
the shared infrastructure.

## Records

- `verification_runs/atlas130/{fresh.name}/manifest.json`: complete source closure and hashes.
- `verification_runs/atlas130/{fresh.name}/summary.json`: fresh row acceptance.
- `verification_runs/atlas130/{fresh.name}/catalogue_compile.log`: complete theorem axiom audit.
- `verification_runs/atlas130/installed_example_1.json` and `.log`: installed-source recheck.
- `verification_runs/atlas130/completed_row.json`: acceptance summary.
- `verification_runs/atlas130/induced_independent_audit_1.json`: original induced audit.
- `verification_runs/atlas130/lower_compact_export_2.json`: integer conversion and completion-count audit.
- `verification_runs/atlas130/upper_independent_audit_1.json`: independent upper-piece audit.

Development failures and successful component runs are retained separately.
See [the certificate explanation](../../notes/atlas130_compact_certificate.md).
'''
    path = root/'LEAN_REMAINING_VERIFICATION_PLAN.md'
    plan = path.read_text(encoding='utf-8')
    for n in (126, 118, 122, 124, 181, 157, 169, 194, 185, 199):
        assert re.search(fr'^\| \d+ \| {n} \| \*\*Completed\.\*\*', plan, re.M)
    plan = re.sub(r'Atlas130 is now the active row\.\s*', '', plan)
    plan, count = re.subn(r'Atlas130\x27s induced-density interpretation is in progress\..*?(?=\| Priority)', '', plan, flags=re.S)
    assert count == 1
    paragraph = (f'Atlas130 completed on {a["date"]}. Both interval pieces and the full catalogue '
                 f'proof passed in a fresh 100-file build: {duration(a["fresh_elapsed_seconds"])} '
                 f'at {peak:.2f} GiB. The installed recheck brings combined verification to '
                 f'{duration(a["combined_seconds"])}. The final theorem has only the standard axioms; '
                 'its example and classification are updated. Atlas203 is now the active row. See '
                 '[the verification record](lean/docs/ATLAS130_VERIFICATION_PROGRESS.md).\n\n')
    marker = '| Priority | Atlas | Proposed route and reason |'
    assert plan.count(marker) == 1
    plan = plan.replace(marker, paragraph+marker)
    plan, count = re.subn(r'^\| 11 \| 130 \| .*? \|$',
                         f'| 11 | 130 | **Completed.** Induced lower interval and four-root upper interval; fresh full 100-file catalogue proof in {duration(a["fresh_elapsed_seconds"])} at {peak:.2f} GiB. |',
                         plan, flags=re.M)
    assert count == 1
    (root/'notes/atlas130_compact_certificate.md').write_text(note, encoding='utf-8')
    (root/'lean/docs/ATLAS130_VERIFICATION_PROGRESS.md').write_text(progress, encoding='utf-8')
    path.write_text(plan, encoding='utf-8')
    print('Recorded completed Atlas130; Atlas203 is next.')


if __name__ == '__main__':
    main()
