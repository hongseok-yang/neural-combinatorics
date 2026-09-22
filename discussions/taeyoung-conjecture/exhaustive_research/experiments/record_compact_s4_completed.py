"""Record an accepted compact row after its fresh build and installed recheck.

Only the requested classification row is promoted. Pre-existing mismatches
between other catalogue metadata and the Markdown table are preserved.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

from verify_compact_s4_fresh import axiom_audit


def duration(seconds):
    rounded=round(seconds)
    return f'{rounded//60}m{rounded%60:02d}s'


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--atlas',required=True,type=int)
    parser.add_argument('--fresh',required=True)
    parser.add_argument('--installed',required=True)
    parser.add_argument('--date',required=True)
    parser.add_argument('--method-label',default='Compact four-root SOS')
    parser.add_argument('--shared-report',action='append',default=[],
                        help='Additional common component reports, relative to this row run directory.')
    args=parser.parse_args()
    atlas=args.atlas
    root=Path(__file__).resolve().parents[1]
    fresh=Path(args.fresh).resolve()
    installed=Path(args.installed).resolve()
    fresh.relative_to(root)
    installed.relative_to(root)
    report=json.loads((fresh/'summary.json').read_text())
    manifest=json.loads((fresh/'manifest.json').read_text())
    smoke=json.loads(installed.with_suffix('.json').read_text())
    assert report['success'] and report['catalogue_installed']
    assert report['all_sources_unchanged'] and report['axiom_audit_passed']
    assert manifest['catalogue']==f'Taeyoung.Examples.Graph{atlas}'
    assert smoke['exit_code']==0 and smoke['termination']=='exited'
    assert smoke['command'][-1].replace('\\','/')==f'Taeyoung/Examples/Graph{atlas}.lean'
    assert axiom_audit(installed.with_suffix('.log').read_text(encoding='utf-8'))
    assert axiom_audit((fresh/'catalogue_compile.log').read_text(encoding='utf-8'))
    elapsed=report['total_elapsed_seconds']
    combined=elapsed+smoke['elapsed_seconds']
    peak=max(report['peak_private_bytes'],smoke['peak_tree_private_bytes'])
    assert combined<=3600 and peak<=16*2**30
    for module,digest in manifest['source_sha256'].items():
        source=root/'lean'/Path(*module.split('.')).with_suffix('.lean')
        assert hashlib.sha256(source.read_bytes()).hexdigest()==digest,module
    example=root/f'lean/Taeyoung/Examples/Graph{atlas}.lean'
    digest=hashlib.sha256(example.read_bytes()).hexdigest()
    assert digest==manifest['prepared_sha256']
    assert 'formalization := .verified' in example.read_text(encoding='utf-8')
    row_bytes=sum((root/'lean'/Path(*m.split('.')).with_suffix('.lean')).stat().st_size
                  for m in manifest['modules'])+example.stat().st_size
    classification=root/'GRAPH_CLASSIFICATION_UP_TO_6_VERTICES.md'
    original=classification.read_text(encoding='utf-8')
    lines=original.splitlines()
    matching=[i for i,line in enumerate(lines) if line.startswith(f'| {atlas} |')]
    assert len(matching)==1
    index=matching[0]
    fields=lines[index].split(' | ')
    assert len(fields)==9,fields
    fields[7]='✅ **Verified**'
    fields[8]=(f'[{args.method_label}](notes/atlas{atlas}_compact_certificate.md): '
               f'complete catalogue kernel proof; '
               f'[fresh {report["row_file_count"]}-file verification]'
               f'(lean/docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md) in '
               f'{duration(elapsed)} at {peak/2**30:.2f} GiB |')
    lines[index]=' | '.join(fields)
    rows=[line for line in lines if re.match(r'^\| \d+ \|',line)]
    assert len(rows)==117
    counts={label:sum(label in row.split(' | ')[7] for row in rows)
            for label in ['Verified','Believed','Unresolved']}
    assert sum(counts.values())==117
    believed=[int(row.split(' | ')[0].lstrip('| ')) for row in rows
              if 'Believed' in row.split(' | ')[7]]
    unresolved=[int(row.split(' | ')[0].lstrip('| ')) for row in rows
                if 'Unresolved' in row.split(' | ')[7]]
    listing=(', '.join(map(str,believed[:-1]))+', and '+str(believed[-1])
             if len(believed)>1 else ', '.join(map(str,believed)))
    for i,line in enumerate(lines):
        if line.startswith('* ✅ **Verified**'):
            lines[i]=re.sub(r'\*\*\d+ rows\.\*\*',f'**{counts["Verified"]} rows.**',line)
        elif line.startswith('* 🔧 **Believed**'):
            noun='row' if counts['Believed']==1 else 'rows'
            lines[i]=re.sub(r'\*\*\d+ rows?\*\* \(Atlas .*?\)\.',
                           f'**{counts["Believed"]} {noun}** (Atlas {listing}).',line)
        elif line.startswith('* ⚪ **Unresolved**'):
            ids=(', '.join(map(str,unresolved[:-1]))+' and '+str(unresolved[-1])
                 if len(unresolved)>1 else ', '.join(map(str,unresolved)))
            noun='row' if len(unresolved)==1 else 'rows'
            details=f': Atlas {ids}.' if unresolved else '.'
            lines[i]=('* ⚪ **Unresolved** — Lean asserts only `P ∨ ¬P`. '
                      f'**{len(unresolved)} {noun}**{details} '
                      'A row stays here until its full classification theorem is carried into Lean.')
    updated='\n'.join(lines)+'\n'
    check=root/'lean/Taeyoung/CheckVerified.lean'
    check_source=check.read_text(encoding='utf-8')
    new_import=f'import Taeyoung.Examples.Graph{atlas}'
    if new_import not in check_source.splitlines():
        check_source=new_import+'\n'+check_source
    audit=f'#print axioms Taeyoung.Examples.Graph{atlas}.status'
    if audit not in check_source.splitlines():
        check_source+=(f'\n/-! Atlas{atlas}: complete compact integer SOS verification; '
                       f'see `docs/ATLAS{atlas}_VERIFICATION_PROGRESS.md`. -/\n{audit}\n')
    record=dict(atlas=atlas,status='verified',date=args.date,
                theorem=manifest['catalogue']+'.status',
                fresh_report=(fresh/'summary.json').relative_to(fresh.parent).as_posix(),
                row_file_count=report['row_file_count'],row_source_bytes=row_bytes,
                shared_project_modules=report['shared_file_count'],
                new_shared_component_report='../atlas118/shared_components.json',
                additional_shared_component_reports=args.shared_report,
                fresh_elapsed_seconds=elapsed,installed_smoke_seconds=smoke['elapsed_seconds'],
                combined_seconds=round(combined,3),peak_private_bytes=peak,
                axioms=['propext','Classical.choice','Quot.sound'],
                classification_counts=counts,sequential=True,example_source_sha256=digest)
    # All guards and source checks finish before any metadata is modified.
    classification.write_text(updated,encoding='utf-8')
    check.write_text(check_source,encoding='utf-8')
    (fresh.parent/'completed_row.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))


if __name__=='__main__':
    main()
