"""Cold, sequential rebuild of the complete Atlas126 method and axiom audit.

Only artifacts in the actual final dependency closure are moved to a retained
backup. Common infrastructure is prebuilt; the changed integer checker is also
rebuilt and separately identified in the report. No Lake parallel build or
external arithmetic oracle is used.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--lake',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--seconds',type=float,default=3600)
    parser.add_argument('--gib',type=float,default=16)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    lean=root/'lean'
    output=Path(args.output).resolve()
    output.relative_to(root)
    if output.exists():
        raise ValueError('Use a new output directory to preserve prior evidence.')
    output.mkdir(parents=True)
    common=['Taeyoung.Methods.Bernstein.CheckedTensor']
    entry='Taeyoung.Methods.Atlas126.Audit'
    example='Taeyoung.Examples.Graph126'
    example_source=lean/'Taeyoung/Examples/Graph126.lean'
    example_source.resolve().relative_to(root)
    original_example=example_source.read_bytes()
    prepared=example_source
    prepared_bytes=prepared.read_bytes()
    prepared_hash=hashlib.sha256(prepared_bytes).hexdigest()
    ordered=[]
    seen=set()

    def visit(module):
        if module in seen:return
        seen.add(module)
        path=lean/Path(*module.split('.')).with_suffix('.lean')
        if not path.exists():return
        for dep in re.findall(r'^import ([A-Za-z0-9_.]+)',path.read_text(encoding='utf-8-sig'),re.M):
            visit(dep)
        if module.startswith('Taeyoung.Methods.Atlas126.') or module in common:
            ordered.append(module)

    # Check the high-memory coloring-count module early in the build.
    visit('Taeyoung.Methods.Atlas126.Rows')
    visit(entry)
    sources={m:hashlib.sha256((lean/Path(*m.split('.')).with_suffix('.lean')).read_bytes()).hexdigest()
             for m in ordered}
    manifest=dict(entry=entry,modules=ordered,source_sha256=sources,
                  common_modules=common,row_module_count=len(ordered)-len(common)+1,
                  certificate_module_count=sum('.Cert.' in m for m in ordered),
                  catalogue_module=example,catalogue_source_sha256=prepared_hash,
                  seconds=args.seconds,gib=args.gib,sequential=True)
    (output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    build=(lean/'.lake/build/lib/lean').resolve()
    build.relative_to(root)
    backup=(output/'previous_artifacts').resolve()
    backup.relative_to(root)
    moved=[]
    started=time.monotonic()
    for module in [*ordered,example]:
        stem=build/Path(*module.split('.'))
        for source in stem.parent.glob(stem.name+'.olean*'):
            resolved=source.resolve()
            relative=resolved.relative_to(build)
            destination=(backup/relative).resolve()
            destination.relative_to(backup)
            if not resolved.is_file():raise ValueError(resolved)
            destination.parent.mkdir(parents=True,exist_ok=True)
            resolved.rename(destination)
            moved.append(str(relative))
    for module in [*ordered,example]:
        assert not (build/Path(*module.split('.')).with_suffix('.olean')).exists()
    (output/'moved_artifacts.json').write_text(json.dumps(moved,indent=2)+'\n',encoding='utf-8')
    print(f'Cold rebuild: {len(ordered)+1} modules, {manifest["certificate_module_count"]} numerical modules; '
          f'{len(moved)} prior artifacts retained in backup.',flush=True)
    command=[sys.executable,str(root/'experiments/verify_lean_modules.py'),
             '--lake',args.lake,'--output',str(output/'build'),
             '--seconds',str(args.seconds-(time.monotonic()-started)),
             '--gib',str(args.gib),*ordered]
    run=subprocess.run(command,cwd=root)
    report=json.loads((output/'build/summary.json').read_text(encoding='utf-8'))
    report['cold_rebuild']=True
    report['row_module_count']=manifest['row_module_count']
    report['common_modules']=common
    report['all_sources_unchanged']=all(
        hashlib.sha256((lean/Path(*m.split('.')).with_suffix('.lean')).read_bytes()).hexdigest()==digest
        for m,digest in sources.items())
    audit_path=output/'build'/entry/'compile.log'
    audit=audit_path.read_text(encoding='utf-8') if audit_path.exists() else ''
    sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',audit,re.S)
    standard={'propext','Classical.choice','Quot.sound'}
    report['axiom_audit_passed']=len(sets)==7 and all(
        {a.strip() for a in row.split(',') if a.strip()}<=standard for row in sets)
    report['catalogue_installed']=False
    report['catalogue_checked']=False
    # Check the final example under its real module name in a staging root.
    # Its source and artifact are installed only after the complete check and
    # axiom audit have passed within the shared deadline.
    if report['success'] and report['all_sources_unchanged'] and report['axiom_audit_passed']:
        staging=output/'sources'
        staged_source=staging/'Taeyoung/Examples/Graph126.lean'
        staged_source.parent.mkdir(parents=True)
        staged_source.write_bytes(prepared_bytes)
        staged_artifact=output/'catalogue.olean'
        remaining=args.seconds-(time.monotonic()-started)
        if remaining>0:
            command=[sys.executable,str(root/'experiments/run_bounded_lean.py'),
                     '--seconds',str(remaining),'--gib',str(args.gib),'--cwd',str(lean),
                     '--output',str(output/'catalogue_compile'),'--',args.lake,'env','lean',
                     '-M','12288','-j','1','--root',str(staging),
                     '-o',str(staged_artifact),str(staged_source)]
            final_run=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT,text=True)
            final_report=json.loads((output/'catalogue_compile.json').read_text(encoding='utf-8'))
            final_report.update(module=example,source_sha256=prepared_hash,
                                source_unchanged=staged_source.read_bytes()==prepared_bytes)
            report['results'].append(final_report)
            final_log=(output/'catalogue_compile.log').read_text(encoding='utf-8')
            final_sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',final_log,re.S)
            report['catalogue_checked']=bool(final_run.returncode==0 and len(final_sets)==1 and
                {a.strip() for a in final_sets[0].split(',') if a.strip()}<=standard and
                final_report['source_unchanged'])
            print(f'{example}: {final_report["elapsed_seconds"]:.1f}s, '
                  f'{final_report["peak_tree_private_bytes"]/2**30:.2f} GiB private, '
                  f'checked {report["catalogue_checked"]}',flush=True)
            if (report['catalogue_checked'] and time.monotonic()-started<=args.seconds and
                    example_source.read_bytes()==original_example and prepared.read_bytes()==prepared_bytes):
                (output/'Graph126.before.lean').write_bytes(original_example)
                shutil.copyfile(staged_source,example_source)
                destination=build/Path(*example.split('.')).with_suffix('.olean')
                destination.resolve().relative_to(build)
                shutil.copyfile(staged_artifact,destination)
                report['catalogue_installed']=True
    report['total_elapsed_seconds']=round(time.monotonic()-started,3)
    report['requested_modules']=[*ordered,example]
    report['total_module_count']=len(ordered)+1
    report['peak_private_bytes']=max((r['peak_tree_private_bytes'] for r in report['results']),default=0)
    report['peak_rss_bytes']=max((r['peak_tree_rss_bytes'] for r in report['results']),default=0)
    report['success']=bool(report['success'] and run.returncode==0 and
        report['all_sources_unchanged'] and report['axiom_audit_passed'] and
        report['catalogue_checked'] and report['catalogue_installed'] and
        report['total_elapsed_seconds']<=args.seconds)
    (output/'summary.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('Fresh row verification:',report['success'],
          f'{report["total_elapsed_seconds"]:.1f} seconds',flush=True)
    return 0 if report['success'] else 1


if __name__=='__main__':
    sys.exit(main())
