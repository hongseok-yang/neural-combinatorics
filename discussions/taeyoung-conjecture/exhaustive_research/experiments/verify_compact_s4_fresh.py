"""Fresh sequential verification of one compact S4 row, then catalogue install.

Row artifacts are retained in a backup, not deleted. The prepared catalogue
source is checked under its real module name and is installed only after the
complete row and its axiom audit pass within the shared resource budget.
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


STANDARD={'propext','Classical.choice','Quot.sound'}


def axiom_audit(log):
    sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
    return bool(sets) and all({a.strip() for a in s.split(',') if a.strip()} <= STANDARD for s in sets)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--atlas',required=True,type=int)
    parser.add_argument('--lake',required=True)
    parser.add_argument('--prepared',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--seconds',type=float,default=3600)
    parser.add_argument('--gib',type=float,default=16)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    lean=root/'lean'
    output=Path(args.output).resolve()
    output.relative_to(root)
    if output.exists(): raise ValueError('Use a fresh output directory.')
    output.mkdir(parents=True)
    prefix=f'Taeyoung.Methods.RootedSOS.CompactS4.Atlas{args.atlas}.'
    entry=prefix+'Certificate'
    example=f'Taeyoung.Examples.Graph{args.atlas}'
    example_source=lean/Path(*example.split('.')).with_suffix('.lean')
    original=example_source.read_bytes()
    prepared=Path(args.prepared).resolve()
    prepared.relative_to(root)
    prepared_bytes=prepared.read_bytes()
    if f'import {entry}'.encode() not in prepared_bytes:
        raise ValueError('Prepared example does not import the complete certificate.')
    if re.search(rb'\b(sorry|admit|native_decide)\b',prepared_bytes):
        raise ValueError('Prepared catalogue source contains an unsupported placeholder or oracle.')
    ordered=[]
    shared=[]
    hashes={}
    seen=set()

    def visit(module):
        if module in seen:return
        seen.add(module)
        path=lean/Path(*module.split('.')).with_suffix('.lean')
        if not path.exists():return
        data=path.read_bytes()
        hashes[module]=hashlib.sha256(data).hexdigest()
        for dep in re.findall(r'^import ([A-Za-z0-9_.]+)',data.decode('utf-8-sig'),re.M):
            visit(dep)
        if module.startswith(prefix):
            if re.search(rb'\b(sorry|admit|native_decide)\b',data):raise ValueError(module)
            ordered.append(module)
        elif module.startswith('Taeyoung.'):
            shared.append(module)

    visit(prefix+'Coloring')
    visit(entry)
    build=(lean/'.lake/build/lib/lean').resolve()
    build.relative_to(root)
    for m in shared:
        if not (build/Path(*m.split('.')).with_suffix('.olean')).exists():
            raise ValueError(f'Unbuilt shared dependency: {m}')
    manifest=dict(entry=entry,modules=ordered,row_file_count=len(ordered)+1,
                  shared_modules=shared,shared_file_count=len(shared),
                  source_sha256=hashes,catalogue=example,
                  prepared_sha256=hashlib.sha256(prepared_bytes).hexdigest(),
                  sequential=True,seconds=args.seconds,gib=args.gib)
    (output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    started=time.monotonic()
    backup=(output/'previous_artifacts').resolve()
    backup.relative_to(root)
    moved=[]
    for module in [*ordered,example]:
        stem=build/Path(*module.split('.'))
        for artifact in stem.parent.glob(stem.name+'.olean*'):
            source=artifact.resolve()
            relative=source.relative_to(build)
            destination=(backup/relative).resolve()
            destination.relative_to(backup)
            if not source.is_file():raise ValueError(source)
            destination.parent.mkdir(parents=True,exist_ok=True)
            source.rename(destination)
            moved.append(str(relative))
    for module in [*ordered,example]:
        assert not (build/Path(*module.split('.')).with_suffix('.olean')).exists()
    (output/'moved_artifacts.json').write_text(json.dumps(moved,indent=2)+'\n')
    print('Fresh row:',len(ordered)+1,'files;',len(shared),'prebuilt shared dependencies.',flush=True)
    command=[sys.executable,str(root/'experiments/verify_lean_modules.py'),'--lake',args.lake,
             '--output',str(output/'build'),'--seconds',str(args.seconds-(time.monotonic()-started)),
             '--gib',str(args.gib),*ordered]
    run=subprocess.run(command,cwd=root)
    report=json.loads((output/'build/summary.json').read_text())
    report.update(cold_rebuild=True,row_file_count=len(ordered)+1,shared_file_count=len(shared),
                  catalogue_checked=False,catalogue_installed=False)
    audit=output/'build'/entry/'compile.log'
    report['axiom_audit_passed']=audit.exists() and axiom_audit(audit.read_text(encoding='utf-8'))
    report['all_sources_unchanged']=all(
        hashlib.sha256((lean/Path(*m.split('.')).with_suffix('.lean')).read_bytes()).hexdigest()==h
        for m,h in hashes.items())
    if report['success'] and report['axiom_audit_passed'] and report['all_sources_unchanged']:
        staging=output/'sources'
        staged_source=staging/Path(*example.split('.')).with_suffix('.lean')
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
            final=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            item=json.loads((output/'catalogue_compile.json').read_text())
            item.update(module=example,source_sha256=manifest['prepared_sha256'],
                        source_unchanged=staged_source.read_bytes()==prepared_bytes)
            report['results'].append(item)
            report['catalogue_checked']=bool(final.returncode==0 and item['source_unchanged'] and
                axiom_audit((output/'catalogue_compile.log').read_text(encoding='utf-8')))
            if (report['catalogue_checked'] and time.monotonic()-started<=args.seconds and
                    example_source.read_bytes()==original and prepared.read_bytes()==prepared_bytes):
                (output/f'Graph{args.atlas}.before.lean').write_bytes(original)
                shutil.copyfile(staged_source,example_source)
                shutil.copyfile(staged_artifact,build/Path(*example.split('.')).with_suffix('.olean'))
                report['catalogue_installed']=True
    report['total_elapsed_seconds']=round(time.monotonic()-started,3)
    report['peak_private_bytes']=max((r['peak_tree_private_bytes'] for r in report['results']),default=0)
    report['peak_rss_bytes']=max((r['peak_tree_rss_bytes'] for r in report['results']),default=0)
    report['success']=bool(report['success'] and run.returncode==0 and report['axiom_audit_passed'] and
        report['all_sources_unchanged'] and report['catalogue_installed'] and
        report['total_elapsed_seconds']<=args.seconds)
    (output/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Fresh row verification:',report['success'],report['total_elapsed_seconds'],'seconds',flush=True)
    return 0 if report['success'] else 1


if __name__=='__main__':
    sys.exit(main())
