"""Account for successful, source-matching shared induced component builds.

Measurements are summed once per module and are explicitly not represented as
a fresh build of the whole common closure. Row-specific sources are excluded.
"""

import hashlib
import json
from pathlib import Path
import re


def main():
    root = Path(__file__).resolve().parents[1]
    lean = root/'lean'
    runs = lean/'verification_runs/atlas130'
    shared_prefix = 'Taeyoung.Methods.RootedSOS.Induced.'
    selected = {}
    for path in sorted(runs.glob('*/summary.json'), key=lambda p: p.stat().st_mtime):
        report = json.loads(path.read_text(encoding='utf-8'))
        for item in report.get('results', []):
            module = item.get('module', '')
            if not (module.startswith(shared_prefix) or module == 'Taeyoung.Methods.RootedSOS.ThirdDegreeFiveCoefficients'):
                continue
            source = lean/Path(*module.split('.')).with_suffix('.lean')
            if (item['exit_code'] == 0 and item['termination'] == 'exited' and
                    item.get('source_unchanged') and source.is_file() and
                    item['source_sha256'] == hashlib.sha256(source.read_bytes()).hexdigest()):
                selected[module] = dict(item, component_run=path.parent.name)
    seen = set()

    def visit(module):
        if module in seen:
            return
        source = lean/Path(*module.split('.')).with_suffix('.lean')
        if not source.is_file():
            return
        seen.add(module)
        for dep in re.findall(r'^import ([A-Za-z0-9_.]+)', source.read_text(encoding='utf-8-sig'), re.M):
            visit(dep)

    visit('Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Certificate')
    required = sorted(m for m in seen if m.startswith(shared_prefix) or m.endswith('.ThirdDegreeFiveCoefficients'))
    missing = sorted(set(required)-set(selected))
    assert not missing, missing
    items = [selected[m] for m in required]
    record = dict(success=True, status='component measurements, not a complete fresh shared rebuild',
                  new_shared_modules=required, file_count=len(items),
                  summed_component_seconds=round(sum(r['elapsed_seconds'] for r in items), 3),
                  peak_private_bytes=max(r['peak_tree_private_bytes'] for r in items),
                  peak_rss_bytes=max(r['peak_tree_rss_bytes'] for r in items),
                  source_bytes=sum((lean/Path(*m.split('.')).with_suffix('.lean')).stat().st_size for m in required),
                  sequential=True, results=items)
    (runs/'induced_shared_components.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in record.items() if k not in ('new_shared_modules', 'results')}, indent=2))


if __name__ == '__main__':
    main()
