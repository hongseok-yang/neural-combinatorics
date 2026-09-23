#!/usr/bin/env python3
"""Fresh, sequential, memory-bounded verification of the 117-row Lean catalogue.

Every Lean module of this project that a catalogue row depends on is compiled
from source into a new, empty build directory.  Nothing previously built in
this project is reused; only Mathlib and its dependency packages are taken
prebuilt from the Lake environment.  Exactly one `lean` process runs at a
time, with one thread, under a process-tree memory cap.

The work is split into independently measured units:

* a **row unit** for each of the 117 catalogue rows: the modules that only
  this row imports, followed by the row's audit;
* a **shared unit** for each library whose modules are imported by more than
  one row (for example `Foundation`, `Fisher`, `PureChordal`, or the Atlas 43
  chain that Atlas 196 reuses).

Rows are processed one at a time, in Atlas order.  Before a row, every shared
unit it needs that has not been verified yet is compiled completely, as its
own unit.  Then the row unit runs: its own modules are compiled and a
generated audit file checks, inside Lean, that the row's theorem `status` has
exactly the catalogue statement (`SatisfiesLowerBound graph` or
`ViolatesLowerBound graph`), that the row's metadata agrees with it, and which
axioms the theorem depends on.  Every unit records its wall time, peak memory,
module count, source size and the state of the machine.

Before any compilation, independent Python checks confirm that the 117 rows
are exactly the Atlas graphs in scope, that each row's Lean edge list is the
Atlas graph with the stated invariants, and that the row statuses agree with
the Markdown catalogue.  After the rows, the kernel-checked counts in
`Taeyoung.Catalogue.Counts` are compiled.

A row is verified when every module it depends on compiles, its audit
compiles, and the theorem depends on no axioms beyond `propext`,
`Classical.choice` and `Quot.sound` (in particular not on `sorryAx` or
`Lean.ofReduceBool`).

Requirements: the Lean toolchain named in `lean-toolchain` (via elan), a
resolved Lake environment with Mathlib built, Python >= 3.11, and the Python
packages `psutil` and `networkx`.  See `tools/README.md`.

Typical use, from the `lean/` directory:

    python tools/verify_catalogue.py --plan            # show the units, compile nothing
    python tools/verify_catalogue.py                   # full run, 32 GiB cap
    python tools/verify_catalogue.py --resume verification_runs/full-20260923-160000
    python tools/verify_catalogue.py --rows 17,43,127  # a subset, for testing
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import itertools
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

try:
    import psutil
except ImportError:  # pragma: no cover - reported to the user
    sys.exit('verify_catalogue.py needs the Python package psutil (pip install psutil).')

ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
EXPECTED_ROWS = 117
GIB = 2 ** 30
POLL_SECONDS = 0.25
FREE_MEMORY_WAIT_SECONDS = 30
MAX_PATH_WARNING = 250


# --------------------------------------------------------------------------- helpers

def now_iso() -> str:
    return dt.datetime.now().astimezone().isoformat(timespec='seconds')


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def gib(n_bytes: float) -> float:
    return round(n_bytes / GIB, 3)


def hms(seconds: float | None) -> str:
    if seconds is None:
        return '—'
    seconds = int(round(seconds))
    return f'{seconds // 3600}:{seconds % 3600 // 60:02d}:{seconds % 60:02d}'


def write_json(path: Path, obj) -> None:
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    os.replace(tmp, path)


def append_jsonl(path: Path, obj) -> None:
    with path.open('a', encoding='utf-8') as fh:
        fh.write(json.dumps(obj, ensure_ascii=False) + '\n')


def read_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]


class Console:
    """Prints progress and mirrors it to progress.log in the run directory."""

    def __init__(self, log_path: Path | None):
        self.log_path = log_path

    def __call__(self, message: str = '') -> None:
        print(message, flush=True)
        if self.log_path is not None:
            with self.log_path.open('a', encoding='utf-8') as fh:
                fh.write(message + '\n')


# --------------------------------------------------------------------------- project model

IMPORT_RE = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)$')


@dataclass
class Module:
    name: str
    path: Path
    imports: list[str]          # project-internal imports only
    source: bytes

    @property
    def lines(self) -> int:
        return self.source.count(b'\n')


@dataclass
class Row:
    atlas: int
    module: str
    n: int
    edges: list[tuple[int, int]]
    status: str                  # 'positive' / 'negative' (from metadata)
    formalization: str           # 'verified' / ...
    statement: str               # 'SatisfiesLowerBound' / 'ViolatesLowerBound'
    vertex_count: int
    edge_count: int
    chromatic_number: int
    graph6: str
    closure: list[str] = field(default_factory=list)

    @property
    def label(self) -> str:
        return f'Atlas {self.atlas:03d}'


@dataclass
class SharedUnit:
    name: str
    modules: list[str]           # dependency order
    users: set[int]              # rows importing at least one of the modules
    depends_on: list[str] = field(default_factory=list)


class Project:
    """The Lean sources of this project and their import graph."""

    def __init__(self, root: Path, lib: str = 'Taeyoung'):
        self.root = root
        self.lib = lib
        self.modules: dict[str, Module] = {}

    def module_path(self, name: str) -> Path:
        return self.root.joinpath(*name.split('.')).with_suffix('.lean')

    def load(self, name: str) -> Module:
        if name in self.modules:
            return self.modules[name]
        path = self.module_path(name)
        if not path.exists():
            raise SystemExit(f'error: module {name} is imported but {path} does not exist')
        source = path.read_bytes()
        imports = []
        for line in source.decode('utf-8-sig').splitlines():
            m = IMPORT_RE.match(line)
            if m:
                imports += [x for x in m.group(1).split() if x == self.lib or x.startswith(self.lib + '.')]
        module = Module(name, path, imports, source)
        self.modules[name] = module
        return module

    def closure(self, name: str) -> list[str]:
        """Import closure of `name` (project modules only), dependencies first."""
        order: list[str] = []
        seen: set[str] = set()
        stack = [(name, False)]
        while stack:
            current, expanded = stack.pop()
            if expanded:
                order.append(current)
                continue
            if current in seen:
                continue
            seen.add(current)
            stack.append((current, True))
            for dep in reversed(self.load(current).imports):
                if dep not in seen:
                    stack.append((dep, False))
        return order


ROW_PATTERNS = {
    'graph': re.compile(r'graphFromEdges\s+(\d+)\s*\[(.*?)\]', re.S),
    'atlas': re.compile(r'atlasId\s*:=\s*(\d+)'),
    'vertex_count': re.compile(r'vertexCount\s*:=\s*(\d+)'),
    'edge_count': re.compile(r'edgeCount\s*:=\s*(\d+)'),
    'chromatic_number': re.compile(r'chromaticNumber\s*:=\s*(\d+)'),
    'graph6': re.compile(r'graph6\s*:=\s*"([^"]*)"'),
    'status': re.compile(r'\bstatus\s*:=\s*\.(\w+)'),
    'formalization': re.compile(r'formalization\s*:=\s*\.(\w+)'),
    'statement': re.compile(r'theorem\s+status\s*:\s*(SatisfiesLowerBound|ViolatesLowerBound)\s+graph\b'),
}


def parse_row(project: Project, path: Path) -> Row:
    module = f'{project.lib}.Examples.{path.stem}'
    text = path.read_text(encoding='utf-8-sig')
    found = {}
    for key, pattern in ROW_PATTERNS.items():
        m = pattern.search(text)
        if not m:
            raise SystemExit(f'error: could not read `{key}` from {path}')
        found[key] = m
    n = int(found['graph'].group(1))
    edges = [(int(a), int(b)) for a, b in re.findall(r'\(\s*(\d+)\s*,\s*(\d+)\s*\)', found['graph'].group(2))]
    return Row(atlas=int(found['atlas'].group(1)), module=module, n=n, edges=edges,
               status=found['status'].group(1), formalization=found['formalization'].group(1),
               statement=found['statement'].group(1),
               vertex_count=int(found['vertex_count'].group(1)), edge_count=int(found['edge_count'].group(1)),
               chromatic_number=int(found['chromatic_number'].group(1)), graph6=found['graph6'].group(1))


# --------------------------------------------------------------------------- measurement units

def library_of(module: str) -> str:
    """The library a shared module belongs to, e.g. `Foundation`, `Fisher`,
    `PureChordal`.  The large RootedSOS library is split into its parts."""
    parts = module.split('.')[1:]
    if not parts:
        return 'Root'
    if parts[0] == 'Methods' and len(parts) >= 2:
        if parts[1] == 'RootedSOS' and len(parts) >= 3:
            sub = parts[2]
            if sub.startswith(('Atlas43', 'Atlas196')):
                return 'RootedSOS: Atlas 43 chain'
            if sub in ('CompactS4', 'Induced'):
                return f'RootedSOS: {sub}'
            return 'RootedSOS: core'
        return parts[1]
    return parts[0]


def build_units(project: Project, rows: list[Row]) -> tuple[list[SharedUnit], dict[str, set[int]], dict[str, str]]:
    """Partition the modules the rows depend on.

    A module imported by exactly one row belongs to that row's unit.  Modules
    imported by several rows are grouped by library into shared units.  A
    shared module only imports shared modules (anything it imports is used by
    at least the same rows), so shared units never depend on row units.  If two
    libraries import each other, they are merged into one unit, so the units
    form an acyclic graph; they are returned in dependency order.
    """
    users: dict[str, set[int]] = {}
    order: list[str] = []
    for row in rows:
        for m in row.closure:
            if m not in users:
                users[m] = set()
                order.append(m)
            users[m].add(row.atlas)
    position = {m: i for i, m in enumerate(order)}
    shared = [m for m in order if len(users[m]) > 1]
    group = {m: library_of(m) for m in shared}
    edges: dict[str, set[str]] = {g: set() for g in set(group.values())}
    for m in shared:
        for dep in project.modules[m].imports:
            if group.get(dep, group[m]) != group[m]:
                edges[group[m]].add(group[dep])
    # Merge libraries that import each other (strongly connected components).
    component = strongly_connected(edges)
    merged: dict[str, list[str]] = {}
    for g, c in component.items():
        merged.setdefault(c, []).append(g)
    unit_name = {c: ' + '.join(sorted(gs)) for c, gs in merged.items()}
    unit_of = {m: unit_name[component[group[m]]] for m in shared}
    unit_edges: dict[str, set[str]] = {u: set() for u in unit_name.values()}
    for g, targets in edges.items():
        for t in targets:
            a, b = unit_name[component[g]], unit_name[component[t]]
            if a != b:
                unit_edges[a].add(b)
    units: dict[str, SharedUnit] = {}
    for m in sorted(shared, key=position.get):
        u = units.setdefault(unit_of[m], SharedUnit(unit_of[m], [], set()))
        u.modules.append(m)
        u.users |= users[m]
    for name, u in units.items():
        u.depends_on = sorted(unit_edges[name])
    ordered: list[SharedUnit] = []
    placed: set[str] = set()

    def place(name: str) -> None:
        if name in placed:
            return
        placed.add(name)
        for dep in sorted(unit_edges[name], key=lambda n: position[units[n].modules[0]]):
            place(dep)
        ordered.append(units[name])

    for name in sorted(units, key=lambda n: position[units[n].modules[0]]):
        place(name)
    return ordered, users, unit_of


def strongly_connected(edges: dict[str, set[str]]) -> dict[str, str]:
    """Tarjan's algorithm; maps each node to a representative of its component."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    result: dict[str, str] = {}
    counter = itertools.count()

    def visit(v: str) -> None:
        index[v] = low[v] = next(counter)
        stack.append(v)
        on_stack.add(v)
        for w in edges[v]:
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            while True:
                w = stack.pop()
                on_stack.discard(w)
                result[w] = v
                if w == v:
                    break

    for v in sorted(edges):
        if v not in index:
            visit(v)
    return result


# --------------------------------------------------------------------------- static checks

def chromatic_number(n: int, edges: list[tuple[int, int]]) -> int:
    for k in range(1, n + 1):
        for colouring in itertools.product(range(k), repeat=n):
            if all(colouring[a] != colouring[b] for a, b in edges):
                return k
    return n


def static_checks(rows: list[Row], markdown: Path | None, say: Console) -> dict:
    """Independent Python checks of the catalogue's scope and graph data."""
    try:
        import networkx as nx
    except ImportError:
        raise SystemExit('error: the static checks need networkx (pip install networkx); '
                         'use --skip-static-checks to run without them')
    problems: list[str] = []
    atlas = nx.graph_atlas_g()
    in_scope = {i for i, g in enumerate(atlas)
                if 1 <= g.number_of_nodes() <= 6 and g.number_of_edges() > 0
                and not nx.is_bipartite(g)
                and min(d for _, d in g.degree()) > 0
                and all(len(c) != 2 for c in nx.connected_components(g))}
    ids = {r.atlas for r in rows}
    if len(rows) != EXPECTED_ROWS:
        problems.append(f'expected {EXPECTED_ROWS} row files, found {len(rows)}')
    if ids != in_scope:
        problems.append(f'row set differs from the Atlas graphs in scope: missing {sorted(in_scope - ids)}, '
                        f'extra {sorted(ids - in_scope)}')
    for r in rows:
        where = f'{r.label} ({r.module})'
        if f'Graph{r.atlas:03d}' != r.module.rsplit('.', 1)[-1]:
            problems.append(f'{where}: atlasId does not match the file name')
        if r.atlas >= len(atlas):
            problems.append(f'{where}: no such Atlas graph')
            continue
        g = nx.Graph()
        g.add_nodes_from(range(r.n))
        g.add_edges_from(r.edges)
        if any(not (0 <= a < r.n and 0 <= b < r.n) or a == b for a, b in r.edges):
            problems.append(f'{where}: edge list has an invalid vertex or loop')
        if not nx.is_isomorphic(g, atlas[r.atlas]):
            problems.append(f'{where}: the Lean edge list is not isomorphic to Atlas graph {r.atlas}')
        if (r.vertex_count, r.edge_count) != (r.n, g.number_of_edges()):
            problems.append(f'{where}: metadata vertex/edge counts {(r.vertex_count, r.edge_count)} '
                            f'!= graph {(r.n, g.number_of_edges())}')
        chi = chromatic_number(r.n, r.edges)
        if chi != r.chromatic_number:
            problems.append(f'{where}: metadata chromatic number {r.chromatic_number} != {chi}')
        expected_statement = {'positive': 'SatisfiesLowerBound', 'negative': 'ViolatesLowerBound'}.get(r.status)
        if r.statement != expected_statement:
            problems.append(f'{where}: status `{r.status}` but theorem states `{r.statement}`')
        if r.formalization != 'verified':
            problems.append(f'{where}: formalization is `{r.formalization}`, not `verified`')
    markdown_result = 'not checked'
    if markdown is not None and markdown.exists():
        table = {}
        for line in markdown.read_text(encoding='utf-8').splitlines():
            m = re.match(r'\|\s*(\d+)\s*\|.*?\*\*(Positive|Negative|Open|Partial)\*\*\s*\|\s*\S*\s*\*\*(\w+)\*\*', line)
            if m:
                table[int(m.group(1))] = (m.group(2).lower(), m.group(3).lower())
        for r in rows:
            if r.atlas not in table:
                problems.append(f'{r.label}: missing from {markdown.name}')
            elif table[r.atlas] != (r.status, r.formalization):
                problems.append(f'{r.label}: {markdown.name} says {table[r.atlas]}, '
                                f'Lean metadata says {(r.status, r.formalization)}')
        markdown_result = f'{len(table)} rows compared'
    counts = {s: sum(r.status == s for r in rows) for s in ('positive', 'negative')}
    say(f'Static checks: {len(rows)} rows ({counts["positive"]} positive, {counts["negative"]} negative); '
        f'scope, edge lists, invariants, statements; markdown: {markdown_result}; '
        f'{"no problems" if not problems else f"{len(problems)} problem(s)"}')
    for p in problems:
        say(f'  PROBLEM: {p}')
    return dict(ok=not problems, problems=problems, counts=counts, markdown=markdown_result)


def source_scan(project: Project, modules: list[str]) -> dict:
    """Informational count of constructs that deserve a reader's attention.

    The decisive check is the axiom audit; this scan only lists where such
    tokens occur (comments included)."""
    patterns = {
        'sorry': re.compile(rb'\bsorry\b'),
        'admit': re.compile(rb'\badmit\b'),
        'native_decide': re.compile(rb'\bnative_decide\b'),
        'axiom declaration': re.compile(rb'^\s*(?:private\s+|protected\s+)?axiom\s', re.M),
        'implemented_by / extern': re.compile(rb'implemented_by|@\[extern'),
    }
    hits = {k: [] for k in patterns}
    for name in modules:
        src = project.modules[name].source
        for key, pattern in patterns.items():
            if pattern.search(src):
                hits[key].append(name)
    return {k: dict(count=len(v), modules=v[:20]) for k, v in hits.items()}


# --------------------------------------------------------------------------- environment

def lake_environment(lake: str, root: Path) -> dict[str, str]:
    probe = 'import json, os; print(json.dumps(dict(os.environ)))'
    run = subprocess.run([lake, 'env', sys.executable, '-c', probe], cwd=root,
                         capture_output=True, text=True, encoding='utf-8')
    if run.returncode != 0:
        raise SystemExit(f'error: `lake env` failed in {root}:\n{run.stderr.strip()}\n'
                         'Resolve the Lake dependencies first (see tools/README.md).')
    return json.loads(run.stdout.strip().splitlines()[-1])


def dependency_search_path(env: dict[str, str], root: Path) -> list[str]:
    """LEAN_PATH without this project's own build directory."""
    own = (root / '.lake').resolve()
    entries = [p for p in env.get('LEAN_PATH', '').split(os.pathsep) if p]
    kept = []
    for entry in entries:
        resolved = Path(entry).resolve()
        if resolved == own or own in resolved.parents:
            continue
        kept.append(str(resolved))
    if not any((Path(p) / 'Mathlib.olean').exists() for p in kept):
        raise SystemExit('error: no prebuilt Mathlib found on the Lake search path. '
                         'Build or download it first (for example `lake exe cache get`).')
    return kept


def lean_options(root: Path, lib: str) -> list[str]:
    """`-D` flags equivalent to the lakefile's leanOptions."""
    lakefile = root / 'lakefile.toml'
    if not lakefile.exists():
        return []
    config = tomllib.loads(lakefile.read_text(encoding='utf-8'))
    options = list(config.get('leanOptions', []))
    for library in config.get('lean_lib', []):
        if library.get('name') == lib:
            options += library.get('leanOptions', [])
    flags = []
    for option in options:
        value = option['value']
        value = str(value).lower() if isinstance(value, bool) else str(value)
        flags += ['-D', f"{option['name']}={value}"]
    return flags


def git_state(root: Path) -> dict:
    def git(*args):
        run = subprocess.run(['git', *args], cwd=root, capture_output=True, text=True, encoding='utf-8')
        return run.stdout.strip() if run.returncode == 0 else None
    commit = git('rev-parse', 'HEAD')
    dirty = git('status', '--porcelain', '--', '.')
    return dict(commit=commit, modified_or_untracked_paths=None if dirty is None else len(dirty.splitlines()))


def dependency_revision(env: dict[str, str]) -> str:
    """Identify the Mathlib build that is trusted: its git commit if available."""
    for entry in env.get('LEAN_PATH', '').split(os.pathsep):
        parents = Path(entry).resolve().parents
        package = parents[3] if len(parents) > 3 else None      # <package>/.lake/build/lib/lean
        if package is not None and package.name.lower() == 'mathlib':
            run = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=package, capture_output=True, text=True)
            return run.stdout.strip() or f'unknown ({package})'
    return 'unknown'


def other_lean_processes(ours: set[int]) -> dict:
    count, rss = 0, 0
    for proc in psutil.process_iter(['name', 'memory_info']):
        name = (proc.info.get('name') or '').lower()
        if name in ('lean', 'lean.exe') and proc.pid not in ours:
            count += 1
            rss += proc.info['memory_info'].rss if proc.info.get('memory_info') else 0
    return dict(count=count, rss_gib=gib(rss))


def machine_snapshot() -> dict:
    vm = psutil.virtual_memory()
    return dict(available_gib=gib(vm.available), used_percent=vm.percent,
                cpu_percent=psutil.cpu_percent(interval=0.5),
                other_lean=other_lean_processes(set()))


# --------------------------------------------------------------------------- bounded execution

class Interrupted(Exception):
    pass


def run_bounded(command: list[str], cwd: Path, env: dict[str, str], cap_bytes: int, log_path: Path) -> dict:
    """Run one command; kill its whole process tree if it exceeds `cap_bytes`.

    Memory is the larger of the tree's resident set and, on Windows, its private
    (committed) bytes, sampled every POLL_SECONDS."""
    log_path.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    peak_rss = peak_private = 0
    cpu_seconds = 0.0
    termination = 'exited'
    with log_path.open('w', encoding='utf-8') as log:
        log.write('$ ' + ' '.join(command) + '\n\n')
        log.flush()
        child = subprocess.Popen(command, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
        known = {child.pid: psutil.Process(child.pid)}
        try:
            while child.poll() is None:
                try:
                    for proc in known[child.pid].children(recursive=True):
                        known.setdefault(proc.pid, proc)
                except psutil.NoSuchProcess:
                    pass
                rss = private = 0
                cpu = 0.0
                for pid, proc in list(known.items()):
                    try:
                        mem = proc.memory_info()
                        rss += mem.rss
                        private += getattr(mem, 'private', mem.rss)
                        times = proc.cpu_times()
                        cpu += times.user + times.system
                    except psutil.NoSuchProcess:
                        known.pop(pid, None)
                peak_rss, peak_private = max(peak_rss, rss), max(peak_private, private)
                cpu_seconds = max(cpu_seconds, cpu)
                if max(rss, private) >= cap_bytes:
                    termination = 'memory_cap'
                    break
                time.sleep(POLL_SECONDS)
        except KeyboardInterrupt:
            termination = 'interrupted'
        finally:
            if termination != 'exited':
                for proc in reversed(list(known.values())):
                    try:
                        proc.kill()
                    except psutil.NoSuchProcess:
                        pass
            exit_code = child.wait()
    result = dict(seconds=round(time.monotonic() - start, 3), cpu_seconds=round(cpu_seconds, 1),
                  peak_rss_gib=gib(peak_rss), peak_private_gib=gib(peak_private),
                  exit_code=exit_code, termination=termination)
    if termination == 'interrupted':
        raise Interrupted(result)
    return result


# --------------------------------------------------------------------------- the verifier

AXIOM_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOM_RE = re.compile(r"'([^']+)' does not depend on any axioms")

AUDIT_TEMPLATE = """\
import {module}

/-!
Generated by tools/verify_catalogue.py.  Independent audit of Atlas {atlas}:
the row theorem has exactly the catalogue statement, the metadata agrees with
it, and the axioms the theorem depends on are printed.
-/

open Taeyoung

example : {statement} {module}.graph := {module}.status
example : {module}.metadata.atlasId = {atlas} := rfl
example : {module}.metadata.status = .{status} := rfl
example : {module}.metadata.formalization = .verified := rfl

#print axioms {module}.status
"""


def parse_axioms(log: str, target: str) -> list[str] | None:
    """Axioms `#print axioms target` reported in `log`; None if it printed nothing."""
    axioms = None
    for m in AXIOM_RE.finditer(log):
        if m.group(1) == target:
            axioms = sorted(a.strip() for a in m.group(2).split(',') if a.strip())
    for m in NO_AXIOM_RE.finditer(log):
        if m.group(1) == target:
            axioms = []
    return axioms


def summarize_modules(records: list[dict]) -> dict:
    """Aggregate measurements of a list of per-module records."""
    return dict(
        compile_seconds=round(sum(r['seconds'] for r in records), 1),
        cpu_seconds=round(sum(r.get('cpu_seconds', 0) for r in records), 1),
        peak_private_gib=max((r['peak_private_gib'] for r in records), default=0.0),
        peak_rss_gib=max((r['peak_rss_gib'] for r in records), default=0.0),
        source_bytes=sum(r['source_bytes'] for r in records),
        source_lines=sum(r['source_lines'] for r in records),
        olean_bytes=sum(r['olean_bytes'] for r in records),
        slowest_module=max(({'module': r['module'], 'seconds': r['seconds']} for r in records),
                           key=lambda x: x['seconds'], default=None),
        most_memory_module=max(({'module': r['module'], 'peak_private_gib': r['peak_private_gib']}
                                for r in records), key=lambda x: x['peak_private_gib'], default=None),
    )


class Verifier:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.root = Path(__file__).resolve().parents[1]
        self.project = Project(self.root)
        self.cap_bytes = int(args.memory_gib * GIB)
        self.heap_mib = args.lean_heap_mib or int(args.memory_gib * 1024) - 2048
        self.require_free = int((args.require_free_gib if args.require_free_gib is not None else args.memory_gib) * GIB)
        if args.resume:
            self.out = Path(args.resume).resolve()
            if not (self.out / 'config.json').exists():
                raise SystemExit(f'error: {self.out} is not a verification run directory')
        else:
            stamp = dt.datetime.now().strftime('%Y%m%d-%H%M%S')
            self.out = Path(args.out).resolve() if args.out else self.root / 'verification_runs' / f'full-{stamp}'
        self.build = self.out / 'build'
        self.say = Console(None)
        self.fingerprints: dict[str, str] = {}
        self.module_results: dict[str, dict] = {}     # module -> measurement (this session or resumed)
        self.failed: dict[str, str] = {}              # module -> reason
        self.run_start = time.monotonic()

    # ----------------------------------------------------------------- setup

    def discover(self) -> tuple[list[Row], list[Row]]:
        """All rows, and the rows selected for this run (all unless --rows)."""
        files = sorted((self.root / self.project.lib / 'Examples').glob('Graph*.lean'))
        rows = [parse_row(self.project, f) for f in files]
        rows.sort(key=lambda r: r.atlas)
        for row in rows:
            row.closure = self.project.closure(row.module)
        selected = rows
        if self.args.rows:
            wanted = {int(x) for x in self.args.rows.split(',') if x.strip()}
            unknown = wanted - {r.atlas for r in rows}
            if unknown:
                raise SystemExit(f'error: no row file for Atlas {sorted(unknown)}')
            selected = [r for r in rows if r.atlas in wanted]
        return rows, selected

    def config_fingerprint(self) -> str:
        return sha256_bytes(json.dumps([self.lean_version, self.options, self.mathlib_rev]).encode())

    def fingerprint(self, name: str) -> str:
        if name not in self.fingerprints:
            module = self.project.modules[name]
            h = hashlib.sha256(self.config_fp.encode())
            h.update(module.source)
            for dep in sorted(module.imports):
                h.update(self.fingerprint(dep).encode())
            self.fingerprints[name] = h.hexdigest()
        return self.fingerprints[name]

    def paths_for(self, name: str) -> tuple[Path, Path]:
        base = self.build.joinpath(*name.split('.'))
        return base.with_suffix('.olean'), base.with_suffix('.ilean')

    def prepare(self) -> None:
        a = self.args
        lake = a.lake or shutil.which('lake')
        if not lake:
            raise SystemExit('error: `lake` not found; install elan or pass --lake')
        self.env_lake = lake_environment(lake, self.root)
        self.lean = self.env_lake.get('LEAN') or shutil.which('lean', path=self.env_lake.get('PATH'))
        if not self.lean:
            raise SystemExit('error: could not locate the `lean` executable of the toolchain')
        self.lean_version = subprocess.run([self.lean, '--version'], capture_output=True, text=True).stdout.strip()
        pinned = (self.root / 'lean-toolchain').read_text().strip()
        pinned_version = pinned.rsplit(':', 1)[-1].lstrip('v')
        if pinned_version not in self.lean_version:
            raise SystemExit(f'error: lean-toolchain pins {pinned} but `lean --version` is {self.lean_version}')
        self.dependency_path = dependency_search_path(self.env_lake, self.root)
        self.options = lean_options(self.root, self.project.lib)
        self.mathlib_rev = dependency_revision(self.env_lake)
        self.config_fp = self.config_fingerprint()
        total = psutil.virtual_memory().total
        if total < self.cap_bytes:
            raise SystemExit(f'error: the memory cap ({a.memory_gib} GiB) exceeds physical memory '
                             f'({gib(total)} GiB); lower --memory-gib')
        self.run_env = dict(os.environ)
        self.run_env.update({k: v for k, v in self.env_lake.items() if k in ('LEAN_SYSROOT', 'LEAN_SRC_PATH', 'PATH')})
        self.run_env['LEAN_PATH'] = os.pathsep.join([str(self.build)] + self.dependency_path)
        self.run_env['LEAN_NUM_THREADS'] = '1'

    def lock(self) -> None:
        lock = self.root / 'verification_runs' / '.verify_catalogue.lock'
        lock.parent.mkdir(parents=True, exist_ok=True)
        if lock.exists():
            try:
                pid = int(lock.read_text().split()[0])
            except (ValueError, IndexError):
                pid = -1
            if pid > 0 and psutil.pid_exists(pid) and pid != os.getpid():
                raise SystemExit(f'error: another verification (pid {pid}) is running; '
                                 f'only one may run at a time ({lock})')
        lock.write_text(f'{os.getpid()} {now_iso()} {self.out}\n')
        self.lock_path = lock

    def unlock(self) -> None:
        try:
            if self.lock_path.read_text().split()[0] == str(os.getpid()):
                self.lock_path.unlink()
        except (OSError, AttributeError, IndexError):
            pass

    # ----------------------------------------------------------------- compilation

    def wait_for_memory(self) -> None:
        announced = False
        while psutil.virtual_memory().available < self.require_free:
            if not announced:
                self.say(f'  waiting: {gib(psutil.virtual_memory().available)} GiB available, '
                         f'{gib(self.require_free)} GiB required before starting the next Lean process')
                announced = True
            time.sleep(FREE_MEMORY_WAIT_SECONDS)

    def compile_module(self, name: str, unit: str) -> dict:
        module = self.project.modules[name]
        olean, ilean = self.paths_for(name)
        olean.parent.mkdir(parents=True, exist_ok=True)
        for stale in (olean, ilean):          # never let an old artifact stand in for this compile
            stale.unlink(missing_ok=True)
        rel = module.path.relative_to(self.root).as_posix()
        command = [self.lean, '-R', str(self.root), '-M', str(self.heap_mib), '-j', '1',
                   *self.options, '-o', str(olean), '-i', str(ilean), rel]
        self.wait_for_memory()
        available = gib(psutil.virtual_memory().available)
        result = run_bounded(command, self.root, self.run_env, self.cap_bytes, self.out / 'logs' / f'{name}.log')
        ok = result['exit_code'] == 0 and result['termination'] == 'exited' and olean.exists()
        unchanged = sha256_bytes(module.path.read_bytes()) == sha256_bytes(module.source)
        record = dict(module=name, unit=unit, fingerprint=self.fingerprint(name), ok=ok and unchanged,
                      source_changed_during_run=not unchanged, **result,
                      available_gib_before=available, source_bytes=len(module.source),
                      source_lines=module.lines, olean_bytes=olean.stat().st_size if olean.exists() else 0,
                      direct_project_imports=len(module.imports), finished=now_iso())
        append_jsonl(self.out / 'modules.jsonl', record)
        return record

    def compile_list(self, modules: list[str], unit: str) -> list[dict]:
        """Compile `modules` in order; record failures; return this session's records."""
        records = []
        pending = [m for m in modules if m not in self.module_results]
        for k, name in enumerate(pending, 1):
            if name in self.failed:
                continue
            bad = [dep for dep in self.project.modules[name].imports if dep in self.failed]
            if bad:
                self.failed[name] = f'blocked: imports failed module {bad[0]}'
                self.say(f'  ({k}/{len(pending)}) {name}: BLOCKED by {bad[0]}')
                continue
            record = self.compile_module(name, unit)
            self.module_results[name] = record
            records.append(record)
            if not record['ok']:
                self.failed[name] = ('memory cap' if record['termination'] == 'memory_cap'
                                     else 'source changed during the run' if record['source_changed_during_run']
                                     else f'exit code {record["exit_code"]}')
            self.say(f'  ({k}/{len(pending)}) {name}: {record["seconds"]:.1f} s, '
                     f'{record["peak_private_gib"]:.2f} GiB, '
                     f'{"ok" if record["ok"] else "FAILED: " + self.failed[name]} '
                     f'| run {hms(time.monotonic() - self.run_start)}')
        return records

    def audit_row(self, row: Row) -> dict:
        audit_dir = self.out / 'audit'
        audit_dir.mkdir(parents=True, exist_ok=True)
        path = audit_dir / f'AuditGraph{row.atlas:03d}.lean'
        path.write_text(AUDIT_TEMPLATE.format(module=row.module, atlas=row.atlas,
                                              statement=row.statement, status=row.status), encoding='utf-8')
        command = [self.lean, '-M', str(self.heap_mib), '-j', '1', *self.options, str(path)]
        self.wait_for_memory()
        log_path = self.out / 'logs' / f'audit.Graph{row.atlas:03d}.log'
        result = run_bounded(command, audit_dir, self.run_env, self.cap_bytes, log_path)
        axioms = parse_axioms(log_path.read_text(encoding='utf-8', errors='replace'), f'{row.module}.status')
        compiled = result['exit_code'] == 0 and result['termination'] == 'exited'
        axioms_ok = axioms is not None and set(axioms) <= ALLOWED_AXIOMS
        return dict(**result, compiled=compiled, axioms=axioms, axioms_ok=axioms_ok, ok=compiled and axioms_ok)

    def negative_controls(self, row: Row) -> dict:
        """Show that the audit can fail: it must reject the opposite statement,
        and the axiom check must catch a proof that uses `sorry`."""
        audit_dir = self.out / 'audit'
        opposite = {'SatisfiesLowerBound': 'ViolatesLowerBound',
                    'ViolatesLowerBound': 'SatisfiesLowerBound'}[row.statement]
        wrong = audit_dir / 'ControlOppositeStatement.lean'
        wrong.write_text(AUDIT_TEMPLATE.format(module=row.module, atlas=row.atlas,
                                               statement=opposite, status=row.status), encoding='utf-8')
        r1 = run_bounded([self.lean, '-M', str(self.heap_mib), '-j', '1', *self.options, str(wrong)],
                         audit_dir, self.run_env, self.cap_bytes, self.out / 'logs' / 'control.opposite.log')
        sorry = audit_dir / 'ControlSorry.lean'
        sorry.write_text('theorem controlSorry : 1 + 1 = 3 := sorry\n\n#print axioms controlSorry\n', encoding='utf-8')
        log2 = self.out / 'logs' / 'control.sorry.log'
        r2 = run_bounded([self.lean, '-j', '1', str(sorry)], audit_dir, self.run_env, self.cap_bytes, log2)
        axioms = parse_axioms(log2.read_text(encoding='utf-8', errors='replace'), 'controlSorry')
        rejected = r1['exit_code'] != 0 and r1['termination'] == 'exited'
        caught = r2['exit_code'] == 0 and axioms is not None and not set(axioms) <= ALLOWED_AXIOMS
        result = dict(row=row.atlas, opposite_statement=opposite, opposite_statement_rejected=rejected,
                      sorry_axioms=axioms, sorry_caught=caught, ok=rejected and caught)
        self.say(f'[controls] opposite statement on {row.label} rejected: {rejected}; '
                 f'`sorry` caught by the axiom check ({axioms}): {caught}')
        return result

    # ----------------------------------------------------------------- units

    def verify_shared(self, index: int, total: int, unit: SharedUnit) -> dict:
        """Compile one shared unit completely, as its own measured item."""
        started, t0 = now_iso(), time.monotonic()
        machine = machine_snapshot()
        done_before = [m for m in unit.modules if m in self.module_results]
        self.say(f'[shared {index}/{total}] {unit.name}: {len(unit.modules)} modules, '
                 f'imported by {len(unit.users)} rows'
                 + (f', {len(done_before)} already compiled in an earlier session' if done_before else ''))
        records = self.compile_list(unit.modules, unit.name)
        measured = [self.module_results[m] for m in unit.modules if m in self.module_results]
        failed = {m: self.failed[m] for m in unit.modules if m in self.failed}
        record = dict(
            kind='shared', name=unit.name, result='verified' if not failed else 'failed',
            started=started, finished=now_iso(), wall_seconds=round(time.monotonic() - t0, 1),
            modules=len(unit.modules), modules_compiled_this_session=len(records),
            used_by_rows=sorted(unit.users), depends_on=unit.depends_on,
            **summarize_modules(measured), failed_modules=failed or None, machine_at_start=machine,
        )
        append_jsonl(self.out / 'shared.jsonl', record)
        self.say(f'  => {unit.name} {record["result"].upper()}: {hms(record["compile_seconds"])} compile, '
                 f'peak {record["peak_private_gib"]:.2f} GiB | run {hms(time.monotonic() - self.run_start)}')
        return record

    def verify_row(self, index: int, total: int, row: Row, own: list[str], shared_units: list[str],
                   previous_rows: dict) -> dict:
        """The row unit: modules only this row imports, then the audit."""
        say = self.say
        prior = previous_rows.get(row.atlas)
        if (prior and prior.get('result') == 'verified'
                and prior.get('closure_fingerprint') == self.closure_fingerprint(row)
                and all(m in self.module_results for m in row.closure)):
            say(f'[row {index}/{total}] {row.label}: verified in an earlier session of this run; skipped')
            return dict(prior, resumed=True)
        started, t0 = now_iso(), time.monotonic()
        machine = machine_snapshot()
        say(f'[row {index}/{total}] {row.label} ({row.status}): {len(own)} row module(s), '
            f'{len(row.closure) - len(own)} shared modules in {len(shared_units)} shared unit(s)')
        self.compile_list(own, row.label)
        blocked_by = {m: self.failed[m] for m in row.closure if m in self.failed}
        audit = None
        if not blocked_by:
            audit = self.audit_row(row)
            say(f'  audit: {audit["seconds"]:.1f} s, {audit["peak_private_gib"]:.2f} GiB, '
                f'axioms {audit["axioms"]}, {"ok" if audit["ok"] else "FAILED"}')
        own_failed = any(m in self.failed for m in own)
        if audit is not None:
            result = 'verified' if audit['ok'] else 'failed'
        else:
            result = 'failed' if own_failed else 'blocked'
        measured = [self.module_results[m] for m in own if m in self.module_results]
        agg = summarize_modules(measured)
        record = dict(
            kind='row', atlas=row.atlas, module=row.module, status=row.status, result=result,
            started=started, finished=now_iso(), wall_seconds=round(time.monotonic() - t0, 1),
            row_modules=len(own), closure_modules=len(row.closure), shared_units=shared_units,
            **agg,
            audit_seconds=audit['seconds'] if audit else None,
            audit_peak_private_gib=audit['peak_private_gib'] if audit else None,
            closure_source_bytes=sum(len(self.project.modules[m].source) for m in row.closure),
            closure_olean_bytes=sum(self.paths_for(m)[0].stat().st_size for m in row.closure
                                    if self.paths_for(m)[0].exists()),
            axioms=audit['axioms'] if audit else None,
            blocked_by=blocked_by or None, machine_at_start=machine,
            closure_fingerprint=self.closure_fingerprint(row),
        )
        if audit:
            record['peak_private_gib'] = max(record['peak_private_gib'], audit['peak_private_gib'])
            record['peak_rss_gib'] = max(record['peak_rss_gib'], audit['peak_rss_gib'])
        append_jsonl(self.out / 'rows.jsonl', record)
        say(f'  => {row.label} {result.upper()}: {hms(record["wall_seconds"])} '
            f'({record["compile_seconds"]:.0f} s compile, {record["audit_seconds"] or 0:.0f} s audit), '
            f'peak {record["peak_private_gib"]:.2f} GiB | run {hms(time.monotonic() - self.run_start)}')
        return record

    def closure_fingerprint(self, row: Row) -> str:
        h = hashlib.sha256()
        for m in row.closure:
            h.update(self.fingerprint(m).encode())
        h.update(AUDIT_TEMPLATE.encode())
        return h.hexdigest()

    def attribute_costs(self, rows: list[Row], records: list[dict], users: dict[str, set[int]]) -> None:
        """Row costs that include shared units, computed once everything is measured.

        * standalone: verifying the row alone from scratch — every module of its
          closure (its own and all shared ones) plus its audit; sum of times,
          largest peak;
        * amortized: its own modules and audit, plus each shared module's time
          divided equally among the rows importing it.  Summed over all rows
          this is the total compile time of the catalogue.
        """
        for row, rec in zip(rows, records):
            measured = [self.module_results.get(m) for m in row.closure]
            if rec.get('audit_seconds') is None or not all(measured):
                rec.update(standalone_seconds=None, standalone_peak_private_gib=None, amortized_seconds=None)
                continue
            audit = rec['audit_seconds']
            rec['standalone_seconds'] = round(sum(x['seconds'] for x in measured) + audit, 1)
            rec['standalone_peak_private_gib'] = max([x['peak_private_gib'] for x in measured]
                                                     + [rec['audit_peak_private_gib']])
            rec['amortized_seconds'] = round(sum(x['seconds'] / len(users[m])
                                                 for m, x in zip(row.closure, measured)) + audit, 1)

    # ----------------------------------------------------------------- catalogue counts

    def verify_counts(self) -> dict:
        name = f'{self.project.lib}.Catalogue.Counts'
        closure = self.project.closure(name)
        if any(m in self.failed for m in closure):
            return dict(kind='catalogue', result='blocked', blocked_by=[m for m in closure if m in self.failed])
        pending = [m for m in closure if m not in self.module_results]
        self.say(f'[catalogue] {name}: {len(pending)} module(s) to compile '
                 f'(everything else was compiled for the rows and shared units)')
        t0 = time.monotonic()
        machine = machine_snapshot()
        records = self.compile_list(closure, 'catalogue counts')
        ok = not any(m in self.failed for m in closure)
        return dict(kind='catalogue', name=name, result='verified' if ok else 'failed',
                    wall_seconds=round(time.monotonic() - t0, 1), modules=len(records),
                    **summarize_modules(records), machine_at_start=machine,
                    checked='row count 117; positive, negative, open and verified counts '
                            '(Taeyoung/Catalogue/Counts.lean)')

    # ----------------------------------------------------------------- driver

    def schedule(self, rows: list[Row], units: list[SharedUnit], unit_of: dict[str, str]):
        """Interleave shared units and rows: before each row, the shared units it
        needs that have not been scheduled yet, in dependency order."""
        by_name = {u.name: u for u in units}
        position = {u.name: i for i, u in enumerate(units)}
        scheduled: set[str] = set()
        steps = []
        for row in rows:
            needed = sorted({unit_of[m] for m in row.closure if m in unit_of}, key=position.get)
            for name in needed:
                if name not in scheduled:
                    scheduled.add(name)
                    steps.append(('shared', by_name[name]))
            own = [m for m in row.closure if m not in unit_of]
            steps.append(('row', (row, own, needed)))
        return steps

    def print_plan(self, steps, units: list[SharedUnit], longest: int) -> None:
        say = self.say
        n_shared = sum(1 for kind, _ in steps if kind == 'shared')
        n_rows = sum(1 for kind, _ in steps if kind == 'row')
        modules = {m for kind, x in steps for m in (x.modules if kind == 'shared' else x[1])}
        mib = sum(len(self.project.modules[m].source) for m in modules) / 2**20
        say(f'Plan: {n_shared} shared units and {n_rows} row units; {len(modules)} project modules '
            f'({mib:.1f} MiB of source) compiled from source, one process at a time.')
        for kind, x in steps:
            if kind == 'shared':
                src = sum(len(self.project.modules[m].source) for m in x.modules) / 2**20
                say(f'  shared  {x.name:32s} {len(x.modules):5d} modules  {src:7.2f} MiB  '
                    f'imported by {len(x.users):3d} rows')
            else:
                row, own, needed = x
                src = sum(len(self.project.modules[m].source) for m in own) / 2**20
                say(f'  row     {row.label:32s} {len(own):5d} modules  {src:7.2f} MiB  '
                    f'+ audit; uses {len(needed)} shared units')
        say(f'Longest build path would be {longest} characters.')

    def run(self) -> int:
        a = self.args
        all_rows, rows = self.discover()
        units_all, users, unit_of = build_units(self.project, all_rows)
        steps = self.schedule(rows, units_all, unit_of)
        all_modules = sorted({m for r in rows for m in r.closure})
        longest = max(len(str(self.paths_for(m)[1])) for m in all_modules)
        if a.plan:
            self.print_plan(steps, units_all, longest)
            return 0

        self.prepare()
        self.out.mkdir(parents=True, exist_ok=True)
        self.say = Console(self.out / 'progress.log')
        say = self.say
        self.lock()
        try:
            config = dict(
                started=now_iso(), resumed=bool(a.resume), run_directory=str(self.out),
                project=str(self.root), git=git_state(self.root.parent),
                lean_version=self.lean_version, lean_executable=self.lean, mathlib_revision=self.mathlib_rev,
                dependency_search_path=self.dependency_path, lean_options=self.options,
                memory_cap_gib=a.memory_gib, lean_heap_mib=self.heap_mib, require_free_gib=gib(self.require_free),
                threads_per_process=1, concurrent_processes=1,
                rows=[r.atlas for r in rows],
                shared_units={u.name: dict(modules=len(u.modules), used_by_rows=sorted(u.users),
                                           depends_on=u.depends_on) for u in units_all},
                python=sys.version.split()[0],
                machine=dict(platform=platform.platform(), processor=platform.processor(),
                             logical_cpus=psutil.cpu_count(), physical_cpus=psutil.cpu_count(logical=False),
                             total_memory_gib=gib(psutil.virtual_memory().total)),
            )
            if not a.resume:
                write_json(self.out / 'config.json', config)
            else:
                append_jsonl(self.out / 'sessions.jsonl', config)
            n_shared = sum(1 for kind, _ in steps if kind == 'shared')
            say(f'Verification run: {self.out}')
            say(f'  {self.lean_version}; Mathlib {self.mathlib_rev}; cap {a.memory_gib} GiB '
                f'(Lean heap {self.heap_mib} MiB); one process at a time; '
                f'{n_shared} shared units + {len(rows)} rows; {len(all_modules)} project modules from source')
            if longest > MAX_PATH_WARNING:
                say(f'  warning: build paths reach {longest} characters; on Windows without long-path support '
                    f'choose a shorter --out')
            others = other_lean_processes({os.getpid()})
            if others['count']:
                say(f'  note: {others["count"]} other lean process(es) running ({others["rss_gib"]} GiB), '
                    f'e.g. an editor; they are left alone but count against free memory')

            static = None if a.skip_static_checks else static_checks(
                all_rows, self.root.parent / 'GRAPH_CLASSIFICATION_UP_TO_6_VERTICES.md', say)
            scan = source_scan(self.project, all_modules)

            previous_rows: dict[int, dict] = {}
            if a.resume:
                for rec in read_jsonl(self.out / 'modules.jsonl'):
                    olean = self.paths_for(rec['module'])[0]
                    if (rec['ok'] and rec['module'] in self.project.modules
                            and rec['fingerprint'] == self.fingerprint(rec['module']) and olean.exists()):
                        self.module_results[rec['module']] = dict(rec, resumed=True)
                for rec in read_jsonl(self.out / 'rows.jsonl'):
                    previous_rows[rec['atlas']] = rec
                say(f'  resuming: {len(self.module_results)} compiled modules reused from earlier sessions of this run')

            shared_records, row_records = [], []
            controls = None
            k_shared = k_row = 0
            for kind, x in steps:
                if kind == 'shared':
                    k_shared += 1
                    shared_records.append(self.verify_shared(k_shared, n_shared, x))
                else:
                    k_row += 1
                    row, own, needed = x
                    record = self.verify_row(k_row, len(rows), row, own, needed, previous_rows)
                    row_records.append(record)
                    if controls is None and record['result'] == 'verified':
                        controls = self.negative_controls(row)

            counts = None
            if not a.skip_counts and not a.rows:
                counts = self.verify_counts()
                say(f'[catalogue] kernel-checked counts: {counts["result"]}')

            self.attribute_costs(rows, row_records, users)
            write_json(self.out / 'units.json', dict(shared=shared_records, rows=row_records, catalogue=counts))
            verified = [r for r in row_records if r['result'] == 'verified']
            summary = dict(
                finished=now_iso(), run_directory=str(self.out),
                rows_total=len(rows), rows_verified=len(verified),
                rows_failed=[r['atlas'] for r in row_records if r['result'] == 'failed'],
                rows_blocked=[r['atlas'] for r in row_records if r['result'] == 'blocked'],
                shared_units_total=len(shared_records),
                shared_units_failed=[s['name'] for s in shared_records if s['result'] != 'verified'],
                static_checks=static, negative_controls=controls, catalogue_counts=counts, source_scan=scan,
                modules_compiled_this_session=sum(1 for r in self.module_results.values() if not r.get('resumed')),
                failed_modules=self.failed,
                total_compile_seconds=round(sum(r['seconds'] for r in self.module_results.values()), 1),
                total_audit_seconds=round(sum(r['audit_seconds'] or 0 for r in row_records), 1),
                peak_private_gib=max([r['peak_private_gib'] for r in row_records]
                                     + [s['peak_private_gib'] for s in shared_records], default=0),
                wall_seconds_this_session=round(time.monotonic() - self.run_start, 1),
            )
            success = (len(verified) == len(rows) and (static is None or static['ok'])
                       and controls is not None and controls['ok']
                       and (counts is None or counts['result'] == 'verified'))
            summary['success'] = success
            write_json(self.out / 'summary.json', summary)
            write_report(self.out, config, summary, shared_records, row_records)
            say()
            say(f'{"SUCCESS" if success else "NOT VERIFIED"}: {len(verified)}/{len(rows)} rows verified; '
                f'report {self.out / "REPORT.md"}')
            return 0 if success else 1
        except (Interrupted, KeyboardInterrupt):
            say('\nInterrupted; the current Lean process was stopped. Resume with:')
            say(f'  python tools/verify_catalogue.py --resume "{self.out}"')
            return 130
        finally:
            self.unlock()


# --------------------------------------------------------------------------- report

def write_report(out: Path, config: dict, summary: dict, shared: list[dict], rows: list[dict]) -> None:
    lines = [
        '# Catalogue verification report', '',
        f'- Run directory: `{out}`',
        f'- Started: {config["started"]}; finished: {summary["finished"]}',
        f'- Git commit: `{config["git"]["commit"]}` '
        f'({config["git"]["modified_or_untracked_paths"]} modified or untracked paths under the project)',
        f'- Toolchain: {config["lean_version"]}; Mathlib `{config["mathlib_revision"]}` (prebuilt, trusted)',
        f'- Machine: {config["machine"]["platform"]}, {config["machine"]["logical_cpus"]} logical CPUs, '
        f'{config["machine"]["total_memory_gib"]} GiB RAM',
        f'- Limits: {config["memory_cap_gib"]} GiB process-tree cap, Lean heap {config["lean_heap_mib"]} MiB, '
        f'one Lean process at a time with one thread',
        f'- Allowed axioms: {", ".join(sorted(ALLOWED_AXIOMS))}',
        '',
        f'**Result: {"SUCCESS" if summary["success"] else "NOT VERIFIED"}** — '
        f'{summary["rows_verified"]}/{summary["rows_total"]} rows verified; '
        f'{summary["shared_units_total"] - len(summary["shared_units_failed"])}/{summary["shared_units_total"]} '
        f'shared units compiled.',
        f'Total compile time {hms(summary["total_compile_seconds"])}, audits {hms(summary["total_audit_seconds"])}; '
        f'largest peak {summary["peak_private_gib"]:.2f} GiB.',
        '',
    ]
    if summary['static_checks']:
        s = summary['static_checks']
        lines.append(f'Static checks: {"passed" if s["ok"] else "FAILED"} '
                     f'({s["counts"]["positive"]} positive, {s["counts"]["negative"]} negative; markdown {s["markdown"]}).')
        lines += [f'- {p}' for p in s['problems']]
    c = summary['negative_controls']
    if c:
        lines.append(f'Negative controls ({"passed" if c["ok"] else "FAILED"}): the audit of Atlas {c["row"]} against '
                     f'the opposite statement `{c["opposite_statement"]}` was '
                     f'{"rejected" if c["opposite_statement_rejected"] else "NOT rejected"}; a proof by `sorry` '
                     f'reported axioms {c["sorry_axioms"]} and was {"caught" if c["sorry_caught"] else "NOT caught"}.')
    else:
        lines.append('Negative controls: not run (no row was verified).')
    if summary['catalogue_counts']:
        lines.append(f'Kernel-checked catalogue counts: {summary["catalogue_counts"]["result"]}.')
    if summary['failed_modules']:
        lines += ['', 'Failed or blocked modules:', ''] + [f'- `{m}`: {r}' for m, r in summary['failed_modules'].items()]

    def mod_name(entry):
        return entry['module'].rsplit('.', 1)[-1] if entry else '—'

    lines += ['', '## Shared units', '',
              'Libraries imported by more than one row, each compiled completely as its own unit, '
              'just before the first row that needs it.', '',
              '| unit | result | modules | used by rows | compile time | peak GiB | source MiB | slowest module |',
              '|---|---|---:|---:|---:|---:|---:|---|']
    for s in shared:
        slow = s.get('slowest_module')
        lines.append(f'| {s["name"]} | {s["result"]} | {s["modules"]} | {len(s["used_by_rows"])} | '
                     f'{hms(s["compile_seconds"])} | {s["peak_private_gib"]:.2f} | {s["source_bytes"] / 2**20:.2f} | '
                     f'{mod_name(slow)} {slow["seconds"] if slow else 0:.0f}s |')
    lines += ['', '## Rows', '',
              'Each row unit compiles only the modules no other row imports, then runs the audit. Two further '
              'views include the shared units:', '',
              '- **standalone**: verifying the row alone from scratch — every module of its import closure plus '
              'its audit (sum of times; largest peak).',
              '- **amortized**: the row unit plus each shared module\'s time divided equally among the rows '
              'importing it. These sum to the total compile time.', '',
              '| Atlas | status | result | row unit | row modules | audit | peak GiB | standalone | '
              'standalone peak GiB | amortized | closure modules | shared units | axioms |',
              '|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|']
    for r in rows:
        alone = r.get('standalone_peak_private_gib')
        lines.append(
            f'| {r["atlas"]} | {r["status"]} | {r["result"]} | {hms(r["wall_seconds"])} | {r["row_modules"]} | '
            f'{hms(r["audit_seconds"])} | {r["peak_private_gib"]:.2f} | {hms(r.get("standalone_seconds"))} | '
            f'{f"{alone:.2f}" if alone is not None else "—"} | {hms(r.get("amortized_seconds"))} | '
            f'{r["closure_modules"]} | {len(r["shared_units"])} | '
            f'{", ".join(r["axioms"]) if r["axioms"] is not None else "—"} |')
    lines += ['', '## Source scan (informational)', '',
              'Occurrences anywhere in the compiled sources, comments included. The axiom audit is decisive.', '']
    for key, value in summary['source_scan'].items():
        lines.append(f'- {key}: {value["count"]} module(s)')
    lines += ['', 'Measurements: `units.json` (shared units, rows, catalogue), `modules.jsonl` (every module), '
              '`shared.jsonl` and `rows.jsonl` (as they finished). Compiler output: `logs/`. Audit files: `audit/`.']
    (out / 'REPORT.md').write_text('\n'.join(lines) + '\n', encoding='utf-8')


# --------------------------------------------------------------------------- CLI

def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    parser = argparse.ArgumentParser(
        description='Rebuild every project module from source (Mathlib excepted) and verify the '
                    '117-row catalogue unit by unit, sequentially, under a memory cap.')
    parser.add_argument('--memory-gib', type=float, default=32,
                        help='process-tree memory cap for each Lean process (default 32)')
    parser.add_argument('--lean-heap-mib', type=int, default=None,
                        help="Lean's own -M heap limit (default: cap minus 2 GiB)")
    parser.add_argument('--require-free-gib', type=float, default=None,
                        help='wait before each Lean process until this much memory is available (default: the cap)')
    parser.add_argument('--out', help='run directory (default verification_runs/full-<timestamp>)')
    parser.add_argument('--resume', metavar='RUN_DIR', help='continue an interrupted run in RUN_DIR')
    parser.add_argument('--rows', help='comma-separated Atlas ids to verify (default: all rows)')
    parser.add_argument('--lake', help='path to the lake executable (default: from PATH)')
    parser.add_argument('--plan', action='store_true', help='print the units and exit without compiling')
    parser.add_argument('--skip-static-checks', action='store_true', help='skip the Python graph and scope checks')
    parser.add_argument('--skip-counts', action='store_true', help='skip Taeyoung.Catalogue.Counts')
    args = parser.parse_args(argv)
    if args.out and args.resume:
        parser.error('--out and --resume are mutually exclusive')
    return Verifier(args).run()


if __name__ == '__main__':
    sys.exit(main())
