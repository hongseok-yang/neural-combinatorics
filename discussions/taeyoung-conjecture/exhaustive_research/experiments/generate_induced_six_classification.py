"""Generate compact, reusable kernel checks for labelled six-vertex graphs."""

import json
from pathlib import Path

import generate_compact_s4_group_totals as shared
from generate_compact_s4_psd import table


NS = 'Taeyoung.Methods.RootedSOS.Induced.Six'
ROOT = Path('lean/Taeyoung/Methods/RootedSOS/Induced/Six')


def write(name, text):
    (ROOT/f'{name}.lean').write_text(text, encoding='utf-8')


def main():
    data = json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    ROOT.mkdir(parents=True, exist_ok=True)
    shared.NS, shared.ROOT = NS, ROOT
    vertices = [sum(v*6**i for i, v in enumerate(p)) for p in data['permutations']]
    edge_maps = [sum(v*15**i for i, v in enumerate(p)) for p in data['edge_permutations']]
    class_codes = [j+156*p for j,p in data['classification']]
    tables = [('vertexData', vertices), ('edgeData', edge_maps),
              ('inverseData', data['inverse_indices']), ('hostData', data['host_codes'])]
    defs = '\n'.join(f'private def {name} : PackedTable := {table(values)}' for name,values in tables)
    parts = []
    for start in range(0, len(class_codes), 512):
        name = f'classificationPart{start:05d}'
        defs += f'\nprivate def {name} : PackedTable := {table(class_codes[start:start+512])}'
        parts.append(name)
    def tree(names):
        if len(names) == 1:
            return names[0]
        mid = len(names)//2
        return f'(.node {mid*512} {tree(names[:mid])} {tree(names[mid:])})'
    defs += f'\nprivate def classificationData : PackedTable := {tree(parts)}'
    pairs = ', '.join(f'({i},{j})' for i,j in data['pairs'])
    write('Data', f'''import Taeyoung.Methods.RootedSOS.PackedMatrix
namespace {NS}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
{defs}
def pairs : Fin 15 → Fin 6 × Fin 6 := ![{pairs}]
def inverse (p : Fin 720) : Fin 720 := ⟨(inverseData.get p).toNat % 720, Nat.mod_lt _ (by decide)⟩
def vertex (p : Fin 720) (i : Fin 6) : Fin 6 :=
  ⟨(vertexData.get p).toNat / 6^i.1 % 6, Nat.mod_lt _ (by decide)⟩
def edge (p : Fin 720) (i : Fin 15) : Fin 15 :=
  ⟨(edgeData.get p).toNat / 15^i.1 % 15, Nat.mod_lt _ (by decide)⟩
def hostCode (j : Fin 156) : Fin 32768 :=
  ⟨(hostData.get j).toNat % 32768, Nat.mod_lt _ (by decide)⟩
def host (code : Fin 32768) : Fin 156 :=
  ⟨(classificationData.get code).toNat % 156, Nat.mod_lt _ (by decide)⟩
def permutation (code : Fin 32768) : Fin 720 :=
  ⟨(classificationData.get code).toNat / 156 % 720, Nat.mod_lt _ (by decide)⟩
end {NS}
''')
    write('Base', f'''import {NS}.Data
import Taeyoung.Methods.RootedSOS.Induced.Relabeling
namespace {NS}
def bits (code : Fin 32768) : Fin 15 → Fin 2 := finFunctionFinEquiv.symm code
def permutationCheck (p : Fin 720) : Prop :=
  (∀ i : Fin 6, vertex (inverse p) (vertex p i) = i ∧ vertex p (vertex (inverse p) i) = i) ∧
  (∀ i : Fin 15, edge (inverse p) (edge p i) = i ∧ edge p (edge (inverse p) i) = i) ∧
  (∀ i : Fin 15,
    (vertex p (pairs i).1 = (pairs (edge p i)).1 ∧ vertex p (pairs i).2 = (pairs (edge p i)).2) ∨
    (vertex p (pairs i).1 = (pairs (edge p i)).2 ∧ vertex p (pairs i).2 = (pairs (edge p i)).1))
instance (p : Fin 720) : Decidable (permutationCheck p) := by unfold permutationCheck; infer_instance
def classificationCheck (code : Fin 32768) : Prop :=
  ∀ i : Fin 15, bits code i = bits (hostCode (host code)) (edge (permutation code) i)
instance (code : Fin 32768) : Decidable (classificationCheck code) := by
  unfold classificationCheck; infer_instance
end {NS}
''')
    imports, theorem = shared.chunks('PermutationChecks', 'Base', 'permutationCheck', 720, 240, 8)
    write('Permutations', f'''{imports}
namespace {NS}
{theorem}
def vertexEquiv (p : Fin 720) : Fin 6 ≃ Fin 6 where
  toFun := vertex p
  invFun := vertex (inverse p)
  left_inv i := ((permutationCheck_all p).1 i).1
  right_inv i := ((permutationCheck_all p).1 i).2
def edgeEquiv (p : Fin 720) : Fin 15 ≃ Fin 15 where
  toFun := edge p
  invFun := edge (inverse p)
  left_inv i := ((permutationCheck_all p).2.1 i).1
  right_inv i := ((permutationCheck_all p).2.1 i).2
end {NS}
''')
    imports, theorem = shared.chunks('ClassificationChecks', 'Base', 'classificationCheck', 32768, 512, 8)
    write('Classification', f'''{imports}
import {NS}.Permutations
namespace {NS}
{theorem}
open MeasureTheory
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]
noncomputable def density (j : Fin 156) (W : Taeyoung.Graphon Ω μ) : Real :=
  inducedDensity pairs (bits (hostCode j)) W
theorem density_nonneg (j : Fin 156) (W : Taeyoung.Graphon Ω μ) : 0 ≤ density j W :=
  inducedDensity_nonneg _ _ W
theorem inducedDensity_classification (code : Fin 32768) (W : Taeyoung.Graphon Ω μ) :
    inducedDensity pairs (bits code) W = density (host code) W :=
  inducedDensity_relabel pairs pairs (bits code) (bits (hostCode (host code)))
    (vertexEquiv (permutation code)) (edgeEquiv (permutation code))
    (classificationCheck_all code) (permutationCheck_all (permutation code)).2.2 W
end {NS}
''')
    print(f'Generated {len(list(ROOT.glob("*.lean")))} shared classification files', flush=True)


if __name__ == '__main__':
    main()
