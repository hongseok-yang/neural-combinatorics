#!/usr/bin/env python3
"""Generate the M0 kernel micro-benchmarks (plan §4 M0) from the exported certificate data.

Usage (from the directory even_cycle_apex_commonality):
    python tools/gen_bench.py certificates lean/Bench

Writes (plan encodings, as specified in plan §4 M0)
  BenchA.lean         one 15x15 rational FactorOK (positive_majority block 16, the largest LDL numbers)
  BenchB.lean         all 32,768 relabelling witnesses, 32 chunks of 1024, one conjoined theorem
  BenchC_forced.lean  the naive rooted expansion of the eleven r = 4 blocks of mean_three:
                      158,400 signed monomials accumulated in a binary trie keyed by the 15-bit mask
and, with a third argument, the redesigned encodings of DEVIATIONS X3:
  b2 -> BenchB2.lean  the same witnesses with direct Nat primitives, one theorem per chunk
  c2 -> BenchC2.lean  the r = 4 group merged per (a, b, T): 14,400 updates of a packed accumulator
The benchmark files are self-contained (they import only `Init`) and are not part of the library.
"""
import json
import sys
from pathlib import Path

EDGES = [(i, j) for i in range(6) for j in range(i + 1, 6)]
INDEX = {e: k for k, e in enumerate(EDGES)}


def lean_int(x):
    return str(x) if x >= 0 else f'({x})'


def chunks(xs, n):
    return [xs[i:i + n] for i in range(0, len(xs), n)]


def header(doc):
    return f'/-! {doc} -/\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace EvenCycleApex.Bench\n\n'


def bench_a(cert, out):
    name, j = 'positive_majority', 16
    A = json.loads((cert / f'{name}_sos.json').read_text())['matrices'][j]
    f = json.loads((cert / 'lean-data' / 'ldl_witnesses.json').read_text())
    f = f['factorizations_of_integer_numerators'][name][j]
    n = len(A)
    s = header(f'M0 benchmark (a): one 15x15 rational `FactorOK` ({name}, block {j}) by `decide +kernel`.')
    s += 'def A : List (List Int) :=\n  [' + ',\n   '.join('[' + ', '.join(lean_int(int(x)) for x in row) + ']' for row in A) + ']\n\n'
    s += 'def L : List (List (Int × Nat)) :=\n  [' + ',\n   '.join(
        '[' + ', '.join(f'({lean_int(int(a))}, {b})' for a, b in row) + ']' for row in f['lower']) + ']\n\n'
    s += 'def D : List (Int × Nat) :=\n  [' + ', '.join(f'({lean_int(int(a))}, {b})' for a, b in f['diagonal']) + ']\n\n'
    s += '''def q (p : Int × Nat) : Rat := mkRat p.1 p.2

def dot3 : List Rat → List Rat → List Rat → Rat
  | a :: as, d :: ds, b :: bs => a * d * b + dot3 as ds bs
  | _, _, _ => 0

/-- Row `i` of `A` against every row `j` of `L`: `A i j = ∑ₕ L i h * δ h * L j h`. -/
def rowOK (Li δ : List Rat) : List Int → List (List Rat) → Bool
  | a :: as, Lj :: Ls => (dot3 Li δ Lj == (a : Rat)) && rowOK Li δ as Ls
  | [], [] => true
  | _, _ => false

def allOK (δ : List Rat) (Lall : List (List Rat)) : List (List Int) → List (List Rat) → Bool
  | Ai :: As, Li :: Ls => rowOK Li δ Ai Lall && allOK δ Lall As Ls
  | [], [] => true
  | _, _ => false

/-- `L i i = 1` and `L i j = 0` for `j > i`. -/
def unitLowerRow (i : Nat) : Nat → List Rat → Bool
  | _, [] => true
  | j, x :: xs => (if j = i then x == 1 else if i < j then x == 0 else true) && unitLowerRow i (j + 1) xs

def unitLower : Nat → List (List Rat) → Bool
  | _, [] => true
  | i, r :: rs => unitLowerRow i 0 r && unitLower (i + 1) rs

def factorOK : Bool :=
  let Lq := L.map (fun r => r.map q)
  let δ := D.map q
  unitLower 0 Lq && δ.all (fun d => decide (0 < d)) && allOK δ Lq A Lq

set_option profiler true in
theorem factorOK_true : factorOK = true := by decide +kernel

end EvenCycleApex.Bench
'''
    (out / 'BenchA.lean').write_text(s, encoding='utf-8')


RELABEL_CORE = '''/-- First and second endpoint of edge `b` (lexicographic order of the 15 pairs of `Fin 6`),
packed in 3-bit fields. -/
def edgeFstPacked : Nat := EDGE_FST
def edgeSndPacked : Nat := EDGE_SND
def edgeFst (b : Nat) : Nat := (edgeFstPacked >>> (3 * b)) % 8
def edgeSnd (b : Nat) : Nat := (edgeSndPacked >>> (3 * b)) % 8

/-- Position of the pair `{i, j}`, `i < j`: `i (11 - i) / 2 + (j - i - 1)`. -/
def pairIdx (i j : Nat) : Nat :=
  if i < j then i * (11 - i) / 2 + (j - i - 1) else j * (11 - j) / 2 + (i - j - 1)

/-- Digit `i` of a base-6 permutation code. -/
def permAt (code i : Nat) : Nat := code / 6 ^ i % 6

def relabelGo (g code : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => relabelGo g code b |||
      (if g.testBit b then 1 <<< pairIdx (permAt code (edgeFst b)) (permAt code (edgeSnd b)) else 0)

def relabel (g code : Nat) : Nat := relabelGo g code 15
'''


def relabel_consts():
    fst = sum(i << (3 * b) for b, (i, j) in enumerate(EDGES))
    snd = sum(j << (3 * b) for b, (i, j) in enumerate(EDGES))
    return RELABEL_CORE.replace('EDGE_FST', str(fst)).replace('EDGE_SND', str(snd))


def bench_b(cert, out):
    w = json.loads((cert / 'lean-data' / 'normalization_witnesses.json').read_text())
    nf, perms = w['normal_form'], w['permutation']
    codes = [sum(p[i] * 6 ** i for i in range(6)) for p in perms]
    packed = [nf[g] + (codes[g] << 15) for g in range(1 << 15)]
    s = header('M0 benchmark (b): 32,768 relabelling witnesses `π_g · g = ν(g)`, chunked by 1024.\n'
               'Entry `g` is `ν(g) + 2^15 * code(π_g)`, the permutation in base 6.')
    s += relabel_consts()
    s += '''
/-- The six digits of `code` are pairwise distinct (so `permAt code` is a permutation of `Fin 6`). -/
def isPerm (code : Nat) : Bool :=
  code < 6 ^ 6 &&
  (List.range 6).all fun i => (List.range 6).all fun j => i == j || permAt code i != permAt code j

def checkOne (g e : Nat) : Bool :=
  isPerm (e >>> 15) && relabel g (e >>> 15) == e % 32768

def checkChunk : Nat → List Nat → Bool
  | _, [] => true
  | g, e :: es => checkOne g e && checkChunk (g + 1) es

'''
    for c, ch in enumerate(chunks(packed, 1024)):
        s += f'def chunk{c} : List Nat := [' + ', '.join(map(str, ch)) + ']\n'
    s += '\nset_option profiler true in\ntheorem chunk0_ok : checkChunk 0 chunk0 = true := by decide +kernel\n\n'
    s += 'set_option profiler true in\ntheorem all_ok : ' + ' && '.join(
        f'checkChunk {1024 * c} chunk{c}' for c in range(32)) + ' = true := by decide +kernel\n\nend EvenCycleApex.Bench\n'
    (out / 'BenchB.lean').write_text(s, encoding='utf-8')


def bench_c(cert, out, forced):
    mats = json.loads((cert / 'mean_three_sos.json').read_text())['matrices']
    types = [0, 1, 3, 7, 11, 12, 13, 15, 30, 31, 63]
    r4 = mats[8:19]
    assert all(len(A) == 15 for A in r4)
    roots = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    fa = [sum(1 << INDEX[(i, 4)] for i in range(4) if (bits >> i) & 1) for bits in range(1, 16)]
    fb = [sum(1 << INDEX[(i, 5)] for i in range(4) if (bits >> i) & 1) for bits in range(1, 16)]
    tm = [sum(1 << INDEX[roots[e]] for e in range(6) if (T >> e) & 1) for T in range(64)]
    signs = [[(bin(T & ~t).count('1') % 2 == 0) for T in range(64)] for t in types]
    tag = 'forced' if forced else 'lazy'
    s = header(f'M0 benchmark (c, {tag}): naive rooted expansion of the eleven r = 4 blocks of `mean_three`,\n'
               '158,400 signed monomials `[T ∪ F_a ∪ F_b\']` accumulated in a binary trie keyed by the 15-bit mask.')
    s += 'inductive Trie where\n  | leaf (c : Int)\n  | node (l r : Trie)\n\n'
    if forced:
        s += '''/-- Insertion; the rebuilt path is forced by matching on the recursive result, and the new leaf
value by an equality test, so that no unevaluated insertion chain survives between steps. -/
def Trie.add : Nat → Nat → Int → Trie → Trie
  | 0, _, c, .leaf v => let w := v + c; if w = 0 then .leaf 0 else .leaf w
  | 0, _, c, .node _ _ => .leaf c
  | d + 1, k, c, .leaf _ =>
      if k % 2 = 0 then
        match Trie.add d (k / 2) c (.leaf 0) with
        | .leaf v => .node (.leaf v) (.leaf 0)
        | .node a b => .node (.node a b) (.leaf 0)
      else
        match Trie.add d (k / 2) c (.leaf 0) with
        | .leaf v => .node (.leaf 0) (.leaf v)
        | .node a b => .node (.leaf 0) (.node a b)
  | d + 1, k, c, .node l r =>
      if k % 2 = 0 then
        match Trie.add d (k / 2) c l with
        | .leaf v => .node (.leaf v) r
        | .node a b => .node (.node a b) r
      else
        match Trie.add d (k / 2) c r with
        | .leaf v => .node l (.leaf v)
        | .node a b => .node l (.node a b)
'''
    else:
        s += '''def Trie.add : Nat → Nat → Int → Trie → Trie
  | 0, _, c, .leaf v => .leaf (v + c)
  | 0, _, c, .node _ _ => .leaf c
  | d + 1, k, c, .leaf _ =>
      if k % 2 = 0 then .node (Trie.add d (k / 2) c (.leaf 0)) (.leaf 0)
      else .node (.leaf 0) (Trie.add d (k / 2) c (.leaf 0))
  | d + 1, k, c, .node l r =>
      if k % 2 = 0 then .node (Trie.add d (k / 2) c l) r else .node l (Trie.add d (k / 2) c r)
'''
    s += '''
/-- A cheap total observation of the trie, so that the kernel must build all of it. -/
def Trie.sumAbs : Trie → Nat
  | .leaf v => v.natAbs
  | .node l r => l.sumAbs + r.sumAbs

def Trie.force (t : Trie) : Trie := match t with
  | .leaf v => .leaf v
  | .node a b => .node a b

def loopT (fab : Nat) (c : Int) : List Nat → List Bool → Trie → Trie
  | m :: ms, s :: ss, acc => loopT fab c ms ss ((acc.add 15 (m ||| fab) (if s then c else -c)).force)
  | _, _, acc => acc

def loopB (fa : Nat) (sg : List Bool) : List Nat → List Int → Trie → Trie
  | f :: fs, c :: cs, acc => loopB fa sg fs cs (loopT (fa ||| f) c tMasks sg acc).force
  | _, _, acc => acc

def loopA (sg : List Bool) : List Nat → List (List Int) → Trie → Trie
  | f :: fs, row :: rows, acc => loopA sg fs rows (loopB f sg fbMasks row acc).force
  | _, _, acc => acc

def loopBlocks : List (List Bool) → List (List (List Int)) → Trie → Trie
  | sg :: sgs, A :: As, acc => loopBlocks sgs As (loopA sg faMasks A acc).force
  | _, _, acc => acc
'''
    s = s.replace('/-- A cheap', 'def faMasks : List Nat := ' + str(fa) + '\ndef fbMasks : List Nat := ' + str(fb) +
                  '\ndef tMasks : List Nat := ' + str(tm) + '\n\n/-- A cheap')
    s += '\ndef signs : List (List Bool) :=\n  [' + ',\n   '.join('[' + ', '.join('true' if x else 'false' for x in row) + ']' for row in signs) + ']\n'
    s += '\ndef blocks : List (List (List Int)) :=\n  [' + ',\n   '.join(
        '[' + ', '.join('[' + ', '.join(lean_int(int(x)) for x in row) + ']' for row in A) + ']' for A in r4) + ']\n'
    total = 0
    from collections import defaultdict
    acc = defaultdict(int)
    for sg, A in zip(signs, r4):
        for a in range(15):
            for b in range(15):
                for T in range(64):
                    c = int(A[a][b]) if sg[T] else -int(A[a][b])
                    acc[tm[T] | fa[a] | fb[b]] += c
    total = sum(abs(v) for v in acc.values())
    s += f'\n/-- Expected `sumAbs`, computed by the generator. -/\ndef expected : Nat := {total}\n'
    s += '\nset_option profiler true in\ntheorem expansion_ok : (loopBlocks signs blocks (.leaf 0)).sumAbs = expected := by decide +kernel\n\nend EvenCycleApex.Bench\n'
    (out / f'BenchC_{tag}.lean').write_text(s, encoding='utf-8')


def main():
    cert, out = Path(sys.argv[1]), Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    bench_a(cert, out)
    bench_b(cert, out)
    bench_c(cert, out, forced=True)   # the lazy variant (forced=False) was not run


if __name__ == '__main__' and len(sys.argv) == 3:
    main()


def bench_b2(cert, out, per_file_chunks=32):
    """Optimized variant (b'): direct `Nat` primitives, 3-bit permutation fields, a packed pair-index
    table, a one-line bijectivity test, and one theorem per chunk (the kernel cache is per declaration)."""
    w = json.loads((cert / 'lean-data' / 'normalization_witnesses.json').read_text())
    nf, perms = w['normal_form'], w['permutation']
    codes = [sum(p[i] << (3 * i) for i in range(6)) for p in perms]
    packed = [nf[g] | (codes[g] << 15) for g in range(1 << 15)]
    fst = sum(i << (3 * b) for b, (i, j) in enumerate(EDGES))
    snd = sum(j << (3 * b) for b, (i, j) in enumerate(EDGES))
    tab = sum(INDEX[tuple(sorted((i, j)))] << (4 * (6 * i + j)) for i in range(6) for j in range(6) if i != j)
    s = header("M0 benchmark (b'): 32,768 relabelling witnesses with direct Nat primitives; one theorem per chunk.\n"
               'Entry `g` is `ν(g) ||| (code(π_g) <<< 15)`, `code(π) = Σ π(i) <<< 3i`.')
    s += f'''def edgeFst (b : Nat) : Nat := Nat.mod (Nat.shiftRight {fst} (Nat.mul 3 b)) 8
def edgeSnd (b : Nat) : Nat := Nat.mod (Nat.shiftRight {snd} (Nat.mul 3 b)) 8
/-- `pairIdx i j` for `i ≠ j`, from a packed 6×6 table of 4-bit fields. -/
def pairIdx (i j : Nat) : Nat := Nat.mod (Nat.shiftRight {tab} (Nat.mul 4 (Nat.add (Nat.mul 6 i) j))) 16
def permAt (code i : Nat) : Nat := Nat.mod (Nat.shiftRight code (Nat.mul 3 i)) 8
def bit (g b : Nat) : Nat := Nat.land (Nat.shiftRight g b) 1

def relabelGo (g code : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => Nat.lor (relabelGo g code b)
      (Nat.shiftLeft (bit g b) (pairIdx (permAt code (edgeFst b)) (permAt code (edgeSnd b))))

/-- The six fields are `< 6` and cover `{{0,…,5}}`, hence form a permutation. -/
def isPerm (code : Nat) : Bool :=
  Nat.blt code 262144 &&
  Nat.beq (Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft 1 (permAt code 0)) (Nat.shiftLeft 1 (permAt code 1)))
    (Nat.lor (Nat.shiftLeft 1 (permAt code 2)) (Nat.shiftLeft 1 (permAt code 3))))
    (Nat.lor (Nat.shiftLeft 1 (permAt code 4)) (Nat.shiftLeft 1 (permAt code 5)))) 63

def checkOne (g e : Nat) : Bool :=
  let code := Nat.shiftRight e 15
  isPerm code && Nat.beq (relabelGo g code 15) (Nat.land e 32767)

def checkChunk : Nat → List Nat → Bool
  | _, [] => true
  | g, e :: es => checkOne g e && checkChunk (Nat.succ g) es

'''
    for c, ch in enumerate(chunks(packed, 1024)):
        s += f'def chunk{c} : List Nat := [' + ', '.join(map(str, ch)) + ']\n'
    s += '\nset_option profiler true\n'
    for c in range(per_file_chunks):
        s += f'theorem chunk{c}_ok : checkChunk {1024 * c} chunk{c} = true := by decide +kernel\n'
    s += '\nend EvenCycleApex.Bench\n'
    (out / 'BenchB2.lean').write_text(s, encoding='utf-8')


if __name__ == '__main__' and len(sys.argv) > 3 and sys.argv[3] == 'b2':
    bench_b2(Path(sys.argv[1]), Path(sys.argv[2]))


def r4_skeleton_data(cert):
    """Orbit ids (0..155) of the r = 4 skeleton masks [T ∪ F_a ∪ F_b'], the merged and unmerged
    coefficient streams for mean_three, and the expected packed accumulators."""
    w = json.loads((cert / 'lean-data' / 'normalization_witnesses.json').read_text())
    nf = w['normal_form']
    reps = sorted(set(nf))
    orbit = {rep: k for k, rep in enumerate(reps)}
    mats = json.loads((cert / 'mean_three_sos.json').read_text())['matrices'][8:19]
    types = [0, 1, 3, 7, 11, 12, 13, 15, 30, 31, 63]
    roots = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    fa = [sum(1 << INDEX[(i, 4)] for i in range(4) if (bits >> i) & 1) for bits in range(1, 16)]
    fb = [sum(1 << INDEX[(i, 5)] for i in range(4) if (bits >> i) & 1) for bits in range(1, 16)]
    tm = [sum(1 << INDEX[roots[e]] for e in range(6) if (T >> e) & 1) for T in range(64)]
    sign = lambda t, T: 1 if bin(T & ~t).count('1') % 2 == 0 else -1
    merged, unmerged = [], []
    for a in range(15):
        for b in range(15):
            for T in range(64):
                o = orbit[nf[tm[T] | fa[a] | fb[b]]]
                merged.append((o, sum(sign(t, T) * int(A[a][b]) for t, A in zip(types, mats))))
    for t, A in zip(types, mats):
        for a in range(15):
            for b in range(15):
                for T in range(64):
                    unmerged.append((orbit[nf[tm[T] | fa[a] | fb[b]]], sign(t, T) * int(A[a][b])))
    return mats, types, merged, unmerged


def packed(stream, W=128):
    pos = neg = 0
    for o, c in stream:
        if c >= 0:
            pos += c << (W * o)
        else:
            neg += (-c) << (W * o)
    return pos, neg


PACKED_CORE = '''/-- One forced update of the packed accumulator `(pos, neg)`: slot `o` has width 128 bits. -/
def upd (pos neg o : Nat) (c : Int) (k : Nat → Nat → Bool) : Bool :=
  match c with
  | .ofNat m =>
      let p := Nat.add pos (Nat.shiftLeft m (Nat.mul 128 o))
      match Nat.beq p 0 with
      | true => k p neg
      | false => k p neg
  | .negSucc m =>
      let q := Nat.add neg (Nat.shiftLeft (Nat.succ m) (Nat.mul 128 o))
      match Nat.beq q 0 with
      | true => k pos q
      | false => k pos q
'''


def bench_c2(cert, out):
    mats, types, merged, _ = r4_skeleton_data(cert)
    signs = [[(bin(T & ~t).count('1') % 2 == 0) for T in range(64)] for t in types]
    orbits = [o for o, _ in merged]
    # (1) merged stream, packed accumulator: coefficients computed in Lean from the 11 matrices
    s = header('M0 benchmark (c2): r = 4 group of `mean_three`, the 11 blocks merged per (a, b, T):\n'
               '14,400 updates of a packed accumulator (156 slots × 128 bits), orbit ids supplied as data.')
    s += PACKED_CORE
    s += '''
/-- `Σ_t ±A⁽ᵗ⁾_ab` for one skeleton: the heads of the eleven matrices' current rows, signed by `T`. -/
def coefT (T : Nat) : List Bool → List Int → Int
  | s :: ss, a :: as => (if s then a else Int.neg a) + coefT T ss as
  | _, _ => 0

/-- Walk `T = 0..63` for one `(a, b)`, with the eleven entries `es` and the orbit ids `os`. -/
def loopT (es : List Int) : Nat → List (List Bool) → List Nat → Nat → Nat → (List Nat → Nat → Nat → Bool) → Bool
  | T, sg :: sgs, o :: os, pos, neg, k => upd pos neg o (coefT T sg es) fun p q => loopT es (T + 1) sgs os p q k
  | _, _, os, pos, neg, k => k os pos neg

/-- Heads and tails of the eleven current rows. -/
def heads : List (List Int) → List Int
  | (a :: _) :: rs => a :: heads rs
  | _ => []
def tails : List (List Int) → List (List Int)
  | (_ :: as) :: rs => as :: tails rs
  | _ => []

def loopB (sgT : List (List Bool)) : Nat → List (List Int) → List Nat → Nat → Nat → (List Nat → Nat → Nat → Bool) → Bool
  | 0, _, os, pos, neg, k => k os pos neg
  | n + 1, rows, os, pos, neg, k =>
      loopT (heads rows) 0 sgT os pos neg fun os' p q => loopB sgT n (tails rows) os' p q k

def rowsAt : List (List (List Int)) → List (List Int)
  | (r :: _) :: ms => r :: rowsAt ms
  | _ => []
def restRows : List (List (List Int)) → List (List (List Int))
  | (_ :: rs) :: ms => rs :: restRows ms
  | _ => []

def loopA (sgT : List (List Bool)) : Nat → List (List (List Int)) → List Nat → Nat → Nat → (List Nat → Nat → Nat → Bool) → Bool
  | 0, _, os, pos, neg, k => k os pos neg
  | n + 1, ms, os, pos, neg, k =>
      loopB sgT 15 (rowsAt ms) os pos neg fun os' p q => loopA sgT n (restRows ms) os' p q k
'''
    # signs transposed: for each T, the 11 signs
    sgT = [[signs[j][T] for j in range(11)] for T in range(64)]
    s += '\ndef sgT : List (List Bool) :=\n  [' + ',\n   '.join('[' + ', '.join('true' if x else 'false' for x in row) + ']' for row in sgT) + ']\n'
    s += '\ndef blocks : List (List (List Int)) :=\n  [' + ',\n   '.join(
        '[' + ', '.join('[' + ', '.join(lean_int(int(x)) for x in row) + ']' for row in A) + ']' for A in mats) + ']\n'
    s += '\ndef orbitIds : List Nat := ' + str(orbits) + '\n'
    pos, neg = packed(merged)
    s += f'\ndef posExpected : Nat := {pos}\ndef negExpected : Nat := {neg}\n'
    s += '''
set_option profiler true in
theorem merged_ok :
    loopA sgT 15 blocks orbitIds 0 0 (fun os p q => os.isEmpty && Nat.beq p posExpected && Nat.beq q negExpected) = true := by
  decide +kernel

end EvenCycleApex.Bench
'''
    (out / 'BenchC2.lean').write_text(s, encoding='utf-8')



if __name__ == '__main__' and len(sys.argv) > 3 and sys.argv[3] == 'c2':
    bench_c2(Path(sys.argv[1]), Path(sys.argv[2]))
