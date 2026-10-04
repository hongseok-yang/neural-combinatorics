import ApicesCommonness.Cycles.Certificate.Checker

/-!
# The certificate targets, from the literal edge sets

Blueprint `def:certificate-targets` (contract item 1 of the plan: the targets are built here from
the literal edge sets, never copied from the certificate side).  Graph polynomials are lists of
`(coefficient, mask)` monomials (`GraphPoly`), evaluated by `evalPoly`; sums are concatenations,
`polyMul` is the labelled product `[g] · [h] = [g ∪ h]` (used only on disjoint edge sets).

`𝖯_ε(E)` (`parityPoly`) lists the subgraphs `F ⊆ E` with `|F| ≡ ε (mod 2)`, enumerated densely over
the submasks of `E` (DEVIATIONS X3 (iii)).  Only the three targets on the proof path are defined
(`P_mean,2` is excluded by plan D10).
-/

open Finset

namespace ApicesCommonness

variable {d : ℕ}

/-- The mask of a literal edge list `[(i, j), …]`. -/
def edgeMask : List (ℕ × ℕ) → ℕ
  | [] => 0
  | e :: es => 2 ^ pairIdx e.1 e.2 ||| edgeMask es

/-- The number of set bits among the fifteen edge positions. -/
def bitCount (g : ℕ) : ℕ := ((List.range 15).filter fun b => g.testBit b).length

/-- `𝖯_ε(E) = ∑_{F ⊆ E, |F| ≡ ε (2)} [F]`. -/
def parityPoly (ε : ℕ) (E : List (ℕ × ℕ)) : GraphPoly :=
  ((subMasks (edgeMask E) 15).filter fun h => bitCount h % 2 == ε).map fun h => (1, h)

/-- `c · P`. -/
def polyScale (c : ℤ) (P : GraphPoly) : GraphPoly := P.map fun x => (c * x.1, x.2)

/-- The labelled product `P · Q`, `[g] · [h] = [g ∪ h]`. -/
def polyMul (P Q : GraphPoly) : GraphPoly :=
  P.flatMap fun x => Q.map fun y => (x.1 * y.1, x.2 ||| y.2)

/-- The monomial `c [E]`. -/
def mono (c : ℤ) (E : List (ℕ × ℕ)) : GraphPoly := [(c, edgeMask E)]

/-- `E_s = {{i, j} : i < s, j ∈ I_s} ∪ {{s, s+1}, {s, s+2}}`, `I_s = {s, s+1, s+2}`. -/
def edgesE (s : ℕ) : List (ℕ × ℕ) :=
  (List.range s).flatMap (fun i => [(i, s), (i, s + 1), (i, s + 2)]) ++ [(s, s + 1), (s, s + 2)]

/-- `B_s = {{i, j} : i < s, j ∈ {s+1, s+2}}`. -/
def edgesB (s : ℕ) : List (ℕ × ℕ) := (List.range s).flatMap fun i => [(i, s + 1), (i, s + 2)]

/-- `P_mean,3 = 𝖯₀(E₃) − 𝖯₀(B₃)`. -/
def targetMeanThree : GraphPoly := parityPoly 0 (edgesE 3) ++ polyScale (-1) (parityPoly 0 (edgesB 3))

/-- `F_ε = 2𝖯_ε(E₃) − 𝖯_ε(B₃)`. -/
def polyF (ε : ℕ) : GraphPoly := polyScale 2 (parityPoly ε (edgesE 3)) ++ polyScale (-1) (parityPoly ε (edgesB 3))

/-- `P_△ = [01] + [02] + [12] − [01, 02, 12]`. -/
def polyPtri : GraphPoly :=
  mono 1 [(0, 1)] ++ mono 1 [(0, 2)] ++ mono 1 [(1, 2)] ++ mono (-1) [(0, 1), (0, 2), (1, 2)]

/-- `C = 𝖯₀({01, 12, 23, 03})`. -/
def polyC : GraphPoly := parityPoly 0 [(0, 1), (1, 2), (2, 3), (0, 3)]

/-- `P₋ = 3F₀ − 3C + F₁ − P_△·F₀ − 13M − T_△ − 12A + 4MT_△ − 12P₃`. -/
def targetNeg : GraphPoly :=
  polyScale 3 (polyF 0) ++ polyScale (-3) polyC ++ polyF 1 ++ polyScale (-1) (polyMul polyPtri (polyF 0)) ++
    mono (-13) [(0, 1)] ++ mono (-1) [(0, 1), (0, 2), (1, 2)] ++ mono (-12) [(0, 1), (2, 3)] ++
    mono 4 [(0, 1), (2, 3), (2, 4), (3, 4)] ++ mono (-12) [(0, 1), (1, 2), (2, 3)]

/-- `P₊ = 6F₀ − 6C + F₁ + P_△·F₀ − 19M − 23T_△ + 12A − 4MT_△ − 24P₃`. -/
def targetPos : GraphPoly :=
  polyScale 6 (polyF 0) ++ polyScale (-6) polyC ++ polyF 1 ++ polyMul polyPtri (polyF 0) ++
    mono (-19) [(0, 1)] ++ mono (-23) [(0, 1), (0, 2), (1, 2)] ++ mono 12 [(0, 1), (2, 3)] ++
    mono (-4) [(0, 1), (2, 3), (2, 4), (3, 4)] ++ mono (-24) [(0, 1), (1, 2), (2, 3)]

/-! ### Evaluation of the combinators -/

lemma evalPoly_append (K : FiniteKernel d) (P Q : GraphPoly) :
    evalPoly K (P ++ Q) = evalPoly K P + evalPoly K Q := by
  simp [evalPoly]

lemma evalPoly_scale (K : FiniteKernel d) (c : ℤ) (P : GraphPoly) :
    evalPoly K (polyScale c P) = c * evalPoly K P := by
  rw [evalPoly, evalPoly, polyScale, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

lemma evalPoly_mono (K : FiniteKernel d) (c : ℤ) (E : List (ℕ × ℕ)) :
    evalPoly K (mono c E) = c * evalMask K (edgeMask E) := by
  simp [evalPoly, mono]

lemma evalPoly_mul (K : FiniteKernel d) (P Q : GraphPoly) :
    evalPoly K (polyMul P Q) = (P.map fun x => (x.1 : ℝ) *
      (Q.map fun y => (y.1 : ℝ) * evalMask K (x.2 ||| y.2)).sum).sum := by
  induction P with
  | nil => simp [evalPoly, polyMul]
  | cons x P ih =>
    rw [polyMul, List.flatMap_cons, ← polyMul, evalPoly_append, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [evalPoly, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun y _ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring

end ApicesCommonness
