import EvenCycleApex.Certificate.Main
import EvenCycleApex.Finite.TwoApex

/-!
# Three-apex moments as graph polynomials

Blueprint `lem:codegree-moments` (the parts for three apices), `def:three-apex-polynomial` and the
conditional graph expansion used in `lem:GH`.

On the sampling space of a colour and three apices (`Sample d 3`), with inner vertices `x, y, y'`:

* `E_z [G(z) Π₃]` is the six-vertex sum over the edges `E₃` (`pi3Edges`: every apex to `x, y, y'`,
  and `x` to `y, y'`), and `E_z [G(z) D₃²]` the one over `B₃` (`d3Edges`, vertex `3` isolated), for
  any function `G` of the apices (`sum_three_apex_Pi`, `sum_three_apex_D_sq`);
* the colour average of `∏_{e ∈ E} S_σ(e)` is the sum over the even submasks of `E`, and the signed
  average the sum over the odd ones (`colour_even_mask`, `colour_odd_mask`), so that the graph
  polynomials `𝖯_ε(E)` of `Targets.lean` evaluate to colour averages (`evalPoly_parityPoly_even`,
  `evalPoly_parityPoly_odd`).
-/

open Finset

namespace EvenCycleApex

variable {d : ℕ}

/-- The edges of `E₃` on `Fin 6`: apices `0, 1, 2`, inner vertices `x = 3`, `y = 4`, `y' = 5`. -/
def pi3Edges : Finset (Fin 6 × Fin 6) :=
  {(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)}

/-- The edges of `B₃` on `Fin 6` (vertex `3` isolated). -/
def d3Edges : Finset (Fin 6 × Fin 6) := {(0, 4), (0, 5), (1, 4), (1, 5), (2, 4), (2, 5)}

lemma maskEdges_edgesE_three : maskEdges (edgeMask (edgesE 3)) = pi3Edges := by decide +kernel

lemma maskEdges_edgesB_three : maskEdges (edgeMask (edgesB 3)) = d3Edges := by decide +kernel

/-- The apex coordinates of a six-vertex assignment. -/
def apexOf (x : Fin 6 → Fin d) : Fin 3 → Fin d := fun j => x (Fin.castAdd 3 j)

private lemma apexOf_vec (a b c e f g : Fin d) (h : Fin 0 → Fin d) :
    apexOf (Matrix.vecCons a (Matrix.vecCons b (Matrix.vecCons c (Matrix.vecCons e
      (Matrix.vecCons f (Matrix.vecCons g h)))))) = Matrix.vecCons a (Matrix.vecCons b
        (Matrix.vecCons c default)) := by
  funext j
  fin_cases j <;> rfl

/-- **`E_z [G(z) Π₃]` as a six-vertex sum** over `E₃`. -/
lemma sum_three_apex_Pi (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) (G : (Fin 3 → Fin d) → ℝ) :
    ∑ z : Fin 3 → Fin d, (∏ j, w (z j)) * G z *
        ∑ x, w x * (∏ j, L (z j) x) * (∑ y, w y * L x y * ∏ j, L (z j) y) ^ 2
      = ∑ x : Fin 6 → Fin d, (∏ i, w (x i)) * G (apexOf x) * ∏ p ∈ pi3Edges, L (x p.1) (x p.2) := by
  unfold pi3Edges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_three, Fin.prod_univ_six]
  simp [apexOf_vec]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  simp only [sq, mul_sum, sum_mul]
  refine sum_congr rfl fun f _ => sum_congr rfl fun g _ => ?_
  ring

/-- **`E_z [G(z) D₃²]` as a six-vertex sum** over `B₃` (the isolated vertex integrates to one). -/
lemma sum_three_apex_D_sq (w : Fin d → ℝ) (hw : ∑ j, w j = 1) (L : Fin d → Fin d → ℝ)
    (G : (Fin 3 → Fin d) → ℝ) :
    ∑ z : Fin 3 → Fin d, (∏ j, w (z j)) * G z * (∑ x, w x * ∏ j, L (z j) x) ^ 2
      = ∑ x : Fin 6 → Fin d, (∏ i, w (x i)) * G (apexOf x) * ∏ p ∈ d3Edges, L (x p.1) (x p.2) := by
  unfold d3Edges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_three, Fin.prod_univ_six]
  simp [apexOf_vec]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  set gv := G (Matrix.vecCons a (Matrix.vecCons b (Matrix.vecCons c default)))
  have key : ∀ x : Fin d, (∑ x₁, ∑ x₂, w a * w b * w c * w x * w x₁ * w x₂ * gv *
      (L a x₁ * (L a x₂ * (L b x₁ * (L b x₂ * (L c x₁ * L c x₂))))))
      = w x * (w a * w b * w c * gv * (∑ y, w y * (L a y * L b y * L c y)) ^ 2) := by
    intro x
    rw [sq, sum_mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun x₁ _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun x₂ _ => by ring
  rw [sum_congr rfl fun x _ => key x, ← sum_mul, hw, one_mul]

/-! ### Parity polynomials as colour averages -/

lemma bitCount_go (g : ℕ) : ∀ n ≤ 15,
    ((List.range n).filter fun b => g.testBit b).length
      = (univ.filter fun b : Fin 15 => (b : ℕ) < n ∧ g.testBit b = true).card
  | 0, _ => by simp
  | n + 1, hn => by
    have ih := bitCount_go g n (by omega)
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    cases hb : g.testBit n
    · rw [filter_succ_clear hb]
      simp [hb]
    · rw [filter_succ_set (by omega) hb, card_insert_of_notMem (not_mem_filter_self (h := g) (by omega))]
      simp [hb]

lemma bitCount_eq_card (g : ℕ) :
    bitCount g = (univ.filter fun b : Fin 15 => g.testBit b = true).card := by
  rw [bitCount, bitCount_go g 15 le_rfl, filter_fifteen]

lemma prod_maskEdges {M : Type*} [CommMonoid M] (g : ℕ) (f : Fin 6 × Fin 6 → M) :
    ∏ e ∈ maskEdges g, f e = ∏ b ∈ univ.filter (fun b : Fin 15 => g.testBit b = true), f (pairOf b) :=
  prod_image fun _ _ _ _ h => pairOf_injective h

lemma card_maskEdges (g : ℕ) : (maskEdges g).card = bitCount g := by
  rw [maskEdges, card_image_of_injective _ pairOf_injective, bitCount_eq_card]

/-- `∑_{h ⊆ g} ∏_{e ∈ h} f(e) = ∏_{e ∈ g} (1 + f(e))`, over the submask enumeration. -/
lemma sum_subMasks_prod (g : ℕ) (f : Fin 6 × Fin 6 → ℝ) :
    ((subMasks g 15).map fun h => ∏ e ∈ maskEdges h, f e).sum = ∏ e ∈ maskEdges g, (1 + f e) := by
  rw [prod_maskEdges, ← filter_fifteen, prod_one_add_subMasks g (fun b => f (pairOf b)) 15 le_rfl]
  exact congrArg List.sum (List.map_congr_left fun h _ => by rw [prod_maskEdges, filter_fifteen])

lemma list_parity_even (l : List ℕ) (F : ℕ → ℝ) :
    ((l.map F).sum + (l.map fun h => (-1) ^ bitCount h * F h).sum) / 2
      = ((l.filter fun h => bitCount h % 2 == 0).map F).sum := by
  induction l with
  | nil => simp
  | cons h l ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    rcases Nat.even_or_odd (bitCount h) with he | ho
    · have hm : bitCount h % 2 = 0 := Nat.even_iff.mp he
      rw [he.neg_one_pow, if_pos (by simp [hm]), List.map_cons, List.sum_cons, ← ih]
      ring
    · have hm : bitCount h % 2 = 1 := Nat.odd_iff.mp ho
      rw [ho.neg_one_pow, if_neg (by simp [hm]), ← ih]
      ring

lemma list_parity_odd (l : List ℕ) (F : ℕ → ℝ) :
    ((l.map F).sum - (l.map fun h => (-1) ^ bitCount h * F h).sum) / 2
      = ((l.filter fun h => bitCount h % 2 == 1).map F).sum := by
  induction l with
  | nil => simp
  | cons h l ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    rcases Nat.even_or_odd (bitCount h) with he | ho
    · have hm : bitCount h % 2 = 0 := Nat.even_iff.mp he
      rw [he.neg_one_pow, if_neg (by simp [hm]), ← ih]
      ring
    · have hm : bitCount h % 2 = 1 := Nat.odd_iff.mp ho
      rw [ho.neg_one_pow, if_pos (by simp [hm]), List.map_cons, List.sum_cons, ← ih]
      ring

lemma prod_maskEdges_neg (h : ℕ) (u : Fin 6 × Fin 6 → ℝ) :
    ∏ e ∈ maskEdges h, -u e = (-1) ^ bitCount h * ∏ e ∈ maskEdges h, u e := by
  rw [prod_neg, card_maskEdges]

/-- **Even colour average over a mask.** -/
lemma colour_even_mask (g : ℕ) (u : Fin 6 × Fin 6 → ℝ) :
    ((∏ e ∈ maskEdges g, (1 + u e)) + ∏ e ∈ maskEdges g, (1 + -u e)) / 2
      = (((subMasks g 15).filter fun h => bitCount h % 2 == 0).map fun h =>
          ∏ e ∈ maskEdges h, u e).sum := by
  rw [← sum_subMasks_prod, ← sum_subMasks_prod, ← list_parity_even]
  simp only [prod_maskEdges_neg]

/-- **Odd (signed) colour average over a mask.** -/
lemma colour_odd_mask (g : ℕ) (u : Fin 6 × Fin 6 → ℝ) :
    ((∏ e ∈ maskEdges g, (1 + u e)) - ∏ e ∈ maskEdges g, (1 + -u e)) / 2
      = (((subMasks g 15).filter fun h => bitCount h % 2 == 1).map fun h =>
          ∏ e ∈ maskEdges h, u e).sum := by
  rw [← sum_subMasks_prod, ← sum_subMasks_prod, ← list_parity_odd]
  simp only [prod_maskEdges_neg]

lemma evalPoly_parityPoly (K : FiniteKernel d) (ε : ℕ) (E : List (ℕ × ℕ)) :
    evalPoly K (parityPoly ε E)
      = (((subMasks (edgeMask E) 15).filter fun h => bitCount h % 2 == ε).map fun h =>
          evalMask K h).sum := by
  simp [evalPoly, parityPoly, List.map_map, Function.comp_def]

/-- **`𝖯₀(E)` is the colour average of the density of `E`.** -/
theorem evalPoly_parityPoly_even (K : FiniteKernel d) (E : List (ℕ × ℕ)) :
    evalPoly K (parityPoly 0 E)
      = (edgeDensity K.w (maskEdges (edgeMask E)) (K.S 1)
          + edgeDensity K.w (maskEdges (edgeMask E)) (K.S (-1))) / 2 := by
  rw [evalPoly_parityPoly]
  simp only [evalMask, edgeDensity]
  rw [list_sum_finset_sum, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [List.sum_map_mul_left, ← mul_add, mul_div_assoc,
    ← colour_even_mask (edgeMask E) fun e => K.U (x e.1) (x e.2)]
  simp [FiniteKernel.S_apply]

/-- **`𝖯₁(E)` is the signed colour average of the density of `E`.** -/
theorem evalPoly_parityPoly_odd (K : FiniteKernel d) (E : List (ℕ × ℕ)) :
    evalPoly K (parityPoly 1 E)
      = (edgeDensity K.w (maskEdges (edgeMask E)) (K.S 1)
          - edgeDensity K.w (maskEdges (edgeMask E)) (K.S (-1))) / 2 := by
  rw [evalPoly_parityPoly]
  simp only [evalMask, edgeDensity]
  rw [list_sum_finset_sum, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [List.sum_map_mul_left, ← mul_sub, mul_div_assoc,
    ← colour_odd_mask (edgeMask E) fun e => K.U (x e.1) (x e.2)]
  simp [FiniteKernel.S_apply]

/-! ### Pointwise values of graph polynomials -/

/-- The value of a graph polynomial at one assignment of the six vertices. -/
def polyAt (L : Fin d → Fin d → ℝ) (P : GraphPoly) (x : Fin 6 → Fin d) : ℝ :=
  (P.map fun y => (y.1 : ℝ) * ∏ e ∈ maskEdges y.2, L (x e.1) (x e.2)).sum

lemma evalPoly_eq_sum_polyAt (K : FiniteKernel d) (P : GraphPoly) :
    evalPoly K P = ∑ x : Fin 6 → Fin d, (∏ i, K.w (x i)) * polyAt K.U P x := by
  simp only [evalPoly, polyAt, evalMask, edgeDensity, mul_sum]
  rw [list_sum_finset_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun y _ => by ring)

lemma polyAt_append (L : Fin d → Fin d → ℝ) (P Q : GraphPoly) (x : Fin 6 → Fin d) :
    polyAt L (P ++ Q) x = polyAt L P x + polyAt L Q x := by
  simp [polyAt]

lemma polyAt_scale (L : Fin d → Fin d → ℝ) (c : ℤ) (P : GraphPoly) (x : Fin 6 → Fin d) :
    polyAt L (polyScale c P) x = c * polyAt L P x := by
  rw [polyAt, polyAt, polyScale, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  simp only [Function.comp_apply]
  push_cast
  ring

/-- The labelled product factors pointwise when the edge sets are disjoint. -/
lemma polyAt_mul (L : Fin d → Fin d → ℝ) {P Q : GraphPoly}
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, Disjoint (maskEdges p.2) (maskEdges q.2)) (x : Fin 6 → Fin d) :
    polyAt L (polyMul P Q) x = polyAt L P x * polyAt L Q x := by
  induction P with
  | nil => simp [polyAt, polyMul]
  | cons p P ih =>
    rw [polyMul, List.flatMap_cons, ← polyMul, polyAt_append,
      ih fun p' hp' q hq => hPQ p' (List.mem_cons_of_mem _ hp') q hq]
    simp only [polyAt, List.map_cons, List.sum_cons, add_mul]
    congr 1
    rw [List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [maskEdges_lor, prod_union (hPQ p List.mem_cons_self q hq)]
    push_cast
    ring

/-- The pointwise value of `𝖯₀(E)`. -/
lemma polyAt_parityPoly_even (L : Fin d → Fin d → ℝ) (E : List (ℕ × ℕ)) (x : Fin 6 → Fin d) :
    polyAt L (parityPoly 0 E) x
      = ((∏ e ∈ maskEdges (edgeMask E), (1 + L (x e.1) (x e.2)))
          + ∏ e ∈ maskEdges (edgeMask E), (1 + -L (x e.1) (x e.2))) / 2 := by
  rw [colour_even_mask]
  simp [polyAt, parityPoly, List.map_map, Function.comp_def]

/-- The pointwise value of `𝖯₁(E)`. -/
lemma polyAt_parityPoly_odd (L : Fin d → Fin d → ℝ) (E : List (ℕ × ℕ)) (x : Fin 6 → Fin d) :
    polyAt L (parityPoly 1 E) x
      = ((∏ e ∈ maskEdges (edgeMask E), (1 + L (x e.1) (x e.2)))
          - ∏ e ∈ maskEdges (edgeMask E), (1 + -L (x e.1) (x e.2))) / 2 := by
  rw [colour_odd_mask]
  simp [polyAt, parityPoly, List.map_map, Function.comp_def]

/-- Every monomial of `𝖯_ε(E)` lies inside `E`. -/
lemma maskEdges_subset_of_mem_parityPoly {ε : ℕ} {E : List (ℕ × ℕ)} {y : ℤ × ℕ}
    (hy : y ∈ parityPoly ε E) : maskEdges y.2 ⊆ maskEdges (edgeMask E) := by
  simp only [parityPoly, List.mem_map, List.mem_filter] at hy
  obtain ⟨h, ⟨hh, -⟩, rfl⟩ := hy
  intro q hq
  obtain ⟨b, hb, rfl⟩ := mem_maskEdges.mp hq
  exact mem_maskEdges.mpr ⟨b, (subMasks_spec _ 15 h hh).2 b hb, rfl⟩

end EvenCycleApex
