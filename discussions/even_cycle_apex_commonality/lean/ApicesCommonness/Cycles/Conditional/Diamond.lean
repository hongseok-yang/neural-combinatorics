import ApicesCommonness.Cycles.Conditional.Trace

/-!
# The one-apex moments: the diamond

Blueprint `lem:diamond`.  For one apex (`s = 1`):

```
  Z₁ = E D₁² = 1 + b,       X := E Π₁ = 1 + 2a + 8b + c + 4q,       q² ≤ b c,
  X ≥ 1 + 2b + c/3.
```

* `D₁(σ, t) = 1 + σ f(t)`, and averaging `(1 + σ f)²` over the colour kills the cross term.
* `E Π₁` is the colour average of the density of the diamond `K_{1,2,1}` (apex `t`, inner vertex `x`,
  their common neighbours `y, y'`; `diamond_edgeDensity`).  By `lem:parity` it is the sum of the
  densities of its 16 even edge subsets, recognised up to relabelling by `decide`: the empty graph
  (`1`), two matchings (`a` each), eight two-edge paths (`b` each), one four-cycle (`c`) and four
  triangles with a pendant edge (`q` each).
* `q = ∑ᵢⱼ wᵢ wⱼ f(i) · U(i, j) K(i, j)`, so Cauchy–Schwarz gives `q² ≤ b · ∑ wᵢwⱼ K(i,j)² = b c`.
* `X − 1 − 2b − c/3 = 2a + 6b + 2c/3 + 4q ≥ 0`, since `(6b + 2c/3)² ≥ 16 b c ≥ 16 q²`.
-/

open Finset Matrix SimpleGraph

namespace ApicesCommonness

variable {d : ℕ}

/-- The diamond `K_{1,2,1}` on `Fin 4`: apex `0`, inner vertex `1`, common neighbours `2, 3`. -/
def diamondEdges : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)}

/-- A triangle `0, 1, 2` with the pendant edge `0 – 3`. -/
def trianglePendantEdges : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (0, 3), (1, 2)}

/-- Sums over a single apex coordinate. -/
lemma sum_fin_one_fun {α : Type*} [Fintype α] (g : (Fin 1 → α) → ℝ) :
    ∑ z, g z = ∑ t, g ![t] := by
  rw [sum_fun_fin_succ]
  simp only [Fintype.sum_unique]
  refine sum_congr rfl fun t _ => ?_
  congr 1

/-- The diamond density, written as the conditional sum `E_t E_x L(t,x) (E_y L(x,y) L(t,y))²`. -/
lemma diamond_edgeDensity (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) :
    edgeDensity w diamondEdges L
      = ∑ t, w t * ∑ x, w x * L t x * (∑ y, w y * L x y * L t y) ^ 2 := by
  unfold edgeDensity diamondEdges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_four]
  simp
  refine sum_congr rfl fun t _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [sq, sum_mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  ring

namespace FiniteKernel

variable (K : FiniteKernel d)

lemma q_eq_edgeDensity : K.q = edgeDensity K.w trianglePendantEdges K.U := by
  unfold edgeDensity trianglePendantEdges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_four]
  simp
  simp only [q, f, cod, mul_sum, sum_mul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  refine sum_congr rfl fun t _ => sum_congr rfl fun l _ => ?_
  ring

/-- For one apex, `D₁(σ, t) = 1 + σ f(t)`. -/
lemma condD_one (b : Bool) (t : Fin d) :
    K.condD ((b, ![t]) : Sample d 1) = 1 + colour b * K.f t := by
  simp only [condD, condH, Fin.prod_univ_one, Matrix.cons_val_zero, S_apply, mul_add, mul_one,
    sum_add_distrib, K.w_sum, f, mul_sum]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [K.U_symm t x]
  ring

/-- Expectation over one apex. -/
lemma E_one (F : Sample d 1 → ℝ) :
    K.E F = (∑ t, K.w t * F (true, ![t]) + ∑ t, K.w t * F (false, ![t])) / 2 := by
  rw [E_eq_colours, sum_fin_one_fun (fun z => (∏ j, K.w (z j)) * F (true, z)),
    sum_fin_one_fun (fun z => (∏ j, K.w (z j)) * F (false, z))]
  simp

/-- **`Z₁ = 1 + b`.** -/
theorem Z_one : K.Z 1 = 1 + K.b := by
  rw [Z, E_one]
  simp only [condD_one, colour_true, colour_false]
  have h : ∀ t, K.w t * (1 + 1 * K.f t) ^ 2 + K.w t * (1 + -1 * K.f t) ^ 2
      = 2 * (K.w t + K.w t * K.f t ^ 2) := fun t => by ring
  rw [← sum_add_distrib]
  simp only [h, ← mul_sum, sum_add_distrib, K.w_sum, b]
  ring

/-- `E Π₁` is the colour average of the diamond density. -/
lemma EPi_one_eq_diamond :
    K.EPi 1 = (edgeDensity K.w diamondEdges (colourKernel 1 K.U)
      + edgeDensity K.w diamondEdges (colourKernel (-1) K.U)) / 2 := by
  rw [EPi, E_one, diamond_edgeDensity, diamond_edgeDensity]
  congr 2 <;> refine sum_congr rfl fun t _ => ?_ <;> congr 1 <;>
    simp only [condPi, condA, condH, Fin.prod_univ_one, Matrix.cons_val_zero, colour_true,
      colour_false] <;> rfl

/-- **The diamond identity** `X = E Π₁ = 1 + 2a + 8b + c + 4q`. -/
theorem EPi_one : K.EPi 1 = 1 + 2 * K.a + 8 * K.b + K.c + 4 * K.q := by
  have hE : ∀ p ∈ diamondEdges, p.1 < p.2 := by decide
  have hpar : diamondEdges.powerset.filter (fun F => Even F.card)
      = {∅, {(0, 1), (0, 2)}, {(0, 1), (0, 3)}, {(0, 1), (1, 2)}, {(0, 1), (1, 3)},
          {(0, 2), (0, 3)}, {(0, 2), (1, 2)}, {(0, 2), (1, 3)}, {(0, 3), (1, 2)},
          {(0, 3), (1, 3)}, {(1, 2), (1, 3)},
          {(0, 2), (0, 3), (1, 2), (1, 3)}, {(0, 1), (0, 3), (1, 2), (1, 3)},
          {(0, 1), (0, 2), (1, 2), (1, 3)}, {(0, 1), (0, 2), (0, 3), (1, 3)},
          {(0, 1), (0, 2), (0, 3), (1, 2)}} := by decide
  rw [EPi_one_eq_diamond, edgeDensity_colour_even, hpar]
  simp (disch := decide) only [sum_insert, sum_singleton]
  have path : ∀ F : Finset (Fin 4 × Fin 4), (∀ p ∈ F, p.1 < p.2) →
      (∃ π : Equiv.Perm (Fin 4), F.image (fun p => sortPair (π p.1) (π p.2)) = {(0, 1), (1, 2)}) →
      edgeDensity K.w F K.U = K.b := fun F hF h => by
    rw [edgeDensity_eq_of_iso K.w K.U_symm hF h, K.path2_4]
  have match2 : ∀ F : Finset (Fin 4 × Fin 4), (∀ p ∈ F, p.1 < p.2) →
      (∃ π : Equiv.Perm (Fin 4), F.image (fun p => sortPair (π p.1) (π p.2)) = {(0, 1), (2, 3)}) →
      edgeDensity K.w F K.U = K.a := fun F hF h => by
    rw [edgeDensity_eq_of_iso K.w K.U_symm hF h, K.matching4]
  have cyc : ∀ F : Finset (Fin 4 × Fin 4), (∀ p ∈ F, p.1 < p.2) →
      (∃ π : Equiv.Perm (Fin 4), F.image (fun p => sortPair (π p.1) (π p.2)) = c4Edges) →
      edgeDensity K.w F K.U = K.c := fun F hF h => by
    rw [edgeDensity_eq_of_iso K.w K.U_symm hF h, ← K.c_eq_edgeDensity]
  have tri : ∀ F : Finset (Fin 4 × Fin 4), (∀ p ∈ F, p.1 < p.2) →
      (∃ π : Equiv.Perm (Fin 4), F.image (fun p => sortPair (π p.1) (π p.2))
        = trianglePendantEdges) →
      edgeDensity K.w F K.U = K.q := fun F hF h => by
    rw [edgeDensity_eq_of_iso K.w K.U_symm hF h, ← K.q_eq_edgeDensity]
  rw [edgeDensity_empty K.w K.w_sum,
    path _ (by decide) (by decide), path _ (by decide) (by decide),
    path _ (by decide) (by decide), path _ (by decide) (by decide),
    path _ (by decide) (by decide), path _ (by decide) (by decide),
    match2 _ (by decide) (by decide), match2 _ (by decide) (by decide),
    path _ (by decide) (by decide), path _ (by decide) (by decide),
    cyc _ (by decide) (by decide),
    tri _ (by decide) (by decide), tri _ (by decide) (by decide),
    tri _ (by decide) (by decide), tri _ (by decide) (by decide)]
  ring

/-- `q² ≤ b c` (Cauchy–Schwarz on pairs). -/
theorem q_sq_le : K.q ^ 2 ≤ K.b * K.c := by
  have hpair : K.q = ∑ p : Fin d × Fin d,
      (K.w p.1 * K.w p.2 * K.f p.1) * (K.U p.1 p.2 * K.cod p.1 p.2) := by
    rw [q, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hF : ∑ p : Fin d × Fin d, K.w p.1 * K.w p.2 * K.f p.1 ^ 2 = K.b := by
    rw [Fintype.sum_prod_type, b]
    refine sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← sum_mul, ← mul_sum, K.w_sum, mul_one]
  have hG : ∑ p : Fin d × Fin d, K.w p.1 * K.w p.2 * (K.U p.1 p.2 * K.cod p.1 p.2) ^ 2 ≤ K.c := by
    rw [c_eq_sum_cod_sq, ← Fintype.sum_prod_type']
    refine sum_le_sum fun p _ => ?_
    have hU : K.U p.1 p.2 ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [K.U_abs_le p.1 p.2, abs_nonneg (K.U p.1 p.2)]
    have hw : 0 ≤ K.w p.1 * K.w p.2 := mul_nonneg (K.w_nonneg _) (K.w_nonneg _)
    rw [mul_pow]
    nlinarith [mul_nonneg hw (sq_nonneg (K.cod p.1 p.2))]
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (r := fun p : Fin d × Fin d => (K.w p.1 * K.w p.2 * K.f p.1) * (K.U p.1 p.2 * K.cod p.1 p.2))
    (f := fun p => K.w p.1 * K.w p.2 * K.f p.1 ^ 2)
    (g := fun p => K.w p.1 * K.w p.2 * (K.U p.1 p.2 * K.cod p.1 p.2) ^ 2)
    (fun p _ => mul_nonneg (mul_nonneg (K.w_nonneg _) (K.w_nonneg _)) (sq_nonneg _))
    (fun p _ => mul_nonneg (mul_nonneg (K.w_nonneg _) (K.w_nonneg _)) (sq_nonneg _))
    (fun p _ => le_of_eq (by ring))
  rw [← hpair, hF] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hG K.b_nonneg)

/-- **`lem:diamond`.**  `Z₁ = 1 + b`, `X = E Π₁ = 1 + 2a + 8b + c + 4q`, `q² ≤ b c`, and
`X ≥ 1 + 2b + c/3`. -/
theorem diamond_lower_bound :
    K.Z 1 = 1 + K.b ∧ K.EPi 1 = 1 + 2 * K.a + 8 * K.b + K.c + 4 * K.q ∧
      K.q ^ 2 ≤ K.b * K.c ∧ 1 + 2 * K.b + K.c / 3 ≤ K.EPi 1 := by
  refine ⟨K.Z_one, K.EPi_one, K.q_sq_le, ?_⟩
  rw [K.EPi_one]
  have hq := K.q_sq_le
  have hb := K.b_nonneg
  have hc := K.c_nonneg
  have ha := K.a_nonneg
  -- `6b + 2c/3 + 4q ≥ 0` because `(6b + 2c/3)² ≥ 16 b c ≥ 16 q²`
  have key : 0 ≤ 6 * K.b + 2 * K.c / 3 + 4 * K.q := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [sq_nonneg (6 * K.b - 2 * K.c / 3), mul_nonneg hb hc]
  linarith

end FiniteKernel

end ApicesCommonness
