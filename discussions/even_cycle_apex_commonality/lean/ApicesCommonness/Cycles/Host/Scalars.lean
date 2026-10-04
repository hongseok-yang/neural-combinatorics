import ApicesCommonness.Cycles.Host.Matrix
import ApicesCommonness.Cycles.Host.Spectral

/-!
# Scalar moments of a finite kernel

Blueprint `def:finite-scalars` and `lem:fourth-traces`, on a weighted host (plan D2).  With
`f(i) = ∑ⱼ wⱼ U(i, j)` and the codegree `K(i, j) = ∑ₜ wₜ U(i, t) U(j, t)`:

```
  m = ⟨1, f⟩,  a = m²,  b = ⟨f, f⟩,  c = Tr T⁴,  r = c^{1/4},  p₃ = ⟨1, T³ 1⟩,  τ = Tr T³,
  q = E_{x,y} f(x) U(x, y) K(x, y),
  r_{σ,4} = t(C₄, S_σ),  R_n = (t(C_n, S₊) + t(C_n, S₋)) / 2.
```

The scalars are defined as the explicit iterated sums (so exact hosts can be evaluated by
`norm_num`, `Host/Regression.lean`) and identified with edge-set densities
(`m_eq_edgeDensity`, …, `c_eq_edgeDensity`) and with the matrix model (`c_eq_trace`).

`fourth_colour_traces` is `lem:fourth-traces`: `R₄ = 1 + 2a + 4b + c` and
`r_{σ,4} = R₄ + 4σ(m + p₃)`.  The proof is the blueprint's: `lem:parity` over the four edges of
`C₄`, then each edge subset is recognised up to relabelling (the permutation found by `decide`) as
an edge, a path, a matching, a three-edge path, or the whole cycle.
-/

open Finset Matrix SimpleGraph

namespace ApicesCommonness

/-- Expanding a sum over `Fin (n + 1) → α` by the first value. -/
lemma sum_fun_fin_succ {α : Type*} [Fintype α] {n : ℕ} (g : (Fin (n + 1) → α) → ℝ) :
    ∑ x, g x = ∑ a, ∑ y : Fin n → α, g (Matrix.vecCons a y) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => α).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The edges of `C₄`, sorted. -/
def c4Edges : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 3), (1, 2), (2, 3)}

lemma edgePairs_cycleGraph_four : edgePairs (cycleGraph 4) = c4Edges := by decide

/-- The edges of `C₃`, sorted. -/
def c3Edges : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2), (1, 2)}

lemma edgePairs_cycleGraph_three : edgePairs (cycleGraph 3) = c3Edges := by decide

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

/-- The degree function `f(i) = ∑ⱼ wⱼ U(i, j)`. -/
def f (i : Fin d) : ℝ := ∑ j, K.w j * K.U i j

/-- `m = ⟨1, f⟩ = ∬ U`. -/
def m : ℝ := ∑ i, K.w i * K.f i

/-- `a = m²`. -/
def a : ℝ := K.m ^ 2

/-- `b = ⟨f, f⟩`. -/
def b : ℝ := ∑ i, K.w i * K.f i ^ 2

/-- The codegree `K(i, j) = ∑ₜ wₜ U(i, t) U(j, t)`, the kernel of `T²`. -/
def cod (i j : Fin d) : ℝ := ∑ t, K.w t * K.U i t * K.U j t

/-- `c = Tr T⁴`, the signed four-cycle density. -/
def c : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, K.w i * K.w j * K.w k * K.w l * (K.U i j * K.U j k * K.U k l * K.U l i)

/-- `r = c^{1/4}`. -/
noncomputable def r : ℝ := K.c ^ ((1 : ℝ) / 4)

/-- `p₃ = ⟨1, T³ 1⟩`, the signed three-edge path density. -/
def p3 : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, K.w i * K.w j * K.w k * K.w l * (K.U i j * K.U j k * K.U k l)

/-- `τ = Tr T³`, the signed triangle density. -/
def τ : ℝ := ∑ i, ∑ j, ∑ k, K.w i * K.w j * K.w k * (K.U i j * K.U j k * K.U k i)

/-- `q = E_{x,y} f(x) U(x, y) K(x, y)` (triangle with a pendant edge). -/
def q : ℝ := ∑ i, ∑ j, K.w i * K.w j * (K.f i * K.U i j * K.cod i j)

/-- `r_{σ,4} = t(C₄, S_σ) = Tr T_{S_σ}⁴`. -/
def rσ4 (σ : ℝ) : ℝ := hostDensity K.w (cycleGraph 4) (K.S σ)

/-- `R_n = E_σ t(C_n, S_σ)`. -/
noncomputable def R (n : ℕ) : ℝ :=
  (hostDensity K.w (cycleGraph n) (K.S 1) + hostDensity K.w (cycleGraph n) (K.S (-1))) / 2

/-! ### Elementary identities -/

lemma m_eq_double_sum : K.m = ∑ i, ∑ j, K.w i * K.U i j * K.w j := by
  simp only [m, f, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma f_abs_le (i : Fin d) : |K.f i| ≤ 1 := by
  calc |K.f i| ≤ ∑ j, |K.w j * K.U i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, K.w j := sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (K.w_nonneg j)]
        exact mul_le_of_le_one_right (K.w_nonneg j) (K.U_abs_le i j)
    _ = 1 := K.w_sum

lemma cod_symm (i j : Fin d) : K.cod i j = K.cod j i := by
  simp only [cod]
  refine sum_congr rfl fun t _ => by ring

/-! ### Edge-set densities of the scalars -/

lemma m_eq_edgeDensity : K.m = edgeDensity K.w ({(0, 1)} : Finset (Fin 2 × Fin 2)) K.U := by
  rw [m_eq_double_sum]
  unfold edgeDensity
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_two, prod_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma b_eq_edgeDensity :
    K.b = edgeDensity K.w ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3)) K.U := by
  unfold edgeDensity
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_three]
  simp
  -- `b = ∑ⱼ wⱼ (∑ᵢ wᵢ U(i, j)) (∑ₖ wₖ U(j, k))`, with the centre `j` summed first
  rw [sum_comm]
  simp only [b, f, sq, mul_sum, sum_mul]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
  rw [K.U_symm j i]
  ring

lemma p3_eq_edgeDensity :
    K.p3 = edgeDensity K.w ({(0, 1), (1, 2), (2, 3)} : Finset (Fin 4 × Fin 4)) K.U := by
  unfold edgeDensity
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_four]
  simp
  simp only [p3]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
    sum_congr rfl fun l _ => by ring

lemma c_eq_edgeDensity : K.c = edgeDensity K.w c4Edges K.U := by
  unfold edgeDensity c4Edges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_four]
  simp
  simp only [c]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
    sum_congr rfl fun l _ => ?_
  rw [K.U_symm l i]
  ring

lemma τ_eq_edgeDensity : K.τ = edgeDensity K.w c3Edges K.U := by
  unfold edgeDensity c3Edges
  simp only [sum_fun_fin_succ, Fintype.sum_unique, Fin.prod_univ_three]
  simp
  simp only [τ]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [K.U_symm k i]
  ring

lemma c_eq_hostDensity : K.c = hostDensity K.w (cycleGraph 4) K.U := by
  rw [c_eq_edgeDensity, hostDensity_eq_edgeDensity, edgePairs_cycleGraph_four]

lemma τ_eq_hostDensity : K.τ = hostDensity K.w (cycleGraph 3) K.U := by
  rw [τ_eq_edgeDensity, hostDensity_eq_edgeDensity, edgePairs_cycleGraph_three]

/-! ### The matrix model -/

/-- The Euclidean matrix `T` of the kernel operator. -/
noncomputable def T : Matrix (Fin d) (Fin d) ℝ := hostMatrix K.w K.U

/-- The Euclidean matrix `T_{S_σ}` of the colour kernel. -/
noncomputable def TS (σ : ℝ) : Matrix (Fin d) (Fin d) ℝ := hostMatrix K.w (K.S σ)

lemma T_isHermitian : K.T.IsHermitian := hostMatrix_isHermitian K.w K.U_symm

lemma TS_isHermitian (σ : ℝ) : (K.TS σ).IsHermitian := hostMatrix_isHermitian K.w (K.S_symm σ)

lemma c_eq_trace : K.c = trace (K.T ^ 4) := by
  rw [c_eq_hostDensity, hostDensity_cycle_eq_trace K.w_nonneg K.U_symm (by norm_num), T]

lemma τ_eq_trace : K.τ = trace (K.T ^ 3) := by
  rw [τ_eq_hostDensity, hostDensity_cycle_eq_trace K.w_nonneg K.U_symm le_rfl, T]

lemma rσ4_eq_trace (σ : ℝ) : K.rσ4 σ = trace (K.TS σ ^ 4) :=
  hostDensity_cycle_eq_trace K.w_nonneg (K.S_symm σ) (by norm_num)

/-- The unit vector `u = (√wᵢ)`. -/
lemma unit_dot_self : hostUnit K.w ⬝ᵥ hostUnit K.w = 1 := hostUnit_dot_self K.w_nonneg K.w_sum

/-- The Rayleigh value of `T_{S_σ}` at the unit vector is `1 + σ m`. -/
lemma rayleigh_TS (σ : ℝ) : hostUnit K.w ⬝ᵥ (K.TS σ *ᵥ hostUnit K.w) = 1 + σ * K.m := by
  have h1 : ∑ i, ∑ j, K.w i * K.w j = 1 := by
    simp only [← mul_sum, K.w_sum, mul_one]
  rw [TS, hostUnit_rayleigh K.w_nonneg]
  calc ∑ i, ∑ j, K.w i * K.S σ i j * K.w j
      = ∑ i, ∑ j, K.w i * K.w j + σ * ∑ i, ∑ j, K.w i * K.U i j * K.w j := by
        simp only [S_apply, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    _ = 1 + σ * K.m := by rw [h1, m_eq_double_sum]

/-! ### `lem:fourth-traces` -/

/-- Isomorphic sorted edge sets of `C₄`'s subgraphs have equal `U`-densities. -/
private lemma iso4 {F G : Finset (Fin 4 × Fin 4)} (hF : ∀ p ∈ F, p.1 < p.2)
    (h : ∃ π : Equiv.Perm (Fin 4), F.image (fun p => sortPair (π p.1) (π p.2)) = G) :
    edgeDensity K.w F K.U = edgeDensity K.w G K.U :=
  edgeDensity_eq_of_iso K.w K.U_symm hF h

/-- A single edge on four vertices has density `m`. -/
lemma edge4 : edgeDensity K.w ({(0, 1)} : Finset (Fin 4 × Fin 4)) K.U = K.m := by
  have h : castAddEdges 2 ({(0, 1)} : Finset (Fin 2 × Fin 2))
      = ({(0, 1)} : Finset (Fin 4 × Fin 4)) := by decide
  rw [m_eq_edgeDensity, ← edgeDensity_castAdd K.w K.w_sum (b := 2)
    ({(0, 1)} : Finset (Fin 2 × Fin 2)) K.U, h]

/-- A two-edge path on four vertices has density `b`. -/
lemma path2_4 : edgeDensity K.w ({(0, 1), (1, 2)} : Finset (Fin 4 × Fin 4)) K.U = K.b := by
  have h : castAddEdges 1 ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3))
      = ({(0, 1), (1, 2)} : Finset (Fin 4 × Fin 4)) := by decide
  rw [b_eq_edgeDensity, ← edgeDensity_castAdd K.w K.w_sum (b := 1)
    ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3)) K.U, h]

/-- A perfect matching on four vertices has density `m²`. -/
lemma matching4 : edgeDensity K.w ({(0, 1), (2, 3)} : Finset (Fin 4 × Fin 4)) K.U = K.a := by
  have h := edgeDensity_append K.w ({(0, 1)} : Finset (Fin 2 × Fin 2))
    ({(0, 1)} : Finset (Fin 2 × Fin 2)) K.U
  have hE : castAddEdges 2 ({(0, 1)} : Finset (Fin 2 × Fin 2))
      ∪ natAddEdges 2 ({(0, 1)} : Finset (Fin 2 × Fin 2))
      = ({(0, 1), (2, 3)} : Finset (Fin 4 × Fin 4)) := by decide
  rw [hE, ← m_eq_edgeDensity] at h
  rw [a, sq, ← h]

/-- **`lem:fourth-traces`, mean part.**  `R₄ = 1 + 2a + 4b + c`. -/
theorem R_four : K.R 4 = 1 + 2 * K.a + 4 * K.b + K.c := by
  have hE : ∀ p ∈ c4Edges, p.1 < p.2 := by decide
  have hsub : ∀ F ∈ c4Edges.powerset, ∀ p ∈ F, p.1 < p.2 := fun F hF p hp =>
    hE p (mem_powerset.mp hF hp)
  have hpar : c4Edges.powerset.filter (fun F => Even F.card)
      = {∅, {(0, 1), (0, 3)}, {(0, 1), (1, 2)}, {(0, 1), (2, 3)}, {(0, 3), (1, 2)},
          {(0, 3), (2, 3)}, {(1, 2), (2, 3)}, c4Edges} := by decide
  rw [R, hostDensity_eq_edgeDensity, hostDensity_eq_edgeDensity, edgePairs_cycleGraph_four, S, S,
    edgeDensity_colour_even, hpar]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  rw [edgeDensity_empty K.w K.w_sum, ← c_eq_edgeDensity,
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(0, 1), (0, 3)} : Finset (Fin 4 × Fin 4)).image (fun p => sortPair (π p.1) (π p.2))
        = {(0, 1), (1, 2)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(0, 3), (2, 3)} : Finset (Fin 4 × Fin 4)).image (fun p => sortPair (π p.1) (π p.2))
        = {(0, 1), (1, 2)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(1, 2), (2, 3)} : Finset (Fin 4 × Fin 4)).image (fun p => sortPair (π p.1) (π p.2))
        = {(0, 1), (1, 2)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(0, 3), (1, 2)} : Finset (Fin 4 × Fin 4)).image (fun p => sortPair (π p.1) (π p.2))
        = {(0, 1), (2, 3)}),
    path2_4, matching4]
  ring

/-- **`lem:fourth-traces`, signed part.**  `(r_{+,4} − r_{−,4}) / 2 = 4(m + p₃)`. -/
theorem rσ4_odd : (K.rσ4 1 - K.rσ4 (-1)) / 2 = 4 * (K.m + K.p3) := by
  have hpar : c4Edges.powerset.filter (fun F => Odd F.card)
      = {{(0, 1)}, {(0, 3)}, {(1, 2)}, {(2, 3)}, {(0, 1), (0, 3), (1, 2)},
          {(0, 1), (0, 3), (2, 3)}, {(0, 1), (1, 2), (2, 3)}, {(0, 3), (1, 2), (2, 3)}} := by
    decide
  rw [rσ4, rσ4, hostDensity_eq_edgeDensity, hostDensity_eq_edgeDensity, edgePairs_cycleGraph_four,
    S, S, edgeDensity_colour_odd, hpar]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  rw [K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(0, 3)} : Finset (Fin 4 × Fin 4)).image (fun p => sortPair (π p.1) (π p.2)) = {(0, 1)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(1, 2)} : Finset (Fin 4 × Fin 4)).image (fun p => sortPair (π p.1) (π p.2)) = {(0, 1)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(2, 3)} : Finset (Fin 4 × Fin 4)).image (fun p => sortPair (π p.1) (π p.2)) = {(0, 1)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(0, 1), (0, 3), (1, 2)} : Finset (Fin 4 × Fin 4)).image
        (fun p => sortPair (π p.1) (π p.2)) = {(0, 1), (1, 2), (2, 3)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(0, 1), (0, 3), (2, 3)} : Finset (Fin 4 × Fin 4)).image
        (fun p => sortPair (π p.1) (π p.2)) = {(0, 1), (1, 2), (2, 3)}),
    K.iso4 (by decide) (by decide : ∃ π : Equiv.Perm (Fin 4),
      ({(0, 3), (1, 2), (2, 3)} : Finset (Fin 4 × Fin 4)).image
        (fun p => sortPair (π p.1) (π p.2)) = {(0, 1), (1, 2), (2, 3)}),
    edge4, ← p3_eq_edgeDensity]
  ring

/-- **`lem:fourth-traces`.**  `R₄ = 1 + 2a + 4b + c` and `r_{σ,4} = R₄ + 4σ(m + p₃)`. -/
theorem fourth_colour_traces :
    K.R 4 = 1 + 2 * K.a + 4 * K.b + K.c ∧
      K.rσ4 1 = K.R 4 + 4 * (K.m + K.p3) ∧ K.rσ4 (-1) = K.R 4 - 4 * (K.m + K.p3) := by
  have h1 := K.R_four
  have h2 := K.rσ4_odd
  have hR : K.R 4 = (K.rσ4 1 + K.rσ4 (-1)) / 2 := rfl
  refine ⟨h1, ?_, ?_⟩ <;> linarith

end FiniteKernel

end ApicesCommonness
