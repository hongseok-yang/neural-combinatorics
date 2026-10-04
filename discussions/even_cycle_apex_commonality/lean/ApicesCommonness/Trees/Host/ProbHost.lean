import ApicesCommonness.Trees.Graph.Apex
import ApicesCommonness.Common.Host.EdgeDensity

/-!
# Weighted hosts with `[0,1]` kernels, and their scalars

Plan T-D2 and §2.2.  A `ProbHost V` is a finite type `V` with weights `w ≥ 0` of mass one and a
symmetric kernel `M` with values in `[0,1]`: exactly the data of a step graphon
(`exists_host_of_isStepKernel`, cell weights and step matrix).  Hosts are allowed over any finite
type (not only `Fin d`), so that the doubled host of T-D8 can be `Bool × V`; for `V = Fin d`,
`hostDens` is `hostDensity` of `Common/Host/Defs.lean` (`hostDens_eq_hostDensity`).

Scalars (the paper's `d(x)`, `r(x,y)`, `a(x)`, `E`, `D`, `R`, weighted):

```
  deg x = ∑_y w_y M_xy,   cod x y = ∑_z w_z M_xz M_yz,   tri x = ∑_y w_y M_xy cod x y,
  E = ∑_x w_x deg x = t(K₂),   D = ∑_x w_x (deg x)² = t(P₃),   R = ∑_x w_x tri x = t(K₃).
```
-/

open Finset SimpleGraph

namespace ApicesCommonness

/-- A weighted finite host with a symmetric `[0,1]`-valued kernel. -/
structure ProbHost (V : Type*) [Fintype V] where
  w : V → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1
  M : V → V → ℝ
  M_symm : ∀ i j, M i j = M j i
  M_nonneg : ∀ i j, 0 ≤ M i j
  M_le_one : ∀ i j, M i j ≤ 1

variable {V : Type*} [Fintype V]

/-- The homomorphism density of `F` in the kernel `L` on the host `(V, w)`. -/
noncomputable def hostDens (w : V → ℝ) {v : ℕ} (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (L : V → V → ℝ) : ℝ :=
  ∑ x : Fin v → V, (∏ i, w (x i)) * ∏ p ∈ edgePairs F, L (x p.1) (x p.2)

lemma hostDens_eq_hostDensity {d v : ℕ} (w : Fin d → ℝ) (F : SimpleGraph (Fin v))
    [DecidableRel F.Adj] (L : Fin d → Fin d → ℝ) : hostDens w F L = hostDensity w F L := rfl

/-- Summing over `Fin (n + 1) → V` one coordinate at a time. -/
lemma sum_fun_succ {M : Type*} [AddCommMonoid M] {n : ℕ} (g : (Fin (n + 1) → V) → M) :
    ∑ x, g x = ∑ a, ∑ y : Fin n → V, g (Matrix.vecCons a y) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => V).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ### Densities of `K₂`, `P₃`, `K₃` in any kernel -/

section SmallGraphs

variable (w : V → ℝ) (L : V → V → ℝ)

lemma hostDens_K₂ :
    hostDens w (⊤ : SimpleGraph (Fin 2)) L = ∑ x, ∑ y, w x * w y * L x y := by
  unfold hostDens
  rw [edgePairs_K₂]
  simp only [sum_fun_succ, Fintype.sum_unique, Fin.prod_univ_two, prod_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

lemma hostDens_P₃ :
    hostDens w (pathGraph 3) L = ∑ x, ∑ y, ∑ z, w x * w y * w z * (L x y * L y z) := by
  unfold hostDens
  rw [edgePairs_P₃]
  simp only [sum_fun_succ, Fintype.sum_unique, Fin.prod_univ_three]
  simp

lemma hostDens_K₃ :
    hostDens w (⊤ : SimpleGraph (Fin 3)) L
      = ∑ x, ∑ y, ∑ z, w x * w y * w z * (L x y * (L x z * L y z)) := by
  unfold hostDens
  rw [edgePairs_K₃]
  simp only [sum_fun_succ, Fintype.sum_unique, Fin.prod_univ_three]
  simp

end SmallGraphs

namespace ProbHost

variable (K : ProbHost V)

/-! ### Scalars -/

/-- The weighted degree `d(x) = ∑_y w_y M_xy`. -/
noncomputable def deg (x : V) : ℝ := ∑ y, K.w y * K.M x y

/-- The weighted codegree `r(x, y) = ∑_z w_z M_xz M_yz`. -/
noncomputable def cod (x y : V) : ℝ := ∑ z, K.w z * K.M x z * K.M y z

/-- The weighted triangle count at `x`: `a(x) = ∑_y w_y M_xy r(x, y)`. -/
noncomputable def tri (x : V) : ℝ := ∑ y, K.w y * K.M x y * K.cod x y

/-- `E = t(K₂)`. -/
noncomputable def E : ℝ := ∑ x, K.w x * K.deg x

/-- `D = t(P₃)`. -/
noncomputable def D : ℝ := ∑ x, K.w x * K.deg x ^ 2

/-- `R = t(K₃)`. -/
noncomputable def R : ℝ := ∑ x, K.w x * K.tri x

lemma deg_nonneg (x : V) : 0 ≤ K.deg x :=
  sum_nonneg fun y _ => mul_nonneg (K.w_nonneg y) (K.M_nonneg x y)

lemma deg_le_one (x : V) : K.deg x ≤ 1 := by
  calc K.deg x ≤ ∑ y, K.w y :=
        sum_le_sum fun y _ => mul_le_of_le_one_right (K.w_nonneg y) (K.M_le_one x y)
    _ = 1 := K.w_sum

lemma cod_nonneg (x y : V) : 0 ≤ K.cod x y :=
  sum_nonneg fun z _ => mul_nonneg (mul_nonneg (K.w_nonneg z) (K.M_nonneg x z)) (K.M_nonneg y z)

lemma cod_symm (x y : V) : K.cod x y = K.cod y x :=
  sum_congr rfl fun z _ => by ring

lemma cod_le_deg (x y : V) : K.cod x y ≤ K.deg x :=
  sum_le_sum fun z _ => mul_le_of_le_one_right
    (mul_nonneg (K.w_nonneg z) (K.M_nonneg x z)) (K.M_le_one y z)

lemma tri_nonneg (x : V) : 0 ≤ K.tri x :=
  sum_nonneg fun y _ => mul_nonneg (mul_nonneg (K.w_nonneg y) (K.M_nonneg x y)) (K.cod_nonneg x y)

lemma tri_le_deg_sq (x : V) : K.tri x ≤ K.deg x ^ 2 := by
  calc K.tri x ≤ ∑ y, K.w y * K.M x y * K.deg x :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (K.cod_le_deg x y)
          (mul_nonneg (K.w_nonneg y) (K.M_nonneg x y))
    _ = K.deg x ^ 2 := by rw [← sum_mul, sq]; rfl

lemma E_nonneg : 0 ≤ K.E := sum_nonneg fun x _ => mul_nonneg (K.w_nonneg x) (K.deg_nonneg x)

lemma D_nonneg : 0 ≤ K.D := sum_nonneg fun x _ => mul_nonneg (K.w_nonneg x) (sq_nonneg _)

lemma R_nonneg : 0 ≤ K.R := sum_nonneg fun x _ => mul_nonneg (K.w_nonneg x) (K.tri_nonneg x)

lemma R_le_D : K.R ≤ K.D :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (K.tri_le_deg_sq x) (K.w_nonneg x)

lemma D_le_E : K.D ≤ K.E :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (by rw [sq]; exact mul_le_of_le_one_right (K.deg_nonneg x) (K.deg_le_one x)) (K.w_nonneg x)

lemma pos_of_R_pos (h : 0 < K.R) : 0 < K.E ∧ 0 < K.D :=
  ⟨h.trans_le (K.R_le_D.trans K.D_le_E), h.trans_le K.R_le_D⟩

/-- A single positive term makes the codegree positive. -/
lemma cod_pos_of {x y z : V} (h : K.w z * K.M x z * K.M y z ≠ 0) : 0 < K.cod x y :=
  lt_of_lt_of_le
    ((mul_nonneg (mul_nonneg (K.w_nonneg z) (K.M_nonneg x z)) (K.M_nonneg y z)).lt_of_ne h.symm)
    (single_le_sum (f := fun z => K.w z * K.M x z * K.M y z)
      (fun z _ => mul_nonneg (mul_nonneg (K.w_nonneg z) (K.M_nonneg x z)) (K.M_nonneg y z))
      (mem_univ z))

lemma tri_pos_of {x y : V} (h : K.w y * K.M x y * K.cod x y ≠ 0) : 0 < K.tri x :=
  lt_of_lt_of_le
    ((mul_nonneg (mul_nonneg (K.w_nonneg y) (K.M_nonneg x y)) (K.cod_nonneg x y)).lt_of_ne h.symm)
    (single_le_sum (f := fun y => K.w y * K.M x y * K.cod x y)
      (fun y _ => mul_nonneg (mul_nonneg (K.w_nonneg y) (K.M_nonneg x y)) (K.cod_nonneg x y))
      (mem_univ y))

lemma deg_pos_of_tri_pos {x : V} (h : 0 < K.tri x) : 0 < K.deg x := by
  have := (h.trans_le (K.tri_le_deg_sq x))
  rcases (K.deg_nonneg x).lt_or_eq with h' | h'
  · exact h'
  · rw [← h'] at this; simp at this

/-! ### The scalars are densities -/

lemma E_eq_sum : K.E = ∑ x, ∑ y, K.w x * K.w y * K.M x y := by
  simp only [E, deg, mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

lemma R_eq_sum : K.R = ∑ x, ∑ y, K.w x * K.w y * K.M x y * K.cod x y := by
  simp only [R, tri, mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

lemma hostDens_K₂_eq : hostDens K.w (⊤ : SimpleGraph (Fin 2)) K.M = K.E := by
  rw [hostDens_K₂, E_eq_sum]

lemma hostDens_P₃_eq : hostDens K.w (pathGraph 3) K.M = K.D := by
  rw [hostDens_P₃, sum_comm]
  simp only [D, deg, sq, sum_mul, mul_sum]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => sum_congr rfl fun z _ => ?_
  rw [K.M_symm x y]
  ring

lemma hostDens_K₃_eq : hostDens K.w (⊤ : SimpleGraph (Fin 3)) K.M = K.R := by
  rw [hostDens_K₃]
  simp only [R, tri, cod, mul_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  ring

end ProbHost

end ApicesCommonness
