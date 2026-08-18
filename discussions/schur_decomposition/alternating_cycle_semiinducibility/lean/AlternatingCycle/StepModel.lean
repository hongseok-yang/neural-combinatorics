import AlternatingCycle.Conjugation

/-!
# The alternating-cycle theorem for step graphons

This is §2 and §9 of `alternating_cycles_schur_proof.tex` in the finite model.  A `StepGraphon` is a
finite partition with weights `w` summing to `1` together with a symmetric `[0,1]`-valued kernel
`W`.  Following `eq:mixed-trace`, the densities are **defined** as traces of the operator matrices

```
  (T_K)_{ij} = K_{ij} √(w_i) √(w_j),
```

so that

```
  Alt_{2m}(W) = Tr((T_W T_U)^m),        t(C_{2m}, 2W−1) = Tr(X^{2m}),    X = T_{2W−1}.
```

(`Analytic/` will connect these traces to the integral homomorphism densities; nothing below
depends on that.)

The structural facts are `eq:color-coordinate`,

```
  T_W = (P + X)/2,     T_U = (P − X)/2,      P = e ⊗ e,  e_i = √(w_i),
```

and the Hilbert–Schmidt budget `eq:HS-budget`, `Tr(X²) = ∑_{ij}(2W_{ij}−1)² w_i w_j ≤ 1`.  With
those, `eq:alt-trace` turns `4^m Alt_{2m}(W)` into `Tr(L^m)` and `thm:main` is `matrix_main_general`
verbatim.
-/

namespace AlternatingCycle

open Matrix Finset

noncomputable section

/-- A weighted step graphon. -/
structure StepGraphon (N : ℕ) where
  /-- The cell weights. -/
  w : Fin N → ℝ
  /-- The kernel values. -/
  W : Fin N → Fin N → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1
  W_symm : ∀ i j, W i j = W j i
  W_nonneg : ∀ i j, 0 ≤ W i j
  W_le_one : ∀ i j, W i j ≤ 1

namespace StepGraphon

variable {N : ℕ} (G : StepGraphon N)

/-- `e_i = √(w_i)`, a unit vector. -/
def e (i : Fin N) : ℝ := Real.sqrt (G.w i)

lemma e_sq (i : Fin N) : G.e i * G.e i = G.w i := Real.mul_self_sqrt (G.w_nonneg i)

lemma e_unit : G.e ⬝ᵥ G.e = 1 := by
  rw [dotProduct, ← G.w_sum]
  exact Finset.sum_congr rfl fun i _ => G.e_sq i

/-- The signed colour coordinate `X = T_{2W−1}`. -/
def Xm : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => (2 * G.W i j - 1) * G.e i * G.e j

/-- The operator of the kernel `W`. -/
def TW : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => G.W i j * G.e i * G.e j

/-- The operator of the complement kernel `U = 1 − W`. -/
def TU : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => (1 - G.W i j) * G.e i * G.e j

lemma Xm_symm : G.Xmᵀ = G.Xm := by
  refine Matrix.ext fun i j => ?_
  show (2 * G.W j i - 1) * G.e j * G.e i = (2 * G.W i j - 1) * G.e i * G.e j
  rw [G.W_symm j i]
  ring

/-- **`eq:color-coordinate`**, first half. -/
lemma two_smul_TW : (2 : ℝ) • G.TW = Matrix.vecMulVec G.e G.e + G.Xm := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, TW, Matrix.of_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Xm,
    Matrix.of_apply, smul_eq_mul]
  ring

/-- **`eq:color-coordinate`**, second half. -/
lemma two_smul_TU : (2 : ℝ) • G.TU = Matrix.vecMulVec G.e G.e - G.Xm := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, TU, Matrix.of_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Xm,
    Matrix.of_apply, smul_eq_mul]
  ring

/-! ### The densities -/

/-- `Alt_{2m}(W) = Tr((T_W T_U)^m)`, the alternating-cycle density of `eq:alt-trace`. -/
def alt (m : ℕ) : ℝ := Matrix.trace ((G.TW * G.TU) ^ m)

/-- `t(C_{2m}, 2W−1) = Tr(X^{2m})`, the signed even-cycle density. -/
def signedCycle (m : ℕ) : ℝ := Matrix.trace (G.Xm ^ (2 * m))

/-- **`eq:alt-trace`**: `4^m Alt_{2m}(W) = Tr(L^m)` with `L = (P+X)(P−X)`. -/
lemma four_pow_mul_alt (m : ℕ) :
    4 ^ m * G.alt m
      = Matrix.trace (((Matrix.vecMulVec G.e G.e + G.Xm)
          * (Matrix.vecMulVec G.e G.e - G.Xm)) ^ m) := by
  have hprod : (Matrix.vecMulVec G.e G.e + G.Xm) * (Matrix.vecMulVec G.e G.e - G.Xm)
      = (4 : ℝ) • (G.TW * G.TU) := by
    rw [← G.two_smul_TW, ← G.two_smul_TU, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
  rw [hprod, smul_pow, Matrix.trace_smul, alt, smul_eq_mul]

/-! ### The Hilbert–Schmidt budget -/

lemma Xm_mul_Xm_diag (i : Fin N) :
    (G.Xm * G.Xm) i i = ∑ j, (2 * G.W i j - 1) ^ 2 * G.w i * G.w j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (2 * G.W i j - 1) * G.e i * G.e j * ((2 * G.W j i - 1) * G.e j * G.e i) = _
  rw [G.W_symm j i]
  have hi := G.e_sq i
  have hj := G.e_sq j
  linear_combination ((2 * G.W i j - 1) ^ 2 * (G.e j * G.e j)) * hi
    + ((2 * G.W i j - 1) ^ 2 * G.w i) * hj

/-- **`eq:HS-budget`**: `Tr(X²) ≤ 1`. -/
lemma trace_Xm_sq_le_one : Matrix.trace (G.Xm * G.Xm) ≤ 1 := by
  have hbound : Matrix.trace (G.Xm * G.Xm) ≤ ∑ i, ∑ j, G.w i * G.w j := by
    rw [Matrix.trace]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Matrix.diag_apply, G.Xm_mul_Xm_diag i]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : (2 * G.W i j - 1) ^ 2 ≤ 1 := by
      nlinarith [G.W_nonneg i j, G.W_le_one i j]
    have h2 : 0 ≤ G.w i * G.w j := mul_nonneg (G.w_nonneg i) (G.w_nonneg j)
    nlinarith [h1, h2]
  have : ∑ i, ∑ j, G.w i * G.w j = 1 := by
    rw [← Finset.sum_mul_sum, G.w_sum, mul_one]
  linarith [hbound, this]

/-! ### Nonnegativity of the signed even cycle -/

/-- `lem:even-signed-cycle` in the finite model: `Tr(X^{2m}) = ‖X^m‖²_HS ≥ 0`. -/
lemma signedCycle_nonneg (m : ℕ) : 0 ≤ G.signedCycle m := by
  have hsym : (G.Xm ^ m)ᵀ = G.Xm ^ m := by
    rw [Matrix.transpose_pow, G.Xm_symm]
  have hsplit : G.Xm ^ (2 * m) = G.Xm ^ m * G.Xm ^ m := by
    rw [← pow_add]
    ring_nf
  rw [signedCycle, hsplit, Matrix.trace]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_nonneg fun j _ => ?_
  have : (G.Xm ^ m) j i = (G.Xm ^ m) i j := by
    conv_lhs => rw [← hsym]
    rfl
  rw [this]
  exact mul_self_nonneg _

/-! ### The theorem -/

/-- **`eq:main-strengthened`.**  For odd `m`,
`4^m Alt_{2m}(W) + t(C_{2m}, 2W−1) ≤ 1`. -/
theorem main_strengthened {m : ℕ} (hm : Odd m) :
    4 ^ m * G.alt m + G.signedCycle m ≤ 1 := by
  rw [G.four_pow_mul_alt m, signedCycle]
  exact matrix_main_general G.Xm_symm G.e_unit G.trace_Xm_sq_le_one hm

/-- **`eq:main-unweighted`.**  For odd `m`, `Alt_{2m}(W) ≤ 4^{-m}`. -/
theorem alt_le {m : ℕ} (hm : Odd m) : G.alt m ≤ 1 / 4 ^ m := by
  have h := G.main_strengthened hm
  have hnn := G.signedCycle_nonneg m
  have hpos : (0 : ℝ) < 4 ^ m := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  linarith

end StepGraphon

end

end AlternatingCycle
