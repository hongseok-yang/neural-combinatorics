import EvenCycleApex.Graph.HomDensity

/-!
# The weighted finite host

Plan D2.  Sections 4–7 of the blueprint are proved on a finite probability space `Fin d` whose
atoms carry weights `w i ≥ 0` summing to one, with a symmetric signed kernel `U` with `|U| ≤ 1`
(`FiniteKernel`).  The blueprint's uniform host is `w = 1/d`.  Weights are only required to be
nonnegative: the step approximants of a graphon (`Host/Bridge.lean`) may have cells of mass zero,
and every finite argument goes through with "at every point" replaced by "at every point of
positive mass", which is all the blueprint uses.

`hostDensity w F L` is the homomorphism density of `F` in the kernel `L` on the host:

```
  t(F, L) = ∑_{x : V(F) → Fin d} (∏ᵢ w(xᵢ)) ∏_{ij ∈ E(F)} L(xᵢ, xⱼ).
```
-/

open Finset

namespace EvenCycleApex

/-- A weighted finite host `Fin d` carrying a symmetric kernel `U` with values in `[-1, 1]`. -/
structure FiniteKernel (d : ℕ) where
  /-- The atom weights. -/
  w : Fin d → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1
  /-- The signed kernel `U = 2W − 1`. -/
  U : Fin d → Fin d → ℝ
  U_symm : ∀ i j, U i j = U j i
  U_abs_le : ∀ i j, |U i j| ≤ 1

/-- `t(F, L)` on a weighted finite host. -/
def hostDensity {d v : ℕ} (w : Fin d → ℝ) (F : SimpleGraph (Fin v)) [DecidableRel F.Adj]
    (L : Fin d → Fin d → ℝ) : ℝ :=
  ∑ x : Fin v → Fin d, (∏ i, w (x i)) * ∏ p ∈ edgePairs F, L (x p.1) (x p.2)

namespace FiniteKernel

variable {d : ℕ} (K : FiniteKernel d)

lemma U_le_one (i j : Fin d) : K.U i j ≤ 1 := (abs_le.mp (K.U_abs_le i j)).2

lemma neg_one_le_U (i j : Fin d) : -1 ≤ K.U i j := (abs_le.mp (K.U_abs_le i j)).1

/-- The colour kernel `S_σ = 1 + σU` of the host. -/
def S (σ : ℝ) : Fin d → Fin d → ℝ := colourKernel σ K.U

lemma S_apply (σ : ℝ) (i j : Fin d) : K.S σ i j = 1 + σ * K.U i j := rfl

lemma S_symm (σ : ℝ) (i j : Fin d) : K.S σ i j = K.S σ j i := by
  rw [S_apply, S_apply, K.U_symm]

/-- For `σ = ±1`, `0 ≤ S_σ ≤ 2`. -/
lemma S_nonneg {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (i j : Fin d) : 0 ≤ K.S σ i j := by
  rcases hσ with rfl | rfl <;> simp only [S_apply] <;>
    linarith [K.U_le_one i j, K.neg_one_le_U i j]

lemma S_le_two {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (i j : Fin d) : K.S σ i j ≤ 2 := by
  rcases hσ with rfl | rfl <;> simp only [S_apply] <;>
    linarith [K.U_le_one i j, K.neg_one_le_U i j]

/-- The kernel of the complementary graphon: `U ↦ −U`. -/
def neg : FiniteKernel d where
  w := K.w
  w_nonneg := K.w_nonneg
  w_sum := K.w_sum
  U := fun i j => -K.U i j
  U_symm := fun i j => by rw [K.U_symm]
  U_abs_le := fun i j => by rw [abs_neg]; exact K.U_abs_le i j

lemma neg_S (σ : ℝ) : K.neg.S σ = K.S (-σ) := by
  funext i j
  simp only [S_apply, neg]
  ring

end FiniteKernel

end EvenCycleApex
