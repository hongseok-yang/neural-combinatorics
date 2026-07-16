/-
# High-density theorem — exact moment/atomic expansion of `Φₘ`

This file isolates the algebraic content of `paper_new.tex`, Theorem `thm:expansion`.
For a moment sequence `s`, `momentConv s r j` is the coefficient of `zʲ` in
`(∑ k, s k zᵏ)^r`.  The `r`-th contribution to `Φₘ` is therefore

  `∑ j≤m-2r kerB m r q j · momentConv s r j`.

The first half below proves that this is exactly the difference between the two logarithmic
(`Sₘ`) coefficient contributions and the nonconstant path-resolvent contribution.  The second half
gives a measure-free version of the paper's product spectral integral: for a finite atomic measure
`∑ᵢ wᵢ δ_{λᵢ}`, iterated integration of `multiKernel` is exactly the same moment polynomial.

Thus no determinant, logarithm, or product-measure API is needed in the downstream proof.  A graphon
bridge only has to represent the finitely many compression moments by atoms in `[-1/2,1/2]` and
identify its defect with `momentPhi`; all kernel algebra and positivity are discharged here.
-/

import OddCycleBound.HighDensity.MixtureIntegral

open scoped BigOperators

namespace OddCycleBound.HighDensity

/-! ## Coefficients of powers of a moment series -/

/-- `momentConv s r j` is `[zʲ] (∑ k, s k zᵏ)^r`, defined without formal power series. -/
def momentConv (s : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | r + 1, j => ∑ k ∈ Finset.range (j + 1), s k * momentConv s r (j - k)

@[simp] lemma momentConv_zero_zero (s : ℕ → ℝ) : momentConv s 0 0 = 1 := rfl

@[simp] lemma momentConv_zero_succ (s : ℕ → ℝ) (j : ℕ) :
    momentConv s 0 (j + 1) = 0 := by
  simp [momentConv]

lemma momentConv_succ (s : ℕ → ℝ) (r j : ℕ) :
    momentConv s (r + 1) j =
      ∑ k ∈ Finset.range (j + 1), s k * momentConv s r (j - k) := rfl

/-- A convolution coefficient only uses input moments of index at most its coefficient index. -/
lemma momentConv_congr_of_le {s t : ℕ → ℝ} : ∀ (r j : ℕ),
    (∀ k ≤ j, s k = t k) → momentConv s r j = momentConv t r j
  | 0, j, _ => by cases j <;> rfl
  | r + 1, j, h => by
      rw [momentConv_succ, momentConv_succ]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := by
        rw [Finset.mem_range] at hk
        omega
      rw [h k hk_le, momentConv_congr_of_le r (j - k)
        (fun ell hell => h ell (by omega))]

/-- The `Sₘ` part of the `r`-th coefficient, after expanding the two resolvents.
The first summand is the `W` side (`p=1-q`, alternating moments), and the second is the `U` side. -/
noncomputable def momentShiftTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m - 2 * r + 1),
    ((m / r : ℝ) *
      ((Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          (1 - q) ^ (m - 2 * r - j) * (-1 : ℝ) ^ j
        + (Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          q ^ (m - 2 * r - j))) * momentConv s r j

/-- The nonconstant path-resolvent part of the `r`-th coefficient of `x_{m-1}`. -/
noncomputable def momentPathTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m - 2 * r + 1),
    (if j < m - 2 * r then
        (Nat.choose (m - 2 * r - 1 - j + r) r : ℝ) * q ^ (m - 2 * r - 1 - j)
      else 0) * momentConv s r j

/-- The `r`-th moment-polynomial contribution to `Φₘ`. -/
noncomputable def momentPhiTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  momentShiftTerm m r q s - momentPathTerm m r q s

/-- The complete moment-polynomial defect.  The index `k` represents `r=k+1`, so the sum is exactly
`1 ≤ r ≤ (m-1)/2`. -/
noncomputable def momentPhi (m : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range ((m - 1) / 2), momentPhiTerm m (k + 1) q s

/-- `momentPhi m` is a finite polynomial: agreement of moments through index `m` is enough. -/
theorem momentPhi_congr_of_le {m : ℕ} (q : ℝ) {s t : ℕ → ℝ}
    (h : ∀ j ≤ m, s j = t j) :
    momentPhi m q s = momentPhi m q t := by
  unfold momentPhi momentPhiTerm momentShiftTerm momentPathTerm
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1 <;> refine Finset.sum_congr rfl fun j hj => ?_
  all_goals
    rw [momentConv_congr_of_le _ _ fun ell hell => h ell (by
      have hjlt : j < m - 2 * (k + 1) + 1 := Finset.mem_range.mp hj
      omega)]

/-- The same `r`-th contribution, packaged using the coefficient `kerB` shared by `multiKernel` and
`diagKernel`. -/
noncomputable def momentKernelTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m - 2 * r + 1), kerB m r q j * momentConv s r j

/-- The complete kernel-side moment expansion. -/
noncomputable def momentKernelExpansion (m : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range ((m - 1) / 2), momentKernelTerm m (k + 1) q s

/-- **Coefficient form of `thm:expansion`, one `r` at a time.**  The two logarithmic contributions
minus the path-resolvent contribution have precisely the shared coefficient `kerB`. -/
lemma momentPhiTerm_eq_momentKernelTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) :
    momentPhiTerm m r q s = momentKernelTerm m r q s := by
  unfold momentPhiTerm momentShiftTerm momentPathTerm momentKernelTerm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold kerB
  ring

/-- **Exact moment-polynomial expansion of `Φₘ`.** -/
theorem momentPhi_eq_momentKernelExpansion (m : ℕ) (q : ℝ) (s : ℕ → ℝ) :
    momentPhi m q s = momentKernelExpansion m q s := by
  unfold momentPhi momentKernelExpansion
  refine Finset.sum_congr rfl fun k _ => ?_
  exact momentPhiTerm_eq_momentKernelTerm m (k + 1) q s

/-! ## Finite atomic product integrals

`atomicIntegral w λ r F` is the integral of `F(λ₁,…,λᵣ)` against the `r`-fold product of the finite
measure `∑ᵢ wᵢ δ_{λᵢ}`.  Lists keep the recursion lightweight and match `multiKernel` directly.
-/

variable {ι : Type*} [Fintype ι]

/-- Iterated integral against a finite atomic measure, represented as nested finite sums. -/
noncomputable def atomicIntegral (w lam : ι → ℝ) : ℕ → (List ℝ → ℝ) → ℝ
  | 0, F => F []
  | r + 1, F => ∑ i, w i * atomicIntegral w lam r (fun L => F (lam i :: L))

/-- Moments of the finite atomic measure `∑ᵢ wᵢ δ_{λᵢ}`. -/
noncomputable def atomicMoment (w lam : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ i, w i * lam i ^ j

@[simp] lemma atomicIntegral_zero (w lam : ι → ℝ) (r : ℕ) :
    atomicIntegral w lam r (fun _ => 0) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [atomicIntegral, ih]

lemma atomicIntegral_add (w lam : ι → ℝ) (r : ℕ) (F G : List ℝ → ℝ) :
    atomicIntegral w lam r (fun L => F L + G L) =
      atomicIntegral w lam r F + atomicIntegral w lam r G := by
  induction r generalizing F G with
  | zero => rfl
  | succ r ih =>
      simp only [atomicIntegral]
      simp_rw [ih, mul_add, Finset.sum_add_distrib]

lemma atomicIntegral_const_mul (w lam : ι → ℝ) (r : ℕ) (c : ℝ) (F : List ℝ → ℝ) :
    atomicIntegral w lam r (fun L => c * F L) = c * atomicIntegral w lam r F := by
  induction r generalizing c F with
  | zero => rfl
  | succ r ih =>
      simp only [atomicIntegral]
      simp_rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring

lemma atomicIntegral_finset_sum {κ : Type*} (w lam : ι → ℝ) (r : ℕ)
    (t : Finset κ) (F : κ → List ℝ → ℝ) :
    atomicIntegral w lam r (fun L => ∑ k ∈ t, F k L) =
      ∑ k ∈ t, atomicIntegral w lam r (F k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [atomicIntegral_zero]
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      rw [atomicIntegral_add, ih]

/-- Integrating `h_j(λ₁,…,λᵣ)` against an atomic product measure gives the coefficient of the `r`-th
power of its moment series.  This is the measure-free Fubini step E4 in the formalization plan. -/
lemma atomicIntegral_hsym (w lam : ι → ℝ) : ∀ (r j : ℕ),
    atomicIntegral w lam r (fun L => hsym L j) = momentConv (atomicMoment w lam) r j
  | 0, j => by
      simp [atomicIntegral, momentConv, hsym_nil]
  | r + 1, j => by
      rw [momentConv_succ]
      simp only [atomicIntegral]
      have hinner : ∀ i : ι,
          atomicIntegral w lam r (fun L => hsym (lam i :: L) j) =
            ∑ k ∈ Finset.range (j + 1),
              lam i ^ k * momentConv (atomicMoment w lam) r (j - k) := by
        intro i
        simp_rw [hsym_cons]
        rw [atomicIntegral_finset_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [atomicIntegral_const_mul, atomicIntegral_hsym w lam r (j - k)]
      simp_rw [hinner, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold atomicMoment
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring

/-- Atomic product integral of the multivariate kernel. -/
noncomputable def atomicKernelTerm (m r : ℕ) (q : ℝ) (w lam : ι → ℝ) : ℝ :=
  atomicIntegral w lam r (multiKernel m r q)

/-- The sum of the finite atomic product integrals over `1 ≤ r ≤ (m-1)/2`. -/
noncomputable def atomicKernelExpansion (m : ℕ) (q : ℝ) (w lam : ι → ℝ) : ℝ :=
  ∑ k ∈ Finset.range ((m - 1) / 2), atomicKernelTerm m (k + 1) q w lam

/-- **Finite atomic form of `thm:expansion`, one `r` at a time.** -/
theorem atomicKernelTerm_eq_momentKernelTerm {m r : ℕ} (hr : r ≠ 0)
    (hn : 1 ≤ m - 2 * r) (q : ℝ) (w lam : ι → ℝ) :
    atomicKernelTerm m r q w lam = momentKernelTerm m r q (atomicMoment w lam) := by
  unfold atomicKernelTerm momentKernelTerm
  have hexpand : multiKernel m r q = fun L =>
      ∑ j ∈ Finset.range (m - 2 * r + 1), kerB m r q j * hsym L j := by
    funext L
    exact multiKernel_expand hr hn q L
  rw [hexpand, atomicIntegral_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [atomicIntegral_const_mul, atomicIntegral_hsym]

/-- **Finite atomic `thm:expansion`.**  For every odd `m ≥ 3`, the moment coefficient defect is the
sum of the `r`-fold atomic product integrals of `multiKernel`. -/
theorem momentPhi_eq_atomicKernelExpansion {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (q : ℝ) (w lam : ι → ℝ) :
    momentPhi m q (atomicMoment w lam) = atomicKernelExpansion m q w lam := by
  rw [momentPhi_eq_momentKernelExpansion]
  unfold momentKernelExpansion atomicKernelExpansion
  refine Finset.sum_congr rfl fun k hk => ?_
  have hklt : k < (m - 1) / 2 := Finset.mem_range.mp hk
  have hrm : 2 * (k + 1) < m := by
    rcases hm with ⟨t, ht⟩
    omega
  exact (atomicKernelTerm_eq_momentKernelTerm (r := k + 1) (by omega)
    (by omega : 1 ≤ m - 2 * (k + 1)) q w lam).symm

/-- Positivity of an atomic product integral, retaining the list-length and support invariants needed
by `multiKernel_nonneg`. -/
lemma atomicIntegral_nonneg_of (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (P : ℝ → Prop) : ∀ (r : ℕ) (F : List ℝ → ℝ),
      (∀ L, L.length = r → (∀ x ∈ L, P x) → 0 ≤ F L) →
      (∀ i, P (lam i)) → 0 ≤ atomicIntegral w lam r F
  | 0, F, hF, _ => by
      exact hF [] rfl (by simp)
  | r + 1, F, hF, hP => by
      simp only [atomicIntegral]
      refine Finset.sum_nonneg fun i _ => mul_nonneg (hw i) ?_
      refine atomicIntegral_nonneg_of w lam hw P r (fun L => F (lam i :: L)) ?_ hP
      intro L hlen hL
      apply hF (lam i :: L)
      · simp [hlen]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hP i
        · exact hL x hx

/-- If the diagonal kernels are nonnegative on `[-1/2,1/2]`, then every finite atomic `r`-th moment
contribution with nonnegative weights and support in that interval is nonnegative. -/
theorem momentKernelTerm_nonneg_of_atomic {m r : ℕ} (hr : r ≠ 0)
    (hn : 1 ≤ m - 2 * r) (q : ℝ) (w lam : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hdiag : ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
      0 ≤ diagKernel m r q ell) :
    0 ≤ momentKernelTerm m r q (atomicMoment w lam) := by
  rw [← atomicKernelTerm_eq_momentKernelTerm hr hn]
  unfold atomicKernelTerm
  refine atomicIntegral_nonneg_of w lam hw
    (fun x => x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) r (multiKernel m r q) ?_ hlam
  intro L hlen hL
  exact multiKernel_nonneg hr hn q L hlen hdiag hL

/-- Atomic version of the complete expansion: diagonal positivity for every relevant `r` makes the
whole moment defect nonnegative. -/
theorem momentPhi_nonneg_of_atomic {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (q : ℝ) (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hdiag : ∀ r, 1 ≤ r → 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), 0 ≤ diagKernel m r q ell) :
    0 ≤ momentPhi m q (atomicMoment w lam) := by
  rw [momentPhi_eq_momentKernelExpansion]
  unfold momentKernelExpansion
  refine Finset.sum_nonneg fun k hk => ?_
  have hklt : k < (m - 1) / 2 := Finset.mem_range.mp hk
  have hr1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hrm : 2 * (k + 1) < m := by
    rcases hm with ⟨t, ht⟩
    omega
  have hn : 1 ≤ m - 2 * (k + 1) := by omega
  exact momentKernelTerm_nonneg_of_atomic (r := k + 1) (by omega) hn q w lam hw hlam
    (hdiag (k + 1) hr1 hrm)

end OddCycleBound.HighDensity
