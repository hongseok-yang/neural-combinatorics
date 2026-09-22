import Taeyoung.Methods.Bernstein.Box

/-!
# Checking staged Bernstein transforms

The direct `trans3` expression repeats all three affine transforms for every
output coefficient. Here supplied intermediate tables are checked one axis at
a time. The numerical tables are witnesses, not trusted computations.
-/

open Finset

namespace Taeyoung.Methods.Bernstein

/-- Balanced lookup for kernel evaluation. Array access is efficient in native
code but its logical reduction may traverse a linear list. Certificate checks
need only the finitely many in-range entries, checked explicitly below. -/
inductive IntTable where
  | leaf (value : ℤ)
  | node (leftSize : ℕ) (left right : IntTable)

def IntTable.get : IntTable → ℕ → ℤ
  | .leaf value, _ => value
  | .node size left right, i =>
      if i < size then left.get i else right.get (i-size)

structure SparseTerm where
  i : ℕ
  j : ℕ
  k : ℕ
  value : ℚ
  deriving DecidableEq

def singleCoeff (t : SparseTerm) (i j k : ℕ) : ℚ :=
  if i = t.i then if j = t.j then if k = t.k then t.value else 0 else 0 else 0

def sparseCoeff (ts : List SparseTerm) (i j k : ℕ) : ℚ :=
  (ts.map fun t => singleCoeff t i j k).sum

def sparseEval (ts : List SparseTerm) (x y z : ℝ) : ℝ :=
  (ts.map fun t => (t.value : ℝ) * z ^ t.k * y ^ t.j * x ^ t.i).sum

theorem msum_congr_on_range {a b : ℕ → ℕ → ℕ → ℚ} {n₁ n₂ n₃ : ℕ}
    (h : ∀ i ∈ range (n₁+1), ∀ j ∈ range (n₂+1), ∀ k ∈ range (n₃+1),
      a i j k = b i j k) (x y z : ℝ) :
    msum a n₁ n₂ n₃ x y z = msum b n₁ n₂ n₃ x y z := by
  unfold msum
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [h i hi j hj k hk]

theorem msum_single (t : SparseTerm) (n₁ n₂ n₃ : ℕ)
    (hi : t.i ≤ n₁) (hj : t.j ≤ n₂) (hk : t.k ≤ n₃) (x y z : ℝ) :
    msum (singleCoeff t) n₁ n₂ n₃ x y z =
      (t.value : ℝ) * z ^ t.k * y ^ t.j * x ^ t.i := by
  have hi' : t.i ∈ range (n₁+1) := mem_range.mpr (by omega)
  have hj' : t.j ∈ range (n₂+1) := mem_range.mpr (by omega)
  have hk' : t.k ∈ range (n₃+1) := mem_range.mpr (by omega)
  simp [msum, singleCoeff, apply_ite, ite_mul, hi', hj', hk']

theorem msum_sparse (ts : List SparseTerm) (n₁ n₂ n₃ : ℕ)
    (h : ∀ t ∈ ts, t.i ≤ n₁ ∧ t.j ≤ n₂ ∧ t.k ≤ n₃) (x y z : ℝ) :
    msum (sparseCoeff ts) n₁ n₂ n₃ x y z = sparseEval ts x y z := by
  induction ts with
  | nil => simp [msum, sparseCoeff, sparseEval]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hts : ∀ u ∈ ts, u.i ≤ n₁ ∧ u.j ≤ n₂ ∧ u.k ≤ n₃ :=
      fun u hu => h u (by simp [hu])
    have heq : sparseCoeff (t :: ts) = fun i j k =>
        singleCoeff t i j k + sparseCoeff ts i j k := by
      funext i j k
      simp [sparseCoeff]
    rw [heq, msum_add, msum_single t n₁ n₂ n₃ ht.1 ht.2.1 ht.2.2, ih hts]
    simp [sparseEval]

theorem msum_sub (a b : ℕ → ℕ → ℕ → ℚ) (n₁ n₂ n₃ : ℕ) (x y z : ℝ) :
    msum (fun i j k => a i j k - b i j k) n₁ n₂ n₃ x y z =
      msum a n₁ n₂ n₃ x y z - msum b n₁ n₂ n₃ x y z := by
  simp only [msum, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem msum_smul (a : ℕ → ℕ → ℕ → ℚ) (c : ℚ)
    (n₁ n₂ n₃ : ℕ) (x y z : ℝ) :
    msum (fun i j k => c * a i j k) n₁ n₂ n₃ x y z =
      (c : ℝ) * msum a n₁ n₂ n₃ x y z := by
  simp only [msum, Rat.cast_mul, mul_assoc, ← Finset.mul_sum]

structure IntTerm where
  i : ℕ
  j : ℕ
  k : ℕ
  value : ℤ
  deriving DecidableEq

def IntTerm.toRat (t : IntTerm) : SparseTerm := ⟨t.i, t.j, t.k, t.value⟩

def intSingleCoeff (t : IntTerm) (i j k : ℕ) : ℤ :=
  if i = t.i then if j = t.j then if k = t.k then t.value else 0 else 0 else 0

def intSparseCoeff (ts : List IntTerm) (i j k : ℕ) : ℤ :=
  (ts.map fun t => intSingleCoeff t i j k).sum

theorem intSparseCoeff_cast (ts : List IntTerm) (i j k : ℕ) :
    (intSparseCoeff ts i j k : ℚ) = sparseCoeff (ts.map IntTerm.toRat) i j k := by
  induction ts with
  | nil => simp [intSparseCoeff, sparseCoeff]
  | cons t ts ih =>
    simp only [intSparseCoeff, sparseCoeff, List.map_cons, List.sum_cons,
      Int.cast_add] at ih ⊢
    rw [ih]
    congr 1
    by_cases hi : i = t.i <;> by_cases hj : j = t.j <;> by_cases hk : k = t.k <;>
      simp [intSingleCoeff, singleCoeff, IntTerm.toRat, hi, hj, hk]

/-- Clear the coefficient denominator before checking the sparse table.
Only integer additions and equality tests remain in the numerical obligation. -/
theorem msum_intSparse_scaled
    (a : ℕ → ℕ → ℕ → ℤ) (ts : List IntTerm) (den : ℚ)
    (n₁ n₂ n₃ : ℕ)
    (he : ∀ i ∈ range (n₁+1), ∀ j ∈ range (n₂+1), ∀ k ∈ range (n₃+1),
      a i j k = intSparseCoeff ts i j k)
    (hb : ∀ t ∈ ts, t.i ≤ n₁ ∧ t.j ≤ n₂ ∧ t.k ≤ n₃)
    (x y z : ℝ) :
    msum (fun i j k => (a i j k : ℚ) / den) n₁ n₂ n₃ x y z =
      sparseEval (ts.map IntTerm.toRat) x y z / (den : ℝ) := by
  have htable : ∀ i ∈ range (n₁+1), ∀ j ∈ range (n₂+1), ∀ k ∈ range (n₃+1),
      (a i j k : ℚ) / den = den⁻¹ * sparseCoeff (ts.map IntTerm.toRat) i j k := by
    intro i hi j hj k hk
    rw [he i hi j hj k hk, intSparseCoeff_cast, div_eq_mul_inv, mul_comm]
  have hb' : ∀ t ∈ ts.map IntTerm.toRat, t.i ≤ n₁ ∧ t.j ≤ n₂ ∧ t.k ≤ n₃ := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hb s hs
  rw [msum_congr_on_range htable x y z, msum_smul,
    msum_sparse (ts.map IntTerm.toRat) n₁ n₂ n₃ hb']
  push_cast
  ring

def transWeight {R : Type*} [CommRing R] (n : ℕ) (l w : R) (k i : ℕ) : R :=
  ∑ r ∈ range (k + 1),
    ((i.choose r : R) * l ^ (i - r) * w ^ r) * ((n - r).choose (k - r) : R)

/-- Denominator-cleared affine Bernstein weights. The common denominator is
`q^n`; checking these integers avoids a rational gcd at every summand. -/
def intTransWeight (n : ℕ) (l w q : ℤ) (k i : ℕ) : ℤ :=
  ∑ r ∈ range (k+1),
    ((i.choose r : ℤ)*l^(i-r)*w^r*q^(n-i))*((n-r).choose (k-r) : ℤ)

private theorem intTransWeight_term (n k i r : ℕ) (l w q : ℤ)
    (hi : i ≤ n) (hr : r ≤ i) (hq : (q : ℚ) ≠ 0) :
    (((i.choose r : ℤ)*l^(i-r)*w^r*q^(n-i)*((n-r).choose (k-r) : ℤ) : ℤ) : ℚ) /
      (q : ℚ)^n =
      ((i.choose r : ℚ)*((l : ℚ)/q)^(i-r)*((w : ℚ)/q)^r)*
        ((n-r).choose (k-r) : ℚ) := by
  have hp : (q : ℚ)^(i-r)*(q : ℚ)^r*(q : ℚ)^(n-i) = (q : ℚ)^n := by
    rw [← pow_add, Nat.sub_add_cancel hr, ← pow_add, Nat.add_sub_of_le hi]
  push_cast
  rw [div_pow, div_pow, ← hp]
  field_simp

theorem intTransWeight_cast (n : ℕ) (l w q : ℤ) (k i : ℕ)
    (hi : i ≤ n) (hq : (q : ℚ) ≠ 0) :
    (intTransWeight n l w q k i : ℚ)/(q : ℚ)^n =
      transWeight n ((l : ℚ)/q) ((w : ℚ)/q) k i := by
  simp only [intTransWeight, transWeight, Int.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hri : r ≤ i
  · simpa only [div_eq_mul_inv] using intTransWeight_term n k i r l w q hi hri hq
  · have hz : i.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hz, Nat.cast_zero, zero_mul, Int.cast_zero]

theorem trans_eq_sum_weight {R : Type*} [CommRing R]
    (a : ℕ → R) (n : ℕ) (l w : R) (k : ℕ) :
    trans a n l w k = ∑ i ∈ range (n + 1), a i * transWeight n l w k i := by
  simp only [trans, coeff, shift, transWeight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem trans_congr_on_range {R : Type*} [CommRing R]
    {a b : ℕ → R} {n : ℕ} (h : ∀ i ∈ range (n + 1), a i = b i)
    (l w : R) (k : ℕ) : trans a n l w k = trans b n l w k := by
  rw [trans_eq_sum_weight, trans_eq_sum_weight]
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

/-- A small matrix supplied for one axis is checked independently of the
coefficient tensor to which it will be applied. -/
abbrev WeightsCorrect (n : ℕ) (l w : ℚ) (weights : ℕ → ℕ → ℚ) : Prop :=
  ∀ k ∈ range (n + 1), ∀ i ∈ range (n + 1),
    weights k i = transWeight n l w k i

abbrev Axis1Correct (n₁ n₂ n₃ : ℕ) (weights : ℕ → ℕ → ℚ)
    (a b : ℕ → ℕ → ℕ → ℚ) : Prop :=
  ∀ k ∈ range (n₁ + 1), ∀ j ∈ range (n₂ + 1), ∀ h ∈ range (n₃ + 1),
    b k j h = ∑ i ∈ range (n₁ + 1), a i j h * weights k i

abbrev Axis2Correct (n₁ n₂ n₃ : ℕ) (weights : ℕ → ℕ → ℚ)
    (a b : ℕ → ℕ → ℕ → ℚ) : Prop :=
  ∀ k ∈ range (n₁ + 1), ∀ j ∈ range (n₂ + 1), ∀ h ∈ range (n₃ + 1),
    b k j h = ∑ i ∈ range (n₂ + 1), a k i h * weights j i

abbrev Axis3Correct (n₁ n₂ n₃ : ℕ) (weights : ℕ → ℕ → ℚ)
    (a b : ℕ → ℕ → ℕ → ℚ) : Prop :=
  ∀ k ∈ range (n₁ + 1), ∀ j ∈ range (n₂ + 1), ∀ h ∈ range (n₃ + 1),
    b k j h = ∑ i ∈ range (n₃ + 1), a k j i * weights h i

/-- Check the input table once, then reuse its entries in every row of the
first matrix product instead of expanding a sparse polynomial repeatedly. -/
theorem axis1Correct_of_table
    {n₁ n₂ n₃ : ℕ} {weights : ℕ → ℕ → ℚ}
    {a table b : ℕ → ℕ → ℕ → ℚ}
    (htable : ∀ i ∈ range (n₁+1), ∀ j ∈ range (n₂+1), ∀ k ∈ range (n₃+1),
      table i j k = a i j k)
    (hb : Axis1Correct n₁ n₂ n₃ weights table b) :
    Axis1Correct n₁ n₂ n₃ weights a b := by
  intro k hk j hj h hh
  rw [hb k hk j hj h hh]
  exact Finset.sum_congr rfl fun i hi => by rw [htable i hi j hj h hh]

/-- Integer matrix products with one denominator for each table. This avoids
normalizing a rational number after every multiply-add in a certificate. -/
theorem scaled_dot_eq (a w : ℕ → ℤ) (b : ℤ) (da dw : ℚ) (n : ℕ)
    (h : b = ∑ i ∈ range (n+1), a i * w i) :
    (b : ℚ) / (da*dw) =
      ∑ i ∈ range (n+1), ((a i : ℚ)/da)*((w i : ℚ)/dw) := by
  rw [h, Int.cast_sum]
  simp only [Int.cast_mul, div_eq_mul_inv, Finset.sum_mul, mul_inv_rev]
  exact Finset.sum_congr rfl fun i hi => by ring

theorem checked_trans3
    (a b c e : ℕ → ℕ → ℕ → ℚ) (n₁ n₂ n₃ : ℕ)
    (l₁ w₁ l₂ w₂ l₃ w₃ : ℚ) (v₁ v₂ v₃ : ℕ → ℕ → ℚ)
    (hv₁ : WeightsCorrect n₁ l₁ w₁ v₁)
    (hv₂ : WeightsCorrect n₂ l₂ w₂ v₂)
    (hv₃ : WeightsCorrect n₃ l₃ w₃ v₃)
    (hb : Axis1Correct n₁ n₂ n₃ v₁ a b)
    (hc : Axis2Correct n₁ n₂ n₃ v₂ b c)
    (he : Axis3Correct n₁ n₂ n₃ v₃ c e) :
    ∀ k ∈ range (n₁ + 1), ∀ j ∈ range (n₂ + 1), ∀ h ∈ range (n₃ + 1),
      e k j h = trans3 a n₁ n₂ n₃ l₁ w₁ l₂ w₂ l₃ w₃ k j h := by
  have hb' : ∀ k ∈ range (n₁ + 1), ∀ j ∈ range (n₂ + 1),
      ∀ h ∈ range (n₃ + 1), b k j h = trans (fun i => a i j h) n₁ l₁ w₁ k := by
    intro k hk j hj h hh
    rw [hb k hk j hj h hh, trans_eq_sum_weight]
    exact Finset.sum_congr rfl fun i hi => by rw [hv₁ k hk i hi]
  have hc' : ∀ k ∈ range (n₁ + 1), ∀ j ∈ range (n₂ + 1),
      ∀ h ∈ range (n₃ + 1),
      c k j h = trans2 (fun i j => a i j h) n₁ n₂ l₁ w₁ l₂ w₂ k j := by
    intro k hk j hj h hh
    rw [hc k hk j hj h hh, trans2, trans_eq_sum_weight]
    exact Finset.sum_congr rfl fun i hi => by rw [hv₂ j hj i hi, hb' k hk i hi h hh]
  intro k hk j hj h hh
  rw [he k hk j hj h hh, trans3, trans_eq_sum_weight]
  exact Finset.sum_congr rfl fun i hi => by rw [hv₃ h hh i hi, hc' k hk j hj i hi]

end Taeyoung.Methods.Bernstein
