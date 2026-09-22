import Taeyoung.Methods.Bernstein.Univariate

/-!
# Bernstein box certificates in three variables

`Univariate.lean` supplies the one-axis transform `trans` and its linearity.
This file chains it across three axes.  The order is fixed by the proof: axis
`1`, then `2`, then `3`, so no commutation lemma is needed.

The payoff is `nonneg_on_box3`.  Checking a box costs one `decide` on the
computed tensor `trans3` and no symbolic algebra at all -- which is the point,
since elaborating a single explicit 144-term box identity was measured to
exceed 4,000,000 heartbeats.
-/

open Finset

namespace Taeyoung.Methods.Bernstein

variable {ι : Type*}

def bfac (n k : ℕ) (s : ℝ) : ℝ := s ^ k * (1 - s) ^ (n - k)

def trans2 {R : Type*} [CommRing R] (a : ℕ → ℕ → R) (n₁ n₂ : ℕ)
    (l₁ W₁ l₂ W₂ : R) (k₁ k₂ : ℕ) : R :=
  trans (fun i₂ => trans (fun i₁ => a i₁ i₂) n₁ l₁ W₁ k₁) n₂ l₂ W₂ k₂

def trans3 {R : Type*} [CommRing R] (a : ℕ → ℕ → ℕ → R) (n₁ n₂ n₃ : ℕ)
    (l₁ W₁ l₂ W₂ l₃ W₃ : R) (k₁ k₂ k₃ : ℕ) : R :=
  trans (fun i₃ => trans2 (fun i₁ i₂ => a i₁ i₂ i₃) n₁ n₂ l₁ W₁ l₂ W₂ k₁ k₂)
    n₃ l₃ W₃ k₃

theorem trans_of_sum_smul (a : ℕ → ι → ℝ) (c : ι → ℝ) (t : Finset ι)
    (n : ℕ) (l W : ℝ) (k : ℕ) :
    trans (fun i => ∑ j ∈ t, a i j * c j) n l W k
      = ∑ j ∈ t, trans (fun i => a i j) n l W k * c j := by
  rw [trans_sum (fun i j => a i j * c j) t n l W k]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : (fun i => a i j * c j) = fun i => c j * a i j := by funext i; ring
  rw [h, trans_smul (fun i => a i j) (c j) n l W k]
  ring

theorem trans2_of_sum_smul (b : ℕ → ℕ → ι → ℝ) (c : ι → ℝ) (t : Finset ι)
    (n₁ n₂ : ℕ) (l₁ W₁ l₂ W₂ : ℝ) (k₁ k₂ : ℕ) :
    trans2 (fun i₁ i₂ => ∑ j ∈ t, b i₁ i₂ j * c j) n₁ n₂ l₁ W₁ l₂ W₂ k₁ k₂
      = ∑ j ∈ t, trans2 (fun i₁ i₂ => b i₁ i₂ j) n₁ n₂ l₁ W₁ l₂ W₂ k₁ k₂ * c j := by
  simp only [trans2]
  have hin : (fun i₂ => trans (fun i₁ => ∑ j ∈ t, b i₁ i₂ j * c j) n₁ l₁ W₁ k₁)
      = fun i₂ => ∑ j ∈ t, trans (fun i₁ => b i₁ i₂ j) n₁ l₁ W₁ k₁ * c j :=
    funext fun i₂ => trans_of_sum_smul (fun i₁ j => b i₁ i₂ j) c t n₁ l₁ W₁ k₁
  rw [hin]
  exact trans_of_sum_smul
    (fun i₂ j => trans (fun i₁ => b i₁ i₂ j) n₁ l₁ W₁ k₁) c t n₂ l₂ W₂ k₂

theorem sum_trans2 (a : ℕ → ℕ → ℝ) (n₁ n₂ : ℕ) (l₁ W₁ l₂ W₂ s₁ s₂ : ℝ) :
    ∑ i₁ ∈ range (n₁ + 1),
        (∑ i₂ ∈ range (n₂ + 1), a i₁ i₂ * (l₂ + W₂ * s₂) ^ i₂) * (l₁ + W₁ * s₁) ^ i₁
      = ∑ k₁ ∈ range (n₁ + 1),
          (∑ k₂ ∈ range (n₂ + 1),
            trans2 a n₁ n₂ l₁ W₁ l₂ W₂ k₁ k₂ * bfac n₂ k₂ s₂) * bfac n₁ k₁ s₁ := by
  rw [sum_trans (fun i₁ => ∑ i₂ ∈ range (n₂ + 1), a i₁ i₂ * (l₂ + W₂ * s₂) ^ i₂)
    n₁ l₁ W₁ s₁]
  refine Finset.sum_congr rfl fun k₁ _ ↦ ?_
  rw [trans_of_sum_smul a (fun i₂ => (l₂ + W₂ * s₂) ^ i₂) (range (n₂ + 1)) n₁ l₁ W₁ k₁]
  rw [sum_trans (fun i₂ => trans (fun i₁ => a i₁ i₂) n₁ l₁ W₁ k₁) n₂ l₂ W₂ s₂]
  simp only [bfac, trans2, mul_assoc]

theorem sum_trans3 (a : ℕ → ℕ → ℕ → ℝ) (n₁ n₂ n₃ : ℕ)
    (l₁ W₁ l₂ W₂ l₃ W₃ s₁ s₂ s₃ : ℝ) :
    ∑ i₁ ∈ range (n₁ + 1),
        (∑ i₂ ∈ range (n₂ + 1),
          (∑ i₃ ∈ range (n₃ + 1), a i₁ i₂ i₃ * (l₃ + W₃ * s₃) ^ i₃)
            * (l₂ + W₂ * s₂) ^ i₂) * (l₁ + W₁ * s₁) ^ i₁
      = ∑ k₁ ∈ range (n₁ + 1),
          (∑ k₂ ∈ range (n₂ + 1),
            (∑ k₃ ∈ range (n₃ + 1),
              trans3 a n₁ n₂ n₃ l₁ W₁ l₂ W₂ l₃ W₃ k₁ k₂ k₃ * bfac n₃ k₃ s₃)
              * bfac n₂ k₂ s₂) * bfac n₁ k₁ s₁ := by
  rw [sum_trans2 (fun i₁ i₂ => ∑ i₃ ∈ range (n₃ + 1), a i₁ i₂ i₃ * (l₃ + W₃ * s₃) ^ i₃)
    n₁ n₂ l₁ W₁ l₂ W₂ s₁ s₂]
  refine Finset.sum_congr rfl fun k₁ _ ↦ ?_
  congr 1
  refine Finset.sum_congr rfl fun k₂ _ ↦ ?_
  rw [trans2_of_sum_smul a (fun i₃ => (l₃ + W₃ * s₃) ^ i₃) (range (n₃ + 1))
    n₁ n₂ l₁ W₁ l₂ W₂ k₁ k₂]
  rw [sum_trans (fun i₃ => trans2 (fun i₁ i₂ => a i₁ i₂ i₃) n₁ n₂ l₁ W₁ l₂ W₂ k₁ k₂)
    n₃ l₃ W₃ s₃]
  simp only [bfac, trans3, mul_assoc]

/-! ### The certificate -/

theorem bfac_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n k : ℕ) :
    0 ≤ bfac n k s := term_nonneg hs0 hs1 n k

/-- **The three-variable box certificate.**  If every entry of the computed
tensor `trans3` is nonnegative, the polynomial is nonnegative on the box. -/
theorem nonneg_on_box3 (a : ℕ → ℕ → ℕ → ℝ) (n₁ n₂ n₃ : ℕ)
    {l₁ W₁ l₂ W₂ l₃ W₃ x y z : ℝ}
    (hW₁ : 0 < W₁) (hW₂ : 0 < W₂) (hW₃ : 0 < W₃)
    (hx0 : l₁ ≤ x) (hx1 : x ≤ l₁ + W₁)
    (hy0 : l₂ ≤ y) (hy1 : y ≤ l₂ + W₂)
    (hz0 : l₃ ≤ z) (hz1 : z ≤ l₃ + W₃)
    (hc : ∀ k₁ ∈ range (n₁ + 1), ∀ k₂ ∈ range (n₂ + 1), ∀ k₃ ∈ range (n₃ + 1),
      0 ≤ trans3 a n₁ n₂ n₃ l₁ W₁ l₂ W₂ l₃ W₃ k₁ k₂ k₃) :
    0 ≤ ∑ i₁ ∈ range (n₁ + 1),
        (∑ i₂ ∈ range (n₂ + 1),
          (∑ i₃ ∈ range (n₃ + 1), a i₁ i₂ i₃ * z ^ i₃) * y ^ i₂) * x ^ i₁ := by
  set s₁ : ℝ := (x - l₁) / W₁ with hs₁
  set s₂ : ℝ := (y - l₂) / W₂ with hs₂
  set s₃ : ℝ := (z - l₃) / W₃ with hs₃
  have b₁ : 0 ≤ s₁ ∧ s₁ ≤ 1 :=
    ⟨div_nonneg (by linarith) hW₁.le, by rw [hs₁, div_le_one hW₁]; linarith⟩
  have b₂ : 0 ≤ s₂ ∧ s₂ ≤ 1 :=
    ⟨div_nonneg (by linarith) hW₂.le, by rw [hs₂, div_le_one hW₂]; linarith⟩
  have b₃ : 0 ≤ s₃ ∧ s₃ ≤ 1 :=
    ⟨div_nonneg (by linarith) hW₃.le, by rw [hs₃, div_le_one hW₃]; linarith⟩
  have ex : x = l₁ + W₁ * s₁ := by rw [hs₁]; field_simp; ring
  have ey : y = l₂ + W₂ * s₂ := by rw [hs₂]; field_simp; ring
  have ez : z = l₃ + W₃ * s₃ := by rw [hs₃]; field_simp; ring
  rw [ex, ey, ez, sum_trans3 a n₁ n₂ n₃ l₁ W₁ l₂ W₂ l₃ W₃ s₁ s₂ s₃]
  refine Finset.sum_nonneg fun k₁ h₁ ↦ mul_nonneg (Finset.sum_nonneg fun k₂ h₂ ↦
    mul_nonneg (Finset.sum_nonneg fun k₃ h₃ ↦
      mul_nonneg (hc k₁ h₁ k₂ h₂ k₃ h₃) (bfac_nonneg b₃.1 b₃.2 n₃ k₃))
      (bfac_nonneg b₂.1 b₂.2 n₂ k₂)) (bfac_nonneg b₁.1 b₁.2 n₁ k₁)

/-! ### Transport along a ring hom -/

theorem trans2_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : ℕ → ℕ → R) (n₁ n₂ : ℕ) (l₁ W₁ l₂ W₂ : R) (k₁ k₂ : ℕ) :
    f (trans2 a n₁ n₂ l₁ W₁ l₂ W₂ k₁ k₂)
      = trans2 (fun i₁ i₂ => f (a i₁ i₂)) n₁ n₂ (f l₁) (f W₁) (f l₂) (f W₂) k₁ k₂ := by
  simp only [trans2, trans_map]

theorem trans3_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : ℕ → ℕ → ℕ → R) (n₁ n₂ n₃ : ℕ) (l₁ W₁ l₂ W₂ l₃ W₃ : R) (k₁ k₂ k₃ : ℕ) :
    f (trans3 a n₁ n₂ n₃ l₁ W₁ l₂ W₂ l₃ W₃ k₁ k₂ k₃)
      = trans3 (fun i₁ i₂ i₃ => f (a i₁ i₂ i₃)) n₁ n₂ n₃
          (f l₁) (f W₁) (f l₂) (f W₂) (f l₃) (f W₃) k₁ k₂ k₃ := by
  simp only [trans3, trans_map, trans2_map]

/-! ### The rational interface -/

/-- **The box certificate with a rational certificate.**  The tensor `trans3` is
computed over `ℚ`, where its sign test is decidable; the conclusion is over `ℝ`. -/
theorem nonneg_on_box3_rat (a : ℕ → ℕ → ℕ → ℚ) (n₁ n₂ n₃ : ℕ)
    {l₁ W₁ l₂ W₂ l₃ W₃ : ℚ} {x y z : ℝ}
    (hW₁ : 0 < (W₁ : ℝ)) (hW₂ : 0 < (W₂ : ℝ)) (hW₃ : 0 < (W₃ : ℝ))
    (hx0 : (l₁ : ℝ) ≤ x) (hx1 : x ≤ (l₁ : ℝ) + (W₁ : ℝ))
    (hy0 : (l₂ : ℝ) ≤ y) (hy1 : y ≤ (l₂ : ℝ) + (W₂ : ℝ))
    (hz0 : (l₃ : ℝ) ≤ z) (hz1 : z ≤ (l₃ : ℝ) + (W₃ : ℝ))
    (hc : ∀ k₁ ∈ range (n₁ + 1), ∀ k₂ ∈ range (n₂ + 1), ∀ k₃ ∈ range (n₃ + 1),
      0 ≤ trans3 a n₁ n₂ n₃ l₁ W₁ l₂ W₂ l₃ W₃ k₁ k₂ k₃) :
    0 ≤ ∑ i₁ ∈ range (n₁ + 1),
        (∑ i₂ ∈ range (n₂ + 1),
          (∑ i₃ ∈ range (n₃ + 1), ((a i₁ i₂ i₃ : ℚ) : ℝ) * z ^ i₃) * y ^ i₂) * x ^ i₁ := by
  refine nonneg_on_box3 (fun i₁ i₂ i₃ => ((a i₁ i₂ i₃ : ℚ) : ℝ)) n₁ n₂ n₃
    hW₁ hW₂ hW₃ hx0 hx1 hy0 hy1 hz0 hz1 ?_
  intro k₁ h₁ k₂ h₂ k₃ h₃
  have hmap := trans3_map (Rat.castHom ℝ) a n₁ n₂ n₃ l₁ W₁ l₂ W₂ l₃ W₃ k₁ k₂ k₃
  simp only [Rat.coe_castHom] at hmap
  rw [← hmap]
  exact_mod_cast (hc k₁ h₁ k₂ h₂ k₃ h₃)

/-! ### The monomial sum

`msum a n₁ n₂ n₃` is the polynomial whose monomial coefficients are `a`.  Naming it
keeps the generated certificate files readable, and lets each face state one
`ring` identity instead of one per box. -/

/-- The polynomial with rational monomial coefficients `a`, evaluated at reals. -/
noncomputable def msum (a : ℕ → ℕ → ℕ → ℚ) (n₁ n₂ n₃ : ℕ) (x y z : ℝ) : ℝ :=
  ∑ i₁ ∈ range (n₁ + 1),
    (∑ i₂ ∈ range (n₂ + 1),
      (∑ i₃ ∈ range (n₃ + 1), ((a i₁ i₂ i₃ : ℚ) : ℝ) * z ^ i₃) * y ^ i₂) * x ^ i₁

/-- Evaluation of rational monomial tables is additive in the table. -/
theorem msum_add (a b : ℕ → ℕ → ℕ → ℚ) (n₁ n₂ n₃ : ℕ) (x y z : ℝ) :
    msum (fun i j k ↦ a i j k + b i j k) n₁ n₂ n₃ x y z =
      msum a n₁ n₂ n₃ x y z + msum b n₁ n₂ n₃ x y z := by
  simp only [msum, Rat.cast_add, Finset.sum_add_distrib, add_mul]

/-- `nonneg_on_box3_rat` in terms of `msum`. -/
theorem msum_nonneg_on_box (a : ℕ → ℕ → ℕ → ℚ) (n₁ n₂ n₃ : ℕ)
    {l₁ W₁ l₂ W₂ l₃ W₃ : ℚ} {x y z : ℝ}
    (hW₁ : 0 < (W₁ : ℝ)) (hW₂ : 0 < (W₂ : ℝ)) (hW₃ : 0 < (W₃ : ℝ))
    (hx0 : (l₁ : ℝ) ≤ x) (hx1 : x ≤ (l₁ : ℝ) + (W₁ : ℝ))
    (hy0 : (l₂ : ℝ) ≤ y) (hy1 : y ≤ (l₂ : ℝ) + (W₂ : ℝ))
    (hz0 : (l₃ : ℝ) ≤ z) (hz1 : z ≤ (l₃ : ℝ) + (W₃ : ℝ))
    (hc : ∀ k₁ ∈ range (n₁ + 1), ∀ k₂ ∈ range (n₂ + 1), ∀ k₃ ∈ range (n₃ + 1),
      0 ≤ trans3 a n₁ n₂ n₃ l₁ W₁ l₂ W₂ l₃ W₃ k₁ k₂ k₃) :
    0 ≤ msum a n₁ n₂ n₃ x y z :=
  nonneg_on_box3_rat a n₁ n₂ n₃ hW₁ hW₂ hW₃ hx0 hx1 hy0 hy1 hz0 hz1 hc

end Taeyoung.Methods.Bernstein
