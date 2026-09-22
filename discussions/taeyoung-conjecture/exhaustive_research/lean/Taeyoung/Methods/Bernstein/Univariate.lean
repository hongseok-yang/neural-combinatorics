import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bernstein box certificates

A polynomial of degree at most `n` in `s`, written `∑ i, a i * s ^ i`, can be
rewritten in the *unnormalised Bernstein form*

```
∑ k ∈ range (n+1), coeff a n k * s ^ k * (1 - s) ^ (n - k),
coeff a n k = ∑ i ∈ range (k+1), a i * (n - i).choose (k - i).
```

Both `s ^ k` and `(1 - s) ^ (n - k)` are nonnegative on `[0,1]`, so nonnegative
coefficients prove the polynomial nonnegative there.  That is the entire content
of a Bernstein certificate.

The formulation deliberately avoids the usual normalisation by `n.choose k`.
The classical Bernstein coefficient is `coeff a n k / n.choose k`; dividing
would put rationals where integers suffice.  Keeping the unnormalised form means
a certificate over `ℤ` stays over `ℤ`, which is what makes a kernel check cheap.

On a box the certificate is stated homogeneously in `x - l` and `h - x`, so no
division by the box width occurs either.  `nonneg_of_box` is the three-variable
form, which is the shape every leaf of a subdivision tree has.

## Relation to `Methods/Certificate/Bernstein.lean`

That module carries the certificate *format* — a `decide +kernel`-checkable
list of rational coefficients with multi-indices, and its soundness on the unit
cube.  What it does not carry is the change of basis at arbitrary degree: it
proves `monomial_eq_bernstein_sum_eight` and `..._ten` by `fin_cases`, so only
degrees `8` and `10` are available, and extending that way costs a case split
per monomial.

`sum_eq_coeff` below is that change of basis for *every* degree, by one
application of the binomial theorem.  Atlas 126 needs it: after the note's
`λ = N/g` is cleared of denominators, its region-L residual has degree `18` in
the density parameter, which `fin_cases` would not reach comfortably.  The two
files are meant to be used together — that one for the checked format, this one
for the basis change and the division-free box form.
-/

open Finset

namespace Taeyoung.Methods.Bernstein

/-! ### The unnormalised Bernstein coefficients -/

/-- `coeff a n k = ∑_{i ≤ k} a i · C(n - i, k - i)`. -/
def coeff {R : Type*} [CommRing R] (a : ℕ → R) (n k : ℕ) : R :=
  ∑ i ∈ range (k + 1), a i * ((n - i).choose (k - i) : R)

/-! ### The monomial expansion

`s ^ i = s ^ i · (s + (1 - s)) ^ (n - i)`, expanded by the binomial theorem.
Truncated subtraction makes this hold for every `i` and `n`. -/

/-- **The binomial identity** behind the Bernstein basis. -/
theorem pow_eq_sum {R : Type*} [CommRing R] (n i : ℕ) (s : R) :
    s ^ i = ∑ j ∈ range (n - i + 1),
      ((n - i).choose j : R) * s ^ (i + j) * (1 - s) ^ (n - i - j) := by
  have hb : (s + (1 - s)) ^ (n - i) =
      ∑ j ∈ range (n - i + 1),
        s ^ j * (1 - s) ^ (n - i - j) * ((n - i).choose j : R) :=
    add_pow s (1 - s) (n - i)
  have hone : s + (1 - s) = 1 := by ring
  rw [hone, one_pow] at hb
  calc s ^ i = s ^ i * 1 := (mul_one _).symm
    _ = s ^ i * ∑ j ∈ range (n - i + 1),
          s ^ j * (1 - s) ^ (n - i - j) * ((n - i).choose j : R) := by rw [← hb]
    _ = ∑ j ∈ range (n - i + 1),
          ((n - i).choose j : R) * s ^ (i + j) * (1 - s) ^ (n - i - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [pow_add]
        ring

/-! ### Monomial to Bernstein

Summing `pow_eq_sum` over the monomials gives the change of basis.  The
reindexing `(i, j) ↦ (i, i + j)` is the only bookkeeping involved. -/

theorem sum_eq_coeff {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) (s : R) :
    ∑ i ∈ range (n + 1), a i * s ^ i
      = ∑ k ∈ range (n + 1), coeff a n k * s ^ k * (1 - s) ^ (n - k) := by
  have step : ∀ i ∈ range (n + 1), a i * s ^ i
      = ∑ k ∈ range (n + 1),
          (if i ≤ k then a i * ((n - i).choose (k - i) : R) else 0)
            * s ^ k * (1 - s) ^ (n - k) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hzero : ∀ k ∈ range i,
        (if i ≤ k then a i * ((n - i).choose (k - i) : R) else 0)
          * s ^ k * (1 - s) ^ (n - k) = 0 := by
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [if_neg (by omega : ¬ i ≤ k)]; ring
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le i) (by omega : i ≤ n + 1),
      ← Finset.range_eq_Ico, Finset.sum_eq_zero hzero, zero_add,
      Finset.sum_Ico_eq_sum_range]
    rw [show n + 1 - i = (n - i) + 1 by omega]
    rw [pow_eq_sum n i s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [if_pos (by omega : i ≤ i + j), show i + j - i = j by omega,
      show n - (i + j) = n - i - j by omega]
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← Finset.sum_mul, ← Finset.sum_mul, coeff]
  congr 2
  have hsub : range (k + 1) ⊆ range (n + 1) := by
    intro z hz; simp only [Finset.mem_range] at hz ⊢; omega
  have hvan : ∀ z ∈ range (n + 1), z ∉ range (k + 1) →
      (if z ≤ k then a z * ((n - z).choose (k - z) : R) else 0) = 0 := by
    intro z _ hz
    simp only [Finset.mem_range, not_lt] at hz
    rw [if_neg (by omega : ¬ z ≤ k)]
  rw [← Finset.sum_subset hsub hvan]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  simp only [Finset.mem_range] at hz
  rw [if_pos (by omega : z ≤ k)]

/-! ### Nonnegativity on `[0,1]` -/

/-- Every unnormalised Bernstein term is nonnegative on `[0,1]`. -/
theorem term_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n k : ℕ) :
    0 ≤ s ^ k * (1 - s) ^ (n - k) := by
  have h1 : (0:ℝ) ≤ 1 - s := by linarith
  positivity

/-- **The Bernstein certificate in one variable.** -/
theorem nonneg_of_coeff_nonneg {a : ℕ → ℝ} {n : ℕ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hc : ∀ k ∈ range (n + 1), 0 ≤ coeff a n k) :
    0 ≤ ∑ k ∈ range (n + 1), coeff a n k * s ^ k * (1 - s) ^ (n - k) := by
  refine Finset.sum_nonneg fun k hk ↦ ?_
  have hterm := term_nonneg hs0 hs1 n k
  calc (0:ℝ) ≤ coeff a n k * (s ^ k * (1 - s) ^ (n - k)) :=
        mul_nonneg (hc k hk) hterm
    _ = coeff a n k * s ^ k * (1 - s) ^ (n - k) := by ring

/-! ### The homogeneous form on an interval

On `[l,h]` the certificate is applied to `s = (x - l)/(h - l)`.  Stating it
homogeneously in `x - l` and `h - x` avoids the division: those two
nonnegativities are the only facts used. -/

/-- The homogeneous Bernstein term on `[l,h]`. -/
theorem term_nonneg_interval {x l h : ℝ} (hl : l ≤ x) (hh : x ≤ h) (n k : ℕ) :
    0 ≤ (x - l) ^ k * (h - x) ^ (n - k) := by
  have h1 : (0:ℝ) ≤ x - l := by linarith
  have h2 : (0:ℝ) ≤ h - x := by linarith
  positivity

/-- **A box certificate in one variable.** -/
theorem nonneg_of_homogeneous {c : ℕ → ℝ} {n : ℕ} {x l h : ℝ}
    (hl : l ≤ x) (hh : x ≤ h) (hc : ∀ k ∈ range (n + 1), 0 ≤ c k) :
    0 ≤ ∑ k ∈ range (n + 1), c k * (x - l) ^ k * (h - x) ^ (n - k) := by
  refine Finset.sum_nonneg fun k hk ↦ ?_
  have hterm := term_nonneg_interval hl hh n k
  calc (0:ℝ) ≤ c k * ((x - l) ^ k * (h - x) ^ (n - k)) :=
        mul_nonneg (hc k hk) hterm
    _ = c k * (x - l) ^ k * (h - x) ^ (n - k) := by ring

/-! ### The three-variable box certificate -/

/-- **A box certificate in three variables.**  A polynomial written as a
nonnegative combination of
`(x-l₁)^i (h₁-x)^(n₁-i) · (y-l₂)^j (h₂-y)^(n₂-j) · (z-l₃)^k (h₃-z)^(n₃-k)`
is nonnegative on the box.  This is the shape of every leaf of a subdivision
tree, and the only interface the Atlas rows need. -/
theorem nonneg_of_box {c : ℕ → ℕ → ℕ → ℝ} {n₁ n₂ n₃ : ℕ}
    {x y z l₁ h₁ l₂ h₂ l₃ h₃ : ℝ}
    (hx₁ : l₁ ≤ x) (hx₂ : x ≤ h₁) (hy₁ : l₂ ≤ y) (hy₂ : y ≤ h₂)
    (hz₁ : l₃ ≤ z) (hz₂ : z ≤ h₃)
    (hc : ∀ i ∈ range (n₁ + 1), ∀ j ∈ range (n₂ + 1), ∀ k ∈ range (n₃ + 1),
      0 ≤ c i j k) :
    0 ≤ ∑ i ∈ range (n₁ + 1), ∑ j ∈ range (n₂ + 1), ∑ k ∈ range (n₃ + 1),
        c i j k * ((x - l₁) ^ i * (h₁ - x) ^ (n₁ - i))
                * ((y - l₂) ^ j * (h₂ - y) ^ (n₂ - j))
                * ((z - l₃) ^ k * (h₃ - z) ^ (n₃ - k)) := by
  refine Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦
    Finset.sum_nonneg fun k hk ↦ ?_
  have t₁ := term_nonneg_interval hx₁ hx₂ n₁ i
  have t₂ := term_nonneg_interval hy₁ hy₂ n₂ j
  have t₃ := term_nonneg_interval hz₁ hz₂ n₃ k
  have hcijk := hc i hi j hj k hk
  positivity

/-! ### Affine reparametrisation

A box certificate is applied on `[l, l+W]`, so the coefficients must first be
transported by `x = l + W*s`.  `shift` does that, again by the binomial theorem,
and again computably: no `ring` call is needed per box. -/

/-- Coefficients of `P(l + W*s)` as a polynomial in `s`. -/
def shift {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) (l W : R) (r : ℕ) : R :=
  ∑ i ∈ range (n + 1), a i * ((i.choose r : R) * l ^ (i - r) * W ^ r)

theorem sum_shift {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) (l W s : R) :
    ∑ i ∈ range (n + 1), a i * (l + W * s) ^ i
      = ∑ r ∈ range (n + 1), shift a n l W r * s ^ r := by
  have step : ∀ i ∈ range (n + 1), a i * (l + W * s) ^ i
      = ∑ r ∈ range (n + 1), a i * ((i.choose r : R) * l ^ (i - r) * W ^ r) * s ^ r := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : range (i + 1) ⊆ range (n + 1) := by
      intro z hz; simp only [Finset.mem_range] at hz ⊢; omega
    have hvan : ∀ z ∈ range (n + 1), z ∉ range (i + 1) →
        a i * ((i.choose z : R) * l ^ (i - z) * W ^ z) * s ^ z = 0 := by
      intro z _ hz
      simp only [Finset.mem_range, not_lt] at hz
      rw [Nat.choose_eq_zero_of_lt (by omega : i < z)]
      push_cast; ring
    rw [← Finset.sum_subset hsub hvan]
    have hb : (l + W * s) ^ i
        = ∑ r ∈ range (i + 1), (W * s) ^ r * l ^ (i - r) * (i.choose r : R) :=
      by rw [show l + W * s = W * s + l by ring]; exact add_pow (W * s) l i
    rw [hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [mul_pow]
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [shift, Finset.sum_mul]

/-! ### Linearity

`coeff` and `shift` are linear in the coefficient sequence.  That is what lets
the three variables of a box be handled one at a time: applying the transform in
`x` to a polynomial whose coefficients are polynomials in `(y,z)` is the same as
applying it coefficientwise. -/

variable {ι : Type*}

theorem coeff_sum (f : ℕ → ι → ℝ) (t : Finset ι) (n k : ℕ) :
    coeff (fun i => ∑ j ∈ t, f i j) n k
      = ∑ j ∈ t, coeff (fun i => f i j) n k := by
  simp only [coeff, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem shift_sum (f : ℕ → ι → ℝ) (t : Finset ι) (n : ℕ) (l W : ℝ) (r : ℕ) :
    shift (fun i => ∑ j ∈ t, f i j) n l W r
      = ∑ j ∈ t, shift (fun i => f i j) n l W r := by
  simp only [shift, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem coeff_smul (a : ℕ → ℝ) (c : ℝ) (n k : ℕ) :
    coeff (fun i => c * a i) n k = c * coeff a n k := by
  simp only [coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ by ring

theorem shift_smul (a : ℕ → ℝ) (c : ℝ) (n : ℕ) (l W : ℝ) (r : ℕ) :
    shift (fun i => c * a i) n l W r = c * shift a n l W r := by
  simp only [shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### The one-axis transform

`trans` packages the two computable steps.  Its linearity is what the
multivariate lift consumes: applying it in `x` to a polynomial whose
coefficients are polynomials in the other variables is the same as applying it
coefficientwise. -/

/-- The full one-axis transform: reparametrise to `[l, l+W]`, then change to the
Bernstein basis.  Both steps are computable, so `trans` is. -/
def trans {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) (l W : R) (k : ℕ) : R :=
  coeff (shift a n l W) n k

theorem sum_trans {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) (l W s : R) :
    ∑ i ∈ range (n + 1), a i * (l + W * s) ^ i
      = ∑ k ∈ range (n + 1), trans a n l W k * s ^ k * (1 - s) ^ (n - k) := by
  rw [sum_shift a n l W s, sum_eq_coeff (shift a n l W) n s]
  rfl

theorem trans_sum (f : ℕ → ι → ℝ) (t : Finset ι) (n : ℕ) (l W : ℝ) (k : ℕ) :
    trans (fun i => ∑ j ∈ t, f i j) n l W k
      = ∑ j ∈ t, trans (fun i => f i j) n l W k := by
  have hs : shift (fun i => ∑ j ∈ t, f i j) n l W
      = fun r => ∑ j ∈ t, shift (fun i => f i j) n l W r :=
    funext fun r => shift_sum f t n l W r
  simp only [trans, hs]
  exact coeff_sum (fun r j => shift (fun i => f i j) n l W r) t n k

theorem trans_smul (a : ℕ → ℝ) (c : ℝ) (n : ℕ) (l W : ℝ) (k : ℕ) :
    trans (fun i => c * a i) n l W k = c * trans a n l W k := by
  have hs : shift (fun i => c * a i) n l W = fun r => c * shift a n l W r :=
    funext fun r => shift_smul a c n l W r
  simp only [trans, hs]
  exact coeff_smul (shift a n l W) c n k

/-! ### Transport along a ring hom

The certificate is *computed* over `ℚ`, where the sign test is decidable, and
*used* over `ℝ`.  These lemmas are the bridge. -/

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeff_map (f : R →+* S) (a : ℕ → R) (n k : ℕ) :
    f (coeff a n k) = coeff (fun i => f (a i)) n k := by
  simp only [coeff, map_sum, map_mul, map_natCast]

theorem shift_map (f : R →+* S) (a : ℕ → R) (n : ℕ) (l W : R) (r : ℕ) :
    f (shift a n l W r) = shift (fun i => f (a i)) n (f l) (f W) r := by
  simp only [shift, map_sum, map_mul, map_natCast, map_pow]

theorem trans_map (f : R →+* S) (a : ℕ → R) (n : ℕ) (l W : R) (k : ℕ) :
    f (trans a n l W k) = trans (fun i => f (a i)) n (f l) (f W) k := by
  simp only [trans, coeff_map, shift_map]

/-! ### The certificate, in usable form -/

/-- **The one-variable Bernstein certificate.**  Nonnegative unnormalised
Bernstein coefficients prove a polynomial nonnegative on `[0,1]`.  This is the
form a checker produces: compute `coeff`, test its sign. -/
theorem poly_nonneg_of_coeff_nonneg {a : ℕ → ℝ} {n : ℕ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hc : ∀ k ∈ range (n + 1), 0 ≤ coeff a n k) :
    0 ≤ ∑ i ∈ range (n + 1), a i * s ^ i := by
  rw [sum_eq_coeff a n s]
  exact nonneg_of_coeff_nonneg hs0 hs1 hc

/-- **The one-variable box certificate, composed.**  Transport the coefficients
to `[l, l+W]` with `shift`, take `coeff`, and test the sign.  Both steps are
computable, so a box costs one `decide` and no `ring`. -/
theorem nonneg_on_interval {a : ℕ → ℝ} {n : ℕ} {l W x : ℝ}
    (hW : 0 < W) (hx0 : l ≤ x) (hx1 : x ≤ l + W)
    (hc : ∀ k ∈ range (n + 1), 0 ≤ coeff (shift a n l W) n k) :
    0 ≤ ∑ i ∈ range (n + 1), a i * x ^ i := by
  set s : ℝ := (x - l) / W with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hW.le
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hW]; linarith
  have hxs : x = l + W * s := by
    rw [hs]; field_simp; ring
  rw [hxs]
  have hshift := sum_shift a n l W s
  rw [hshift]
  exact poly_nonneg_of_coeff_nonneg hs0 hs1 hc

/-- **A rational one-variable box certificate.**  The transform is computed
over `ℚ`, where its coefficient signs are decidable, and transported to `ℝ`.
This is the univariate analogue of `nonneg_on_box3_rat`. -/
theorem nonneg_on_interval_rat (a : ℕ → ℚ) (n : ℕ)
    {l W : ℚ} {x : ℝ}
    (hW : 0 < (W : ℝ)) (hx0 : (l : ℝ) ≤ x)
    (hx1 : x ≤ (l : ℝ) + (W : ℝ))
    (hc : ∀ k ∈ range (n + 1), 0 ≤ trans a n l W k) :
    0 ≤ ∑ i ∈ range (n + 1), ((a i : ℚ) : ℝ) * x ^ i := by
  refine nonneg_on_interval (a := fun i => ((a i : ℚ) : ℝ))
    (n := n) (l := (l : ℝ)) (W := (W : ℝ)) hW hx0 hx1 ?_
  intro k hk
  change 0 ≤ trans (fun i => ((a i : ℚ) : ℝ)) n (l : ℝ) (W : ℝ) k
  have hmap := trans_map (Rat.castHom ℝ) a n l W k
  simp only [Rat.coe_castHom] at hmap
  rw [← hmap]
  exact_mod_cast (hc k hk)

end Taeyoung.Methods.Bernstein
