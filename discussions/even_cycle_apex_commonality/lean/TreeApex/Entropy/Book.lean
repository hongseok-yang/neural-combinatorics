import TreeApex.Entropy.Triangle
import TreeApex.Entropy.TreeLaw

/-!
# Conditionally independent pages of a book (paper `lem:book`), weighted

Plan §2.4.  On a host with `R > 0` and `k = j + 1` pages, the book law of `(Z₁..Z_k, X, Y)` is

```
  Q(z⃗, x, y) = P₂(x, y) ∏ᵢ (w_{zᵢ} M_{x zᵢ} M_{y zᵢ} / cod(x, y))
             = w_x w_y M_xy ∏ᵢ w_{zᵢ} M_{x zᵢ} M_{y zᵢ} / (R cod(x, y)^j)          (bookQ)
```

(given the shared edge `(X, Y)`, the pages are independent apices of the triangle).  It is a
`SymLaw` (`bookLaw`) with the reference factors `ρ_S(z⃗) = ∏ w_{zᵢ}`, `ν(z⃗, x) = w_x ∏ M_{x zᵢ}`,
`η = M` (`bookRef`), whose tree weights are the weights of `T^{+k}`.

* `relEnt_book` (**B1**, `eq:book-entropy` as an identity): `relEnt ρ_B Q = log R + j h`.
* `g_eq`: `g = j h + ∑ μ log Φ` with `Φ(z⃗, x) = μ(z⃗, x) R / (ρ_S(z⃗) ν(z⃗, x))`.
* `pages_kl` (`eq:pages-mi` in `KL` form): `∑ μ log Φ ≥ k h − j A`, from one `KL ≥ 0` between the
  law `μ` of `(Z⃗, X)` and the law `w_x ∏ᵢ (w_{zᵢ} M_{x zᵢ} cod(x, zᵢ)) / (R tri(x)^j)` (independent
  pages given `X`, each with the triangle's conditional law).
* `g_ge` (**B2**, `eq:book-extension`): `g ≥ k log R − log E − j log D`.
-/

open Finset

namespace TreeApex

namespace ProbHost

variable {V : Type*} [Fintype V] (K : ProbHost V)

/-! ### Products over the pages -/

/-- `∑_{z⃗} ∏ᵢ c(zᵢ) = (∑ c)^n`. -/
lemma sum_pages_prod {n : ℕ} (c : V → ℝ) : ∑ s : Fin n → V, ∏ i, c (s i) = (∑ z, c z) ^ n := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (z : V) => c z)]
  simp

/-- `∑_{z⃗} ∏ᵢ c(zᵢ) F(z_{i₀}) = (∑ c F) (∑ c)^j`: one distinguished page. -/
lemma sum_pages_prod_mul {j : ℕ} (c F : V → ℝ) (i₀ : Fin (j + 1)) :
    ∑ s : Fin (j + 1) → V, (∏ i, c (s i)) * F (s i₀) = (∑ z, c z * F z) * (∑ z, c z) ^ j := by
  have h := Fintype.prod_sum (fun (i : Fin (j + 1)) (z : V) => c z * if i = i₀ then F z else 1)
  rw [Fin.prod_univ_succAbove _ i₀] at h
  simp only [if_pos, mul_one, (Fin.succAbove_ne i₀ _), if_false, prod_const, card_univ,
    Fintype.card_fin] at h
  rw [h]
  refine sum_congr rfl fun s _ => ?_
  rw [prod_mul_distrib, prod_ite_eq' univ i₀ (fun i => F (s i))]
  simp

/-! ### The book law -/

variable (j : ℕ)

/-- The page weight `∏ᵢ w_{zᵢ} M_{x zᵢ} M_{y zᵢ}`. -/
noncomputable def pageWeight (s : Fin (j + 1) → V) (x y : V) : ℝ :=
  ∏ i, (K.w (s i) * K.M x (s i) * K.M y (s i))

/-- The numerator `w_x w_y M_xy ∏ᵢ w_{zᵢ} M_{x zᵢ} M_{y zᵢ}` of the book law (`= ρ_B`). -/
noncomputable def bookNum (s : Fin (j + 1) → V) (x y : V) : ℝ :=
  K.w x * K.w y * K.M x y * K.pageWeight j s x y

/-- **The book law** `Q(z⃗, x, y) = bookNum / (R cod(x,y)^j)`. -/
noncomputable def bookQ (s : Fin (j + 1) → V) (x y : V) : ℝ :=
  K.bookNum j s x y / (K.R * K.cod x y ^ j)

lemma pageWeight_nonneg (s : Fin (j + 1) → V) (x y : V) : 0 ≤ K.pageWeight j s x y :=
  prod_nonneg fun _ _ => mul_nonneg (mul_nonneg (K.w_nonneg _) (K.M_nonneg _ _)) (K.M_nonneg _ _)

lemma bookNum_nonneg (s : Fin (j + 1) → V) (x y : V) : 0 ≤ K.bookNum j s x y :=
  mul_nonneg (mul_nonneg (mul_nonneg (K.w_nonneg x) (K.w_nonneg y)) (K.M_nonneg x y))
    (K.pageWeight_nonneg j s x y)

lemma bookQ_nonneg (s : Fin (j + 1) → V) (x y : V) : 0 ≤ K.bookQ j s x y :=
  div_nonneg (K.bookNum_nonneg j s x y) (mul_nonneg K.R_nonneg (pow_nonneg (K.cod_nonneg x y) j))

lemma bookQ_symm (s : Fin (j + 1) → V) (x y : V) : K.bookQ j s x y = K.bookQ j s y x := by
  simp only [bookQ, bookNum, pageWeight, K.M_symm x y, K.cod_symm x y]
  congr 1
  rw [show K.w x * K.w y = K.w y * K.w x from mul_comm _ _]
  congr 1
  exact prod_congr rfl fun i _ => by ring

lemma sum_pageWeight (x y : V) : ∑ s, K.pageWeight j s x y = K.cod x y ^ (j + 1) :=
  sum_pages_prod fun z => K.w z * K.M x z * K.M y z

/-- Moving the sum over the pages inside. -/
lemma sum_pages_swap {M : Type*} [AddCommMonoid M] (f : (Fin (j + 1) → V) → V → V → M) :
    ∑ s, ∑ x, ∑ y, f s x y = ∑ x, ∑ y, ∑ s, f s x y := by
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_comm

/-- Summing out the pages leaves the pair marginal `P₂` of the triangle. -/
lemma sum_bookQ_pages (x y : V) : ∑ s, K.bookQ j s x y = K.P₂ x y := by
  simp only [bookQ, bookNum, ← sum_div, ← mul_sum, sum_pageWeight, P₂]
  by_cases hc : K.cod x y = 0
  · simp [hc]
  · rw [pow_succ]
    by_cases hR : K.R = 0
    · simp [hR]
    · field_simp

lemma bookQ_support {s : Fin (j + 1) → V} {x y : V} (h : K.bookQ j s x y ≠ 0) :
    K.w x ≠ 0 ∧ K.w y ≠ 0 ∧ K.M x y ≠ 0 ∧ (∀ i, K.w (s i) * K.M x (s i) * K.M y (s i) ≠ 0) ∧
      K.R ≠ 0 ∧ K.cod x y ≠ 0 := by
  simp only [bookQ, bookNum, pageWeight, div_ne_zero_iff, mul_ne_zero_iff, prod_ne_zero_iff,
    mem_univ, true_implies] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, -⟩ := h
  refine ⟨h1, h2, h3, fun i => mul_ne_zero (mul_ne_zero (h4 i).1.1 (h4 i).1.2) (h4 i).2, h5, ?_⟩
  exact (K.cod_pos_of (z := s 0) (mul_ne_zero (mul_ne_zero (h4 0).1.1 (h4 0).1.2) (h4 0).2)).ne'

/-- The book law as a symmetric law of `(Z⃗, X, Y)`. -/
noncomputable def bookLaw (hR : 0 < K.R) : SymLaw (Fin (j + 1) → V) V where
  Q := K.bookQ j
  nonneg := K.bookQ_nonneg j
  sum_eq := by
    rw [sum_pages_swap]
    simp only [sum_bookQ_pages]
    exact K.sum_sum_P₂ hR
  symm := K.bookQ_symm j

/-- The reference factors of `T^{+k}`: `ρ_S = ∏ w_{zᵢ}`, `ν(z⃗, x) = w_x ∏ M_{x zᵢ}`, `η = M`. -/
noncomputable def bookRef (hR : 0 < K.R) : RefFactors (K.bookLaw j hR) where
  ρS s := ∏ i, K.w (s i)
  ν s x := K.w x * ∏ i, K.M x (s i)
  η := K.M
  ρS_nonneg s := prod_nonneg fun _ _ => K.w_nonneg _
  ν_nonneg s x := mul_nonneg (K.w_nonneg x) (prod_nonneg fun _ _ => K.M_nonneg _ _)
  η_nonneg := K.M_nonneg
  supp s x y h := by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := K.bookQ_support j h
    simp only [mul_ne_zero_iff] at h4
    refine ⟨prod_ne_zero_iff.mpr fun i _ => (h4 i).1.1, mul_ne_zero h1
      (prod_ne_zero_iff.mpr fun i _ => (h4 i).1.2), mul_ne_zero h2
      (prod_ne_zero_iff.mpr fun i _ => (h4 i).2), h3⟩

variable {K j}

lemma bookLaw_Q (hR : 0 < K.R) : (K.bookLaw j hR).Q = K.bookQ j := rfl

lemma bookWeight_eq (hR : 0 < K.R) (q : (Fin (j + 1) → V) × V × V) :
    (K.bookRef j hR).bookWeight q = K.bookNum j q.1 q.2.1 q.2.2 := by
  simp only [RefFactors.bookWeight, bookRef, bookNum, pageWeight, prod_mul_distrib]
  ring

variable (K j)

/-- **B1** (`eq:book-entropy`, as an identity): `relEnt ρ_B Q = log R + j h`. -/
theorem relEnt_book (hR : 0 < K.R) :
    relEnt (K.bookRef j hR).bookWeight
        (fun q : (Fin (j + 1) → V) × V × V => (K.bookLaw j hR).Q q.1 q.2.1 q.2.2)
      = Real.log K.R + j * K.h := by
  rw [relEnt_congr (fun q => Real.log K.R + j * Real.log (K.cod q.2.1 q.2.2)) fun q hq => by
    obtain ⟨-, -, -, -, h5, h6⟩ := K.bookQ_support j hq
    have hn : K.bookNum j q.1 q.2.1 q.2.2 ≠ 0 := by
      intro h0; apply hq; simp [bookLaw_Q, bookQ, h0]
    rw [bookWeight_eq, bookLaw_Q, bookQ, div_div_cancel₀ hn, Real.log_mul h5 (pow_ne_zero _ h6),
      Real.log_pow]]
  simp only [mul_add, sum_add_distrib, ← sum_mul, Fintype.sum_prod_type]
  have h1 : ∑ s, ∑ x, ∑ y, (K.bookLaw j hR).Q s x y = 1 := (K.bookLaw j hR).sum_eq
  have h2 : ∑ s, ∑ x, ∑ y, (K.bookLaw j hR).Q s x y * (j * Real.log (K.cod x y)) = j * K.h := by
    rw [sum_pages_swap]
    simp only [← sum_mul, bookLaw_Q, sum_bookQ_pages, h, mul_sum]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  rw [h1, one_mul, h2]

/-- `∑ Q log cod = h`, summing out the pages. -/
lemma sum_bookQ_log_cod (hR : 0 < K.R) :
    ∑ s, ∑ x, ∑ y, (K.bookLaw j hR).Q s x y * Real.log (K.cod x y) = K.h := by
  rw [sum_pages_swap]
  simp only [← sum_mul, bookLaw_Q, sum_bookQ_pages]
  rfl

/-! ### The extension entropy `g` -/

/-- `Φ(z⃗, x) = μ(z⃗, x) R / (ρ_S(z⃗) ν(z⃗, x))`, the weighted `φ` of plan §2.4. -/
noncomputable def bookPhi (hR : 0 < K.R) (s : Fin (j + 1) → V) (x : V) : ℝ :=
  (K.bookLaw j hR).marg s x * K.R / ((K.bookRef j hR).ρS s * (K.bookRef j hR).ν s x)

/-- **`g = j h + ∑ μ log Φ`.** -/
theorem g_eq (hR : 0 < K.R) :
    (K.bookLaw j hR).condRelEnt (K.bookRef j hR)
      = j * K.h + ∑ s, ∑ x, (K.bookLaw j hR).marg s x * Real.log (K.bookPhi j hR s x) := by
  have hterm : ∀ s x, (K.bookLaw j hR).marg s x * relEnt
      (fun y => (K.bookRef j hR).ν s y * (K.bookRef j hR).η x y) ((K.bookLaw j hR).kern s x)
      = (K.bookLaw j hR).marg s x * Real.log (K.bookPhi j hR s x)
        + j * ∑ y, (K.bookLaw j hR).Q s x y * Real.log (K.cod x y) := by
    intro s x
    by_cases hm : (K.bookLaw j hR).marg s x = 0
    · simp [hm, (K.bookLaw j hR).Q_eq_zero_of_marg hm]
    rw [relEnt_congr (fun y => Real.log (K.bookPhi j hR s x) + j * Real.log (K.cod x y))
      fun y hy => by
        have hQ := (K.bookLaw j hR).Q_ne_zero_of_kern hy
        obtain ⟨hρ, hνx, hνy, hη⟩ := (K.bookRef j hR).supp s x y hQ
        obtain ⟨-, -, -, -, h5, h6⟩ := K.bookQ_support j hQ
        have hQe : (K.bookLaw j hR).Q s x y = (K.bookRef j hR).ρS s * (K.bookRef j hR).ν s x
            * (K.bookRef j hR).ν s y * (K.bookRef j hR).η x y / (K.R * K.cod x y ^ j) := by
          rw [bookLaw_Q, bookQ, ← bookWeight_eq hR (s, x, y)]
          rfl
        have hΦ : K.bookPhi j hR s x ≠ 0 :=
          div_ne_zero (mul_ne_zero hm h5) (mul_ne_zero hρ hνx)
        rw [show (K.bookRef j hR).ν s y * (K.bookRef j hR).η x y / (K.bookLaw j hR).kern s x y
            = K.bookPhi j hR s x * K.cod x y ^ j by
          rw [SymLaw.kern, hQe, bookPhi]
          field_simp,
          Real.log_mul hΦ (pow_ne_zero _ h6), Real.log_pow]]
    simp only [mul_add, sum_add_distrib, ← sum_mul, (K.bookLaw j hR).sum_kern hm, one_mul,
      ← mul_assoc, (K.bookLaw j hR).marg_mul_kern, mul_sum]
    exact congrArg _ (sum_congr rfl fun y _ => by ring)
  unfold SymLaw.condRelEnt
  simp only [hterm, sum_add_distrib, ← mul_sum]
  rw [K.sum_bookQ_log_cod j hR]
  ring

/-- Summing out the pages of `Q` against a function of one page. -/
lemma sum_bookQ_page (i₀ : Fin (j + 1)) (f : V → V → ℝ) (x y : V) :
    ∑ s, K.bookQ j s x y * f x (s i₀)
      = K.w x * K.w y * K.M x y * (∑ z, K.w z * K.M x z * K.M y z * f x z) / K.R := by
  have hpages := sum_pages_prod_mul (fun z => K.w z * K.M x z * K.M y z) (fun z => f x z) i₀
  have hl : ∑ s, K.bookQ j s x y * f x (s i₀)
      = K.w x * K.w y * K.M x y / (K.R * K.cod x y ^ j)
        * ∑ s : Fin (j + 1) → V, (∏ i, (K.w (s i) * K.M x (s i) * K.M y (s i))) * f x (s i₀) := by
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    simp only [bookQ, bookNum, pageWeight]
    ring
  rw [hl, hpages]
  have hcod : ∑ z, K.w z * K.M x z * K.M y z = K.cod x y := rfl
  rw [hcod]
  by_cases hc : K.cod x y = 0
  · have hz : ∀ z, K.w z * K.M x z * K.M y z = 0 := fun z =>
      (sum_eq_zero_iff_of_nonneg fun z _ => mul_nonneg (mul_nonneg (K.w_nonneg z)
        (K.M_nonneg x z)) (K.M_nonneg y z)).mp hc z (mem_univ z)
    simp [hz]
  · by_cases hR : K.R = 0
    · simp [hR]
    · field_simp

/-- **Each page has the triangle's pair law**: `∑_{z⃗,x} μ(z⃗, x) f(x, z_{i₀}) = ∑ P₂ f`. -/
lemma sum_marg_page (hR : 0 < K.R) (i₀ : Fin (j + 1)) (f : V → V → ℝ) :
    ∑ s, ∑ x, (K.bookLaw j hR).marg s x * f x (s i₀) = ∑ x, ∑ z, K.P₂ x z * f x z := by
  simp only [SymLaw.marg, bookLaw_Q, sum_mul]
  rw [sum_pages_swap]
  simp only [K.sum_bookQ_page j i₀ f]
  refine sum_congr rfl fun x _ => ?_
  simp only [P₂, cod, mul_sum, sum_div, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => sum_congr rfl fun y _ => ?_
  rw [K.M_symm y z]
  ring

/-- `∑_{z⃗} μ(z⃗, x) = P₁(x)`. -/
lemma sum_marg_pages (hR : 0 < K.R) (x : V) : ∑ s, (K.bookLaw j hR).marg s x = K.P₁ x := by
  simp only [SymLaw.marg, bookLaw_Q]
  rw [sum_comm]
  simp only [sum_bookQ_pages, sum_P₂]

/-- The support of the `(Z⃗, X)` marginal of the book law. -/
lemma marg_support (hR : 0 < K.R) {s : Fin (j + 1) → V} {x : V}
    (hm : (K.bookLaw j hR).marg s x ≠ 0) :
    K.w x ≠ 0 ∧ K.R ≠ 0 ∧ K.tri x ≠ 0 ∧ (∀ i, K.w (s i) * K.M x (s i) ≠ 0) ∧
      (∀ i, K.cod x (s i) ≠ 0) := by
  obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero hm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := K.bookQ_support j hy
  refine ⟨h1, h5, (K.tri_pos_of (y := y) (mul_ne_zero (mul_ne_zero h2 h3) h6)).ne',
    fun i => left_ne_zero_of_mul (h4 i), fun i => (K.cod_pos_of (z := y) ?_).ne'⟩
  rw [K.M_symm (s i) y]
  exact mul_ne_zero (mul_ne_zero h2 h3) (right_ne_zero_of_mul (h4 i))

/-- **`eq:pages-mi` in `KL` form**: `∑ μ log Φ ≥ k h − j A`. -/
theorem pages_kl (hR : 0 < K.R) :
    (j + 1) * K.h - j * K.A
      ≤ ∑ s, ∑ x, (K.bookLaw j hR).marg s x * Real.log (K.bookPhi j hR s x) := by
  let μ : (Fin (j + 1) → V) × V → ℝ := fun q => (K.bookLaw j hR).marg q.1 q.2
  let r : (Fin (j + 1) → V) × V → ℝ := fun q =>
    K.w q.2 * (∏ i, K.w (q.1 i) * K.M q.2 (q.1 i) * K.cod q.2 (q.1 i)) / (K.R * K.tri q.2 ^ j)
  have hμ0 : ∀ q, 0 ≤ μ q := fun q => (K.bookLaw j hR).marg_nonneg _ _
  have hμ1 : ∑ q, μ q = 1 := by rw [Fintype.sum_prod_type]; exact (K.bookLaw j hR).sum_marg
  have hr0 : ∀ q, 0 ≤ r q := fun q =>
    div_nonneg (mul_nonneg (K.w_nonneg _) (prod_nonneg fun _ _ => mul_nonneg (mul_nonneg
      (K.w_nonneg _) (K.M_nonneg _ _)) (K.cod_nonneg _ _)))
      (mul_nonneg K.R_nonneg (pow_nonneg (K.tri_nonneg _) _))
  have hr1 : ∑ q, r q = 1 := by
    rw [Fintype.sum_prod_type, sum_comm, ← K.sum_P₁ hR]
    refine sum_congr rfl fun x _ => ?_
    simp only [r, ← sum_div, ← mul_sum]
    rw [sum_pages_prod (fun z => K.w z * K.M x z * K.cod x z)]
    have ht : ∑ z, K.w z * K.M x z * K.cod x z = K.tri x := rfl
    rw [ht, P₁]
    by_cases h0 : K.tri x = 0
    · simp [h0]
    · rw [pow_succ]; field_simp
  have hsupp : ∀ q, μ q ≠ 0 → r q ≠ 0 := fun q hq => by
    obtain ⟨h1, h5, ht, h4, hc⟩ := K.marg_support j hR hq
    exact div_ne_zero (mul_ne_zero h1 (prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (h4 i) (hc i))) (mul_ne_zero h5 (pow_ne_zero _ ht))
  have hKL := relEnt_nonpos_of_law hμ0 hμ1 hr0 hr1 hsupp
  rw [relEnt_congr (fun q => (∑ i, Real.log (K.cod q.2 (q.1 i))) - j * Real.log (K.tri q.2)
      - Real.log (K.bookPhi j hR q.1 q.2)) fun q hq => by
    obtain ⟨h1, h5, ht, h4, hc⟩ := K.marg_support j hR hq
    have hρνe : (K.bookRef j hR).ρS q.1 * (K.bookRef j hR).ν q.1 q.2
        = K.w q.2 * ((∏ i, K.w (q.1 i)) * ∏ i, K.M q.2 (q.1 i)) := by
      simp only [bookRef]; ring
    have hw : ∏ i, K.w (q.1 i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => left_ne_zero_of_mul (h4 i)
    have hM : ∏ i, K.M q.2 (q.1 i) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i _ => right_ne_zero_of_mul (h4 i)
    have hΦe : K.bookPhi j hR q.1 q.2 = μ q * K.R
        / (K.w q.2 * ((∏ i, K.w (q.1 i)) * ∏ i, K.M q.2 (q.1 i))) := by
      rw [bookPhi, hρνe]
    have hΦ : K.bookPhi j hR q.1 q.2 ≠ 0 := by
      rw [hΦe]; exact div_ne_zero (mul_ne_zero hq h5) (mul_ne_zero h1 (mul_ne_zero hw hM))
    have hprod : ∏ i, K.cod q.2 (q.1 i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hc i
    have hre : r q = K.w q.2 * ((∏ i, K.w (q.1 i)) * ∏ i, K.M q.2 (q.1 i))
        * (∏ i, K.cod q.2 (q.1 i)) / (K.R * K.tri q.2 ^ j) := by
      simp only [r, prod_mul_distrib]; ring
    rw [show r q / μ q = (∏ i, K.cod q.2 (q.1 i)) / (K.tri q.2 ^ j * K.bookPhi j hR q.1 q.2) by
        rw [hre, hΦe]
        field_simp,
      Real.log_div hprod (mul_ne_zero (pow_ne_zero _ ht) hΦ),
      Real.log_prod fun i _ => hc i, Real.log_mul (pow_ne_zero _ ht) hΦ, Real.log_pow]
    ring] at hKL
  rw [Fintype.sum_prod_type] at hKL
  simp only [μ, mul_sub, sum_sub_distrib, mul_sum] at hKL
  -- the page terms
  have hpage : ∑ s, ∑ x, ∑ i, (K.bookLaw j hR).marg s x * Real.log (K.cod x (s i))
      = (j + 1) * K.h := by
    have hi : ∀ i : Fin (j + 1),
        ∑ s, ∑ x, (K.bookLaw j hR).marg s x * Real.log (K.cod x (s i)) = K.h :=
      fun i => K.sum_marg_page j hR i fun x z => Real.log (K.cod x z)
    have hswap : ∑ s, ∑ x, ∑ i, (K.bookLaw j hR).marg s x * Real.log (K.cod x (s i))
        = ∑ i, ∑ s, ∑ x, (K.bookLaw j hR).marg s x * Real.log (K.cod x (s i)) :=
      (sum_congr rfl fun s _ => sum_comm).trans sum_comm
    rw [hswap]
    simp only [hi, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have htri : ∑ s, ∑ x, (K.bookLaw j hR).marg s x * (j * Real.log (K.tri x)) = j * K.A := by
    rw [sum_comm]
    simp only [← sum_mul, K.sum_marg_pages j hR, A, mul_sum]
    exact sum_congr rfl fun x _ => by ring
  rw [hpage, htri] at hKL
  linarith

/-- **B2** (`eq:book-extension`): `g ≥ k log R − log E − j log D`, `k = j + 1`. -/
theorem g_ge (hR : 0 < K.R) :
    (j + 1) * Real.log K.R - Real.log K.E - j * Real.log K.D
      ≤ (K.bookLaw j hR).condRelEnt (K.bookRef j hR) := by
  rw [K.g_eq j hR]
  have h1 := K.pages_kl j hR
  have h2 := K.h_ge hR
  have h3 := K.I_le hR
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h4 : (j : ℝ) * (Real.log K.R - Real.log K.D) ≤ j * (2 * K.h - K.A) :=
    mul_le_mul_of_nonneg_left (by linarith) hj
  nlinarith

end ProbHost

end TreeApex
