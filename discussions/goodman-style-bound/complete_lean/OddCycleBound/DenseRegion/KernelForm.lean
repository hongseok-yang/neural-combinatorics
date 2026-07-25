/-
# High-density theorem — the finite Beta(r,r) form of the diagonal kernel (M2, `eq:G-form`)

The gateway from the `ρ`-lemma to `diagKernel ≥ 0`.  The paper's `eq:G-form` writes the diagonal
kernel as a **finite** Beta(r,r) expectation (no improper `∫₀^∞`):
`P̃_{m,r}(q,ℓ) = C_{m,r} ∫₀¹ x^{r-1}(1-x)^{r-1}·[(m/n)(Vₓⁿ+Wₓⁿ) − x·Vₓⁿ⁻¹] dx`,
`Vₓ = qx+ℓ(1-x)`, `Wₓ = (1-q)x−ℓ(1-x)`, `n = m−2r`, and the bracket integrand `= xⁿ ρ(Vₓ/x)`.

This file builds `eq:G-form` from `beta_nat` (Beta moments) + the coefficient matching against
`diagKernel_expand`, then reads off `thm:pointwise` (regimes `2r ≥ n` and `ℓ ≤ 0`).
-/

import OddCycleBound.DenseRegion.MixtureIntegral
import OddCycleBound.DenseRegion.RhoLemma

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/-- **Binomial Beta moment.**  Expanding `(c·x + d·(1-x))ᵏ` by the binomial theorem and integrating
against the weight `xᵃ(1-x)ᵇ` termwise via `beta_nat`:
`∫₀¹ xᵃ(1-x)ᵇ(cx+d(1-x))ᵏ = Σ_{i≤k} C(k,i)cⁱd^{k-i}·(a+i)!(b+(k-i))!/((a+i)+(b+(k-i))+1)!`. -/
lemma beta_binom_pow (a b : ℕ) (c d : ℝ) (k : ℕ) :
    (∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ b * (c * x + d * (1 - x)) ^ k)
      = ∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℝ) * c ^ i * d ^ (k - i)
            * ((Nat.factorial (a + i) * Nat.factorial (b + (k - i)) : ℝ)
               / Nat.factorial ((a + i) + (b + (k - i)) + 1)) := by
  have hexp : ∀ x : ℝ, x ^ a * (1 - x) ^ b * (c * x + d * (1 - x)) ^ k
      = ∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℝ) * c ^ i * d ^ (k - i) * (x ^ (a + i) * (1 - x) ^ (b + (k - i))) := by
    intro x
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have e1 : (c * x) ^ i = c ^ i * x ^ i := mul_pow c x i
    have e2 : (d * (1 - x)) ^ (k - i) = d ^ (k - i) * (1 - x) ^ (k - i) := mul_pow d (1 - x) (k - i)
    have e3 : x ^ (a + i) = x ^ a * x ^ i := pow_add x a i
    have e4 : (1 - x) ^ (b + (k - i)) = (1 - x) ^ b * (1 - x) ^ (k - i) := pow_add (1 - x) b (k - i)
    rw [e1, e2, e3, e4]; ring
  rw [intervalIntegral.integral_congr (fun x _ => hexp x),
    intervalIntegral.integral_finsetSum
      (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [intervalIntegral.integral_const_mul, beta_nat (a + i) (b + (k - i))]

/-- **The `hsym` closed form of the Beta moment.**  The binomial Beta moment folds into a single
complete-homogeneous symmetric polynomial: `∫₀¹ xᵃ(1-x)ᵇ(cx+d(1-x))ᵏ = a!b!k!/(a+b+k+1)! ·
h_k(c^{×(a+1)}, d^{×(b+1)})`.  This is the finite analogue of `dirExp_pow` (`eq:dir-moment`); the
per-term identity `C(k,i)(a+i)!(b+(k-i))! = a!b!k!·C(i+a,a)·C((k-i)+b,b)` is the factorial core. -/
lemma beta_hsym (a b : ℕ) (c d : ℝ) (k : ℕ) :
    (∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ b * (c * x + d * (1 - x)) ^ k)
      = (Nat.factorial a * Nat.factorial b * Nat.factorial k : ℝ) / Nat.factorial (a + b + k + 1)
        * hsym (List.replicate (a + 1) c ++ List.replicate (b + 1) d) k := by
  rw [beta_binom_pow a b c d k, hsym_replicate_append_replicate c d b a k, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [show k + 1 - 1 - j = k - j from by omega]
  -- key factorial identity (all in ℕ, cast to ℝ)
  have ha : (Nat.choose (j + a) a : ℝ) * Nat.factorial a * Nat.factorial j = Nat.factorial (a + j) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left a j)
    rw [Nat.add_sub_cancel] at h
    rw [show a + j = j + a from by ring]; exact_mod_cast h
  have hb : (Nat.choose (k - j + b) b : ℝ) * Nat.factorial b * Nat.factorial (k - j)
      = Nat.factorial (b + (k - j)) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left b (k - j))
    rw [Nat.add_sub_cancel] at h
    rw [show b + (k - j) = k - j + b from by ring]; exact_mod_cast h
  have hk : (Nat.choose k j : ℝ) * Nat.factorial j * Nat.factorial (k - j) = Nat.factorial k := by
    have h := Nat.choose_mul_factorial_mul_factorial hj
    exact_mod_cast h
  have key : (Nat.choose k j : ℝ) * Nat.factorial (a + j) * Nat.factorial (b + (k - j))
      = Nat.factorial a * Nat.factorial b * Nat.factorial k
        * (Nat.choose (j + a) a : ℝ) * (Nat.choose (k - j + b) b : ℝ) := by
    rw [← ha, ← hb, ← hk]; ring
  rw [show k - (k - j) = j from by omega]
  rw [show (a + j) + (b + (k - j)) + 1 = a + b + k + 1 from by omega]
  have hne : (Nat.factorial (a + b + k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  linear_combination (c ^ j * d ^ (k - j)) * key

/-- The Beta(r,r)-form constant `C_{m,r} = C(m-1,2r-1)·(n/r)·(2r-1)!/((r-1)!)²`  (`n = m−2r`).
Positive for `r ≥ 1`, `n ≥ 1` (`Cmr_pos`). -/
noncomputable def Cmr (m r : ℕ) : ℝ :=
  (Nat.choose (m - 1) (2 * r - 1) : ℝ) * ((m - 2 * r : ℕ) : ℝ) / (r : ℝ)
    * (Nat.factorial (2 * r - 1) : ℝ) / (Nat.factorial (r - 1) : ℝ) ^ 2

/-- The `C(m-1,2r-1)` factorial cancellation, `n = m−2r`: `C(m-1,2r-1)·(2r-1)!·n! = (m-1)!`. -/
private lemma choose_fact_cancel {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) :
    (Nat.choose (m - 1) (2 * r - 1) : ℝ) * Nat.factorial (2 * r - 1) * Nat.factorial (m - 2 * r)
      = Nat.factorial (m - 1) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 2 * r - 1 ≤ m - 1 from by omega)
  rw [show m - 1 - (2 * r - 1) = m - 2 * r from by omega] at h
  exact_mod_cast h

/-- **Constant identity 1:** `C_{m,r}·(m/n)·K = m/r`, where `K = (r-1)!²·n!/(m-1)!` is the
`beta_hsym` constant for the two `Vₓⁿ, Wₓⁿ` integrals. -/
lemma Cmr_K_eq {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) :
    Cmr m r * ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
        * ((Nat.factorial (r - 1) * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r) : ℝ)
           / Nat.factorial (m - 1))
      = (m : ℝ) / r := by
  have hchoose := choose_fact_cancel (m := m) (r := r) hr hn
  have hnR : ((m - 2 * r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hm1 : (Nat.factorial (m - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hr1f : (Nat.factorial (r - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold Cmr
  field_simp
  linear_combination (m : ℝ) * hchoose

/-- **Constant identity 2:** `C_{m,r}·K₃ = 1`, where `K₃ = r!·(r-1)!·(n-1)!/(m-1)!` is the
`beta_hsym` constant for the `x·Vₓⁿ⁻¹` integral. -/
lemma Cmr_K3_eq {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) :
    Cmr m r * ((Nat.factorial r * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r - 1) : ℝ)
        / Nat.factorial (m - 1))
      = 1 := by
  have hchoose := choose_fact_cancel (m := m) (r := r) hr hn
  have hnR : ((m - 2 * r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hm1 : (Nat.factorial (m - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hr1f : (Nat.factorial (r - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hrfac : (Nat.factorial r : ℝ) = (r : ℝ) * Nat.factorial (r - 1) := by
    exact_mod_cast (Nat.mul_factorial_pred (show r ≠ 0 from hr)).symm
  have hnfac : (Nat.factorial (m - 2 * r) : ℝ) = ((m - 2 * r : ℕ) : ℝ) * Nat.factorial (m - 2 * r - 1) := by
    exact_mod_cast (Nat.mul_factorial_pred (show m - 2 * r ≠ 0 from by omega)).symm
  unfold Cmr
  rw [hnfac] at hchoose
  rw [hrfac]
  field_simp
  linear_combination hchoose

/-- **`eq:G-form` — the finite Beta(r,r) form of the diagonal kernel.**  For `r ≥ 1`, `n = m−2r ≥ 1`:
`P̃_{m,r}(q,ℓ) = C_{m,r} ∫₀¹ x^{r-1}(1-x)^{r-1}[(m/n)(Vₓⁿ+Wₓⁿ) − x·Vₓⁿ⁻¹] dx`,
`Vₓ = qx+ℓ(1-x)`, `Wₓ = (1-q)x−ℓ(1-x)`.  Proof: the three integrals fold (via `beta_hsym`) into the
three `hsym` blocks of `diagKernel`, with the scalar constants collapsing by `Cmr_K_eq`/`Cmr_K3_eq`. -/
lemma gform_eq {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q ℓ : ℝ) :
    diagKernel m r q ℓ
      = Cmr m r * ∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1)
          * (((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
              * ((q * x + ℓ * (1 - x)) ^ (m - 2 * r) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
            - x * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1)) := by
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
  have hG1 : (∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (m - 2 * r))
      = (Nat.factorial (r - 1) * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r) : ℝ)
          / Nat.factorial (m - 1)
        * hsym (List.replicate r q ++ List.replicate r ℓ) (m - 2 * r) := by
    rw [beta_hsym (r - 1) (r - 1) q ℓ (m - 2 * r), show r - 1 + 1 = r from by omega,
      show (r - 1) + (r - 1) + (m - 2 * r) + 1 = m - 1 from by omega]
  have hG2 : (∫ x in (0:ℝ)..1, x ^ (r - 1) * (1 - x) ^ (r - 1)
        * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
      = (Nat.factorial (r - 1) * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r) : ℝ)
          / Nat.factorial (m - 1)
        * hsym (List.replicate r (1 - q) ++ List.replicate r (-ℓ)) (m - 2 * r) := by
    rw [beta_hsym (r - 1) (r - 1) (1 - q) (-ℓ) (m - 2 * r), show r - 1 + 1 = r from by omega,
      show (r - 1) + (r - 1) + (m - 2 * r) + 1 = m - 1 from by omega]
  have hG3 : (∫ x in (0:ℝ)..1, x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1))
      = (Nat.factorial r * Nat.factorial (r - 1) * Nat.factorial (m - 2 * r - 1) : ℝ)
          / Nat.factorial (m - 1)
        * hsym (List.replicate (r + 1) q ++ List.replicate r ℓ) (m - 2 * r - 1) := by
    rw [beta_hsym r (r - 1) q ℓ (m - 2 * r - 1), show r - 1 + 1 = r from by omega,
      show r + (r - 1) + (m - 2 * r - 1) + 1 = m - 1 from by omega]
  have hpt : Set.EqOn
      (fun x => x ^ (r - 1) * (1 - x) ^ (r - 1)
        * (((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
            * ((q * x + ℓ * (1 - x)) ^ (m - 2 * r) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
          - x * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1)))
      (fun x => ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ)) * (x ^ (r - 1) * (1 - x) ^ (r - 1)
            * (q * x + ℓ * (1 - x)) ^ (m - 2 * r))
          + ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ)) * (x ^ (r - 1) * (1 - x) ^ (r - 1)
            * ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
          - x ^ r * (1 - x) ^ (r - 1) * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1))
      (Set.uIcc 0 1) := by
    intro x _
    dsimp only
    rw [show x ^ r = x ^ (r - 1) * x from by rw [← pow_succ, Nat.sub_add_cancel hr1]]
    ring
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hG1, hG2, hG3]
  unfold diagKernel
  linear_combination
    (-(hsym (List.replicate r q ++ List.replicate r ℓ) (m - 2 * r))
      - hsym (List.replicate r (1 - q) ++ List.replicate r (-ℓ)) (m - 2 * r)) * Cmr_K_eq hr hn
    + hsym (List.replicate (r + 1) q ++ List.replicate r ℓ) (m - 2 * r - 1) * Cmr_K3_eq hr hn

/-- `C_{m,r} > 0` for `r ≥ 1`, `n = m−2r ≥ 1`. -/
lemma Cmr_pos {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) : 0 < Cmr m r := by
  have hc : 0 < (Nat.choose (m - 1) (2 * r - 1) : ℝ) :=
    mod_cast Nat.choose_pos (show 2 * r - 1 ≤ m - 1 from by omega)
  have hn0 : 0 < ((m - 2 * r : ℕ) : ℝ) := mod_cast (show 0 < m - 2 * r from by omega)
  have hr0 : 0 < (r : ℝ) := mod_cast Nat.pos_of_ne_zero hr
  have hf1 : 0 < (Nat.factorial (2 * r - 1) : ℝ) := mod_cast Nat.factorial_pos _
  have hf2 : 0 < (Nat.factorial (r - 1) : ℝ) := mod_cast Nat.factorial_pos _
  unfold Cmr
  exact div_pos (mul_pos (div_pos (mul_pos hc hn0) hr0) hf1) (by positivity)

/-- **The bracket integrand equals `xⁿ·ρ(Vₓ/x)`** for `x ≠ 0` (`n = m−2r ≥ 1`).  Since `Vₓ/x = q +
ℓ(1-x)/x` and `1 − Vₓ/x = Wₓ/x`, the finite-`x` form of the kernel integrand carries the whole `ρ`
sign structure. -/
lemma bracket_eq_rho {m r : ℕ} (hn : 1 ≤ m - 2 * r) (q ℓ x : ℝ) (hx : x ≠ 0) :
    ((m : ℝ) / ((m - 2 * r : ℕ) : ℝ))
        * ((q * x + ℓ * (1 - x)) ^ (m - 2 * r) + ((1 - q) * x + (-ℓ) * (1 - x)) ^ (m - 2 * r))
      - x * (q * x + ℓ * (1 - x)) ^ (m - 2 * r - 1)
      = x ^ (m - 2 * r) * rho (m - 2 * r) m ((q * x + ℓ * (1 - x)) / x) := by
  set n := m - 2 * r with hndef
  have hn1 : 1 ≤ n := hn
  have h1 : x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ n = (q * x + ℓ * (1 - x)) ^ n := by
    rw [div_pow]; field_simp
  have h2 : x ^ n * (1 - (q * x + ℓ * (1 - x)) / x) ^ n = ((1 - q) * x + (-ℓ) * (1 - x)) ^ n := by
    rw [show (1 : ℝ) - (q * x + ℓ * (1 - x)) / x = ((1 - q) * x + (-ℓ) * (1 - x)) / x from by
      field_simp; ring, div_pow]; field_simp
  have h3 : x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ (n - 1) = x * (q * x + ℓ * (1 - x)) ^ (n - 1) := by
    rw [div_pow, show x ^ n = x ^ (n - 1) * x from by rw [← pow_succ, Nat.sub_add_cancel hn1]]
    field_simp
  rw [rho, show x ^ n * ((m / (n : ℝ)) * (((q * x + ℓ * (1 - x)) / x) ^ n
        + (1 - (q * x + ℓ * (1 - x)) / x) ^ n) - ((q * x + ℓ * (1 - x)) / x) ^ (n - 1))
      = (m / (n : ℝ)) * (x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ n
          + x ^ n * (1 - (q * x + ℓ * (1 - x)) / x) ^ n)
        - x ^ n * ((q * x + ℓ * (1 - x)) / x) ^ (n - 1) from by ring, h1, h2, h3]

/-- Reduce `0 ≤ diagKernel` to the pointwise `ρ`-nonnegativity of `Vₓ/x` on `(0,1]`
(`n = 2t+1` odd, `r ≥ 1`).  The `x = 0` endpoint contributes `0` because `n` is odd. -/
lemma diagKernel_nonneg_of_rho {m r t : ℕ} (hr : r ≠ 0) (ht : m - 2 * r = 2 * t + 1) (q ℓ : ℝ)
    (hrho : ∀ x, 0 < x → x ≤ 1 → 0 ≤ rho (2 * t + 1) m ((q * x + ℓ * (1 - x)) / x)) :
    0 ≤ diagKernel m r q ℓ := by
  have hn : 1 ≤ m - 2 * r := by omega
  rw [gform_eq hr hn]
  apply mul_nonneg (le_of_lt (Cmr_pos hr hn))
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro x hx
  refine mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg (by linarith [hx.2]) _)) ?_
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0, ht]
    rw [show q * (0:ℝ) + ℓ * (1 - 0) = ℓ from by ring,
      show (1 - q) * (0:ℝ) + (-ℓ) * (1 - 0) = -ℓ from by ring, Odd.neg_pow ⟨t, by ring⟩]
    apply le_of_eq; ring
  · rw [bracket_eq_rho hn q ℓ x (ne_of_gt hx0), ht]
    exact mul_nonneg (pow_nonneg (le_of_lt hx0) _) (hrho x hx0 hx.2)

/-- **`thm:pointwise` regime (a): `2r ≥ n`.**  Then `m ≥ 2n`, so `ρ ≥ 0` everywhere (`rho_empty`) and
the kernel integrand is pointwise nonnegative, hence `P̃_{m,r}(q,ℓ) ≥ 0` for every `q, ℓ`. -/
theorem diagKernel_nonneg_two_r_ge {m r t : ℕ} (hr : r ≠ 0) (ht : m - 2 * r = 2 * t + 1)
    (h2r : 2 * t + 1 ≤ 2 * r) (q ℓ : ℝ) : 0 ≤ diagKernel m r q ℓ := by
  refine diagKernel_nonneg_of_rho hr ht q ℓ (fun x _ _ => ?_)
  exact rho_empty t m (by exact_mod_cast (show 2 * (2 * t + 1) ≤ m from by omega)) _

/-- **`thm:pointwise` regime (b): `ℓ ≤ 0`** (with `q ≤ 1/2`).  Then `Vₓ/x = q + ℓ(1-x)/x ≤ q ≤ 1/2`
on `(0,1]`, so `ρ(Vₓ/x) ≥ 0` (`rho_window_left`), hence `P̃_{m,r}(q,ℓ) ≥ 0`. -/
theorem diagKernel_nonneg_le_zero {m r t : ℕ} (hr : r ≠ 0) (ht : m - 2 * r = 2 * t + 1)
    (q ℓ : ℝ) (hq : q ≤ 1 / 2) (hl : ℓ ≤ 0) : 0 ≤ diagKernel m r q ℓ := by
  refine diagKernel_nonneg_of_rho hr ht q ℓ (fun x hx0 hx1 => ?_)
  apply rho_window_left t m (by exact_mod_cast (show 2 * t + 1 ≤ m from by omega))
  rw [div_le_iff₀ hx0]
  nlinarith [mul_nonneg (le_of_lt hx0) (by linarith : (0:ℝ) ≤ 1 / 2 - q),
    mul_nonpos_of_nonpos_of_nonneg hl (by linarith : (0:ℝ) ≤ 1 - x)]

end OddCycleBound.DenseRegion
