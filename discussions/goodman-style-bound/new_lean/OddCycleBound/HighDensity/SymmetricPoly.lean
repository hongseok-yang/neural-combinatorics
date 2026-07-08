/-
# High-density theorem — the complete homogeneous symmetric polynomial layer (M1 foundation)

Pure algebra (no graphons).  The `𝓟_{m,r}` kernels of `paper_new.tex` (thm:expansion, eq:P-def) are
built from the complete homogeneous symmetric polynomial `h_d`.  This file defines `hsym` (= `h_d`
evaluated at a list of reals) and proves the two identities the mixture/kernel layer needs:

* **concatenation / convolution** `hsym (xs ++ ys) d = Σ_{j≤d} hsym xs j · hsym ys (d-j)`;
* **single value** `hsym (replicate (k+1) a) d = C(d+k, k) · a^d`.

Together they give the paper's line-1928 identity
`h_d(a^{×(k+1)}, b⃗) = Σ_j C(d-j+k, k) a^{d-j} h_j(b⃗)`.
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OddCycleBound.HighDensity

/-- The complete homogeneous symmetric polynomial `h_d` evaluated at a list of reals:
`hsym (x :: xs) d = Σ_{j=0}^d xʲ · hsym xs (d-j)`, `hsym [] 0 = 1`, `hsym [] (d+1) = 0`. -/
def hsym : List ℝ → ℕ → ℝ
  | [], 0 => 1
  | [], (_ + 1) => 0
  | (x :: xs), d => ∑ j ∈ Finset.range (d + 1), x ^ j * hsym xs (d - j)

lemma hsym_cons (x : ℝ) (xs : List ℝ) (d : ℕ) :
    hsym (x :: xs) d = ∑ j ∈ Finset.range (d + 1), x ^ j * hsym xs (d - j) := rfl

@[simp] lemma hsym_nil (d : ℕ) : hsym [] d = if d = 0 then 1 else 0 := by
  cases d <;> rfl

/-- **Concatenation / convolution.**  `hsym (xs ++ ys) d = Σ_{j≤d} hsym xs j · hsym ys (d-j)`. -/
lemma hsym_append (ys : List ℝ) : ∀ (xs : List ℝ) (d : ℕ),
    hsym (xs ++ ys) d = ∑ j ∈ Finset.range (d + 1), hsym xs j * hsym ys (d - j)
  | [], d => by
      simp only [List.nil_append]
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos d))]
      · simp
      · intro j _ hj
        rw [hsym_nil, if_neg hj, zero_mul]
  | (x :: xs), d => by
      rw [List.cons_append, hsym_cons]
      simp_rw [hsym_append ys xs, Finset.mul_sum]
      simp_rw [hsym_cons, Finset.sum_mul]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij' (fun p => ⟨p.1 + p.2, p.1⟩) (fun p => ⟨p.2, p.1 - p.2⟩)
        ?_ ?_ ?_ ?_ ?_
      · rintro ⟨j, i⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range, Sigma.mk.injEq, heq_eq_eq] at hp ⊢
        omega
      · rintro ⟨J, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range, Sigma.mk.injEq, heq_eq_eq] at hp ⊢
        omega
      · rintro ⟨j, i⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        show (⟨j, j + i - j⟩ : Σ _ : ℕ, ℕ) = ⟨j, i⟩
        rw [show j + i - j = i from by omega]
      · rintro ⟨J, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        show (⟨j + (J - j), j⟩ : Σ _ : ℕ, ℕ) = ⟨J, j⟩
        rw [show j + (J - j) = J from by omega]
      · rintro ⟨j, i⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        rw [show j + i - j = i from by omega, show d - j - i = d - (j + i) from by omega]
        ring

/-- Hockey-stick identity `Σ_{i≤d} C(i+k, k) = C(d+k+1, k+1)`. -/
lemma sum_choose_hockey (k : ℕ) : ∀ d,
    ∑ i ∈ Finset.range (d + 1), Nat.choose (i + k) k = Nat.choose (d + k + 1) (k + 1)
  | 0 => by simp
  | (d + 1) => by
      rw [Finset.sum_range_succ, sum_choose_hockey k d]
      rw [show d + 1 + k + 1 = (d + k + 1) + 1 from by omega,
        Nat.choose_succ_succ (d + k + 1) k, show d + 1 + k = d + k + 1 from by omega]
      ring

/-- **Single value.**  `hsym (replicate (k+1) a) d = C(d+k, k) · a^d`. -/
lemma hsym_replicate (a : ℝ) : ∀ (k d : ℕ),
    hsym (List.replicate (k + 1) a) d = (Nat.choose (d + k) k : ℝ) * a ^ d
  | 0, d => by
      rw [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
      show hsym [a] d = a ^ d
      rw [hsym_cons, Finset.sum_eq_single_of_mem d (Finset.self_mem_range_succ d)]
      · simp
      · intro j hj hjd
        rw [Finset.mem_range] at hj
        rw [hsym_nil, if_neg (by omega), mul_zero]
  | (k + 1), d => by
      show hsym (a :: List.replicate (k + 1) a) d = _
      rw [hsym_cons]
      simp_rw [hsym_replicate a k]
      have hterm : ∀ j ∈ Finset.range (d + 1),
          a ^ j * ((Nat.choose (d - j + k) k : ℝ) * a ^ (d - j))
            = (Nat.choose (d - j + k) k : ℝ) * a ^ d := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hpow : a ^ j * a ^ (d - j) = a ^ d := by
          rw [← pow_add, show j + (d - j) = d from by omega]
        rw [← hpow]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      have hcast : ∑ j ∈ Finset.range (d + 1), (Nat.choose (d - j + k) k : ℝ)
          = (Nat.choose (d + (k + 1)) (k + 1) : ℝ) := by
        have hreindex : ∑ j ∈ Finset.range (d + 1), Nat.choose (d - j + k) k
            = ∑ i ∈ Finset.range (d + 1), Nat.choose (i + k) k :=
          Finset.sum_nbij' (fun j => d - j) (fun i => d - i)
            (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
            (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega)
            (by intro j hj; simp only [Finset.mem_range] at hj; omega)
            (by intro i hi; simp only [Finset.mem_range] at hi; omega)
            (by intro j _; rfl)
        rw [← Nat.cast_sum, hreindex, sum_choose_hockey k d,
          show d + (k + 1) = d + k + 1 from by omega]
      rw [hcast]

/-- **The paper's convolution identity (line 1928):**
`h_d(a^{×(k+1)}, ys) = Σ_{j≤d} C(d-j+k, k) a^{d-j} · h_j(ys)`. -/
lemma hsym_replicate_append (a : ℝ) (ys : List ℝ) (k d : ℕ) :
    hsym (List.replicate (k + 1) a ++ ys) d
      = ∑ j ∈ Finset.range (d + 1),
          (Nat.choose (d - j + k) k : ℝ) * a ^ (d - j) * hsym ys j := by
  rw [hsym_append]
  refine Finset.sum_nbij' (fun j => d - j) (fun j => d - j)
    (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
    (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
    (by intro j hj; simp only [Finset.mem_range] at hj; omega)
    (by intro j hj; simp only [Finset.mem_range] at hj; omega)
    ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [hsym_replicate a k, show d - (d - j) = j from by omega]

@[simp] lemma hsym_singleton (a : ℝ) (d : ℕ) : hsym [a] d = a ^ d := by
  simpa using hsym_replicate a 0 d

/-! ### The diagonal kernel `P̃_{m,r}(q,ℓ)`

The diagonal of `𝓟_{m,r}` (paper eq:P-def evaluated at `λ₁=⋯=λ_r=ℓ`), which by the
mixture-of-diagonals theorem (thm:mixture) is what the whole positivity reduces to (cor:diagonal).
With `n = m-2r`, `p = 1-q`:
`P̃_{m,r} = (m/r)[h_n(p^{×r},(-ℓ)^{×r}) + h_n(q^{×r},ℓ^{×r})] − h_{n-1}(q^{×(r+1)},ℓ^{×r})`. -/
noncomputable def diagKernel (m r : ℕ) (q ℓ : ℝ) : ℝ :=
  (m / r : ℝ)
      * (hsym (List.replicate r (1 - q) ++ List.replicate r (-ℓ)) (m - 2 * r)
        + hsym (List.replicate r q ++ List.replicate r ℓ) (m - 2 * r))
    - hsym (List.replicate (r + 1) q ++ List.replicate r ℓ) (m - 2 * r - 1)

/-- **Validation against the paper (line 2174):** `P̃_{5,1}(q,ℓ) = 4ℓ² + (8q−5)ℓ + 12q² − 15q + 5`. -/
lemma diagKernel_five_one (q ℓ : ℝ) :
    diagKernel 5 1 q ℓ = 4 * ℓ ^ 2 + (8 * q - 5) * ℓ + 12 * q ^ 2 - 15 * q + 5 := by
  unfold diagKernel
  simp only [show (5 : ℕ) - 2 * 1 = 3 from rfl, show (5 : ℕ) - 2 * 1 - 1 = 2 from rfl,
    show (1 : ℕ) + 1 = 2 from rfl, List.replicate_succ, List.replicate_zero,
    List.cons_append, List.nil_append, hsym_cons, hsym_nil, Finset.sum_range_succ,
    Finset.sum_range_zero]
  push_cast
  ring

end OddCycleBound.HighDensity
