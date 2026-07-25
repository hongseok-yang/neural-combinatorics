/-
# Dense region (Phase D) — the centered `ρ` identities (paper §4, lines 1444–1557)

Elementary polynomial identities for `ρ_{n,m}` that feed the gamma endgame.  `RhoLemma.lean`
already supplies `eq:dense-rho-pointwise` (as `rho_rearrange1`).  This file adds, for odd
`n = 2t+1` and `m = n + 2r`:

* `An` and its **reflection evenness** `Aₙ(½+v) = Aₙ(½−v)` (`An_half_even`);
* `eq:dense-rho-derivative` (line 1541): `n·ρ_{n,m}(u) = 2r·Aₙ(u) − (1−u)·Aₙ'(u)`, stated with
  `Aₙ'(u) = n(u^{n-1} − (1−u)^{n-1})` — a pure `ring` identity, no `deriv`;
* the **centered form** `eq:dense-rho-centered` (line 1552):
  `n·ρ_{n,m}(½+v) = 2r·a₀ + Σ_{j=1}^{t} aⱼ·(2(r+j)v^{2j} − j·v^{2j-1})`,
  with `aⱼ = 2·C(2t+1,2j)·(½)^{2t+1-2j} > 0` (`aCoef`, `aCoef_pos`).

The centered form is the object on which `prop:dense-gamma-positive` (`ShiftedGammaPositive.lean`)
takes a gamma expectation and applies the moment inequality term by term.
-/
import OddCycleBound.DenseRegion.RhoLemma

open scoped BigOperators

namespace OddCycleBound.DenseRegion

/-- `Aₙ(u) = uⁿ + (1−u)ⁿ`. -/
noncomputable def An (n : ℕ) (u : ℝ) : ℝ := u ^ n + (1 - u) ^ n

/-- `Aₙ(u) = Aₙ(1−u)` (swap the two summands). -/
lemma An_reflect (n : ℕ) (u : ℝ) : An n u = An n (1 - u) := by
  unfold An; rw [show (1 : ℝ) - (1 - u) = u from by ring]; ring

/-- `Aₙ(½+v) = Aₙ(½−v)`: the reflection evenness in the centered variable. -/
lemma An_half_even (n : ℕ) (v : ℝ) : An n (1 / 2 + v) = An n (1 / 2 - v) := by
  rw [An_reflect n (1 / 2 + v), show (1 : ℝ) - (1 / 2 + v) = 1 / 2 - v from by ring]

/-- **`eq:dense-rho-derivative` (line 1541).**  For `n = 2t+1`, `m = n + 2r`:
`n·ρ_{n,m}(u) = 2r·Aₙ(u) − (1−u)·Aₙ'(u)`, with `Aₙ'(u) = n(u^{n-1} − (1−u)^{n-1})`. -/
lemma rho_derivative (t r : ℕ) (u : ℝ) :
    (2 * (t : ℝ) + 1) * rho (2 * t + 1) (2 * t + 1 + 2 * r) u
      = 2 * (r : ℝ) * An (2 * t + 1) u
        - (1 - u) * ((2 * (t : ℝ) + 1) * (u ^ (2 * t) - (1 - u) ^ (2 * t))) := by
  have hn : (2 * (t : ℝ) + 1) ≠ 0 := by positivity
  unfold rho An
  rw [show 2 * t + 1 - 1 = 2 * t from by omega]
  push_cast
  rw [pow_succ u (2 * t), pow_succ (1 - u) (2 * t)]
  field_simp
  ring

/-- The centered even coefficients `aⱼ = 2·C(2t+1,2j)·(½)^{2t+1-2j}` of `Aₙ(½+v)` (`n = 2t+1`). -/
noncomputable def aCoef (t j : ℕ) : ℝ :=
  2 * (Nat.choose (2 * t + 1) (2 * j) : ℝ) * (1 / 2 : ℝ) ^ (2 * t + 1 - 2 * j)

/-- `aⱼ > 0` for `j ≤ t` (then `2j ≤ 2t < 2t+1`, so the binomial coefficient is positive). -/
lemma aCoef_pos (t j : ℕ) (hj : j ≤ t) : 0 < aCoef t j := by
  have hc : 0 < (Nat.choose (2 * t + 1) (2 * j) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 2 * j ≤ 2 * t + 1 from by omega)
  unfold aCoef; positivity

/-- **`eq:dense-even-expansion` (line 1545).**  For odd `n = 2t+1`,
`Aₙ(½+v) = Σ_{j=0}^{t} aⱼ v^{2j}`.  Both `(½+v)ⁿ` and `(½−v)ⁿ` expand by the binomial theorem;
odd powers of `v` cancel between the two, and the even index `k = 2j` carries coefficient `aⱼ`. -/
lemma An_half_expansion (t : ℕ) (v : ℝ) :
    An (2 * t + 1) (1 / 2 + v) = ∑ j ∈ Finset.range (t + 1), aCoef t j * v ^ (2 * j) := by
  classical
  set g : ℕ → ℝ := fun k =>
    (1 + (-1 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ (2 * t + 1 - k) * (Nat.choose (2 * t + 1) k : ℝ)) * v ^ k
    with hg
  -- 1. binomial expansion, combining the two summands into `g`
  have hAn : An (2 * t + 1) (1 / 2 + v) = (v + 1 / 2) ^ (2 * t + 1) + (-v + 1 / 2) ^ (2 * t + 1) := by
    unfold An
    rw [show (1 : ℝ) / 2 + v = v + 1 / 2 from by ring,
        show (1 : ℝ) - (v + 1 / 2) = -v + 1 / 2 from by ring]
  have hexp : An (2 * t + 1) (1 / 2 + v) = ∑ k ∈ Finset.range (2 * t + 2), g k := by
    rw [hAn, add_pow, add_pow, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hnp : (-v) ^ k = (-1 : ℝ) ^ k * v ^ k := by rw [neg_pow]
    simp only [hg]; rw [hnp]; ring
  -- 2. only even `k = 2j` survive; reindex to `range (t+1)`
  have hinj : ∀ a ∈ Finset.range (t + 1), ∀ b ∈ Finset.range (t + 1),
      (fun j => 2 * j) a = (fun j => 2 * j) b → a = b := by
    intro a _ b _ hab; dsimp only at hab; omega
  have himg : (Finset.range (t + 1)).image (fun j => 2 * j) ⊆ Finset.range (2 * t + 2) := by
    intro k hk; simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    obtain ⟨j, hj, rfl⟩ := hk; omega
  have hz : ∀ k ∈ Finset.range (2 * t + 2),
      k ∉ (Finset.range (t + 1)).image (fun j => 2 * j) → g k = 0 := by
    intro k hkr hk
    simp only [Finset.mem_range] at hkr
    simp only [Finset.mem_image, Finset.mem_range] at hk
    have hodd : Odd k := by
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨j, rfl⟩ := he; exact absurd ⟨j, by omega, by ring⟩ hk
      · exact ho
    simp only [hg]; rw [hodd.neg_one_pow]; ring
  have hreindex : ∑ k ∈ Finset.range (2 * t + 2), g k = ∑ j ∈ Finset.range (t + 1), g (2 * j) := by
    rw [← Finset.sum_subset himg hz, Finset.sum_image hinj]
  -- 3. `g (2j) = aⱼ v^{2j}`
  have hterm : ∀ j ∈ Finset.range (t + 1), g (2 * j) = aCoef t j * v ^ (2 * j) := by
    intro j _
    simp only [hg, aCoef]
    rw [show (-1 : ℝ) ^ (2 * j) = 1 from by rw [pow_mul]; norm_num]
    ring
  rw [hexp, hreindex, Finset.sum_congr rfl hterm]

/-- The differentiated even expansion (`Aₙ'(½+v)`, the odd companion of `An_half_expansion`).
For `n = 2t+1`, `n·((½+v)^{n-1} − (½−v)^{n-1}) = Σ_{j=0}^{t} 2j·aⱼ·v^{2j-1}` (the `j=0` term vanishes).
The coefficient identity `(2t+1)·C(2t,2j−1) = 2j·C(2t+1,2j)` is `Nat.succ_mul_choose_eq`. -/
lemma An_deriv_half_expansion (t : ℕ) (v : ℝ) :
    (2 * (t : ℝ) + 1) * ((1 / 2 + v) ^ (2 * t) - (1 / 2 - v) ^ (2 * t))
      = ∑ j ∈ Finset.range (t + 1), (2 * (j : ℝ)) * aCoef t j * v ^ (2 * j - 1) := by
  classical
  set g : ℕ → ℝ := fun k =>
    (2 * (t : ℝ) + 1) * (1 - (-1 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ (2 * t - k) * (Nat.choose (2 * t) k : ℝ))
      * v ^ k with hg
  have hexp : (2 * (t : ℝ) + 1) * ((1 / 2 + v) ^ (2 * t) - (1 / 2 - v) ^ (2 * t))
      = ∑ k ∈ Finset.range (2 * t + 1), g k := by
    rw [show (1 : ℝ) / 2 + v = v + 1 / 2 from by ring, show (1 : ℝ) / 2 - v = -v + 1 / 2 from by ring,
        add_pow, add_pow, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hnp : (-v) ^ k = (-1 : ℝ) ^ k * v ^ k := by rw [neg_pow]
    simp only [hg]; rw [hnp]; ring
  -- reindex the odd `k = 2j-1`
  have hinj : ∀ a ∈ Finset.range (t + 1), ∀ b ∈ Finset.range (t + 1),
      (fun j => 2 * j - 1) a = (fun j => 2 * j - 1) b → a = b := by
    intro a _ b _ hab; dsimp only at hab; omega
  have himg : (Finset.range (t + 1)).image (fun j => 2 * j - 1) ⊆ Finset.range (2 * t + 1) := by
    intro k hk; simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    obtain ⟨j, hj, rfl⟩ := hk; omega
  have hz : ∀ k ∈ Finset.range (2 * t + 1),
      k ∉ (Finset.range (t + 1)).image (fun j => 2 * j - 1) → g k = 0 := by
    intro k hkr hk
    simp only [Finset.mem_range] at hkr
    simp only [Finset.mem_image, Finset.mem_range] at hk
    have heven : Even k := by
      rcases Nat.even_or_odd k with he | ho
      · exact he
      · obtain ⟨i, rfl⟩ := ho; exact absurd ⟨i + 1, by omega, by omega⟩ hk
    simp only [hg]; rw [heven.neg_one_pow]; ring
  have hreindex : ∑ k ∈ Finset.range (2 * t + 1), g k
      = ∑ j ∈ Finset.range (t + 1), g (2 * j - 1) := by
    rw [← Finset.sum_subset himg hz, Finset.sum_image hinj]
  have hterm : ∀ j ∈ Finset.range (t + 1),
      g (2 * j - 1) = (2 * (j : ℝ)) * aCoef t j * v ^ (2 * j - 1) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0; simp only [hg]; norm_num
    · have hodd : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
      have hchoose : (2 * (t : ℝ) + 1) * (Nat.choose (2 * t) (2 * j - 1) : ℝ)
          = (2 * (j : ℝ)) * (Nat.choose (2 * t + 1) (2 * j) : ℝ) := by
        have h := Nat.succ_mul_choose_eq (2 * t) (2 * j - 1)
        rw [show (2 * t).succ = 2 * t + 1 from rfl, show (2 * j - 1).succ = 2 * j from by omega] at h
        have hc := congrArg (Nat.cast (R := ℝ)) h
        push_cast at hc
        linear_combination hc
      simp only [hg, aCoef]
      rw [hodd.neg_one_pow, show 2 * t - (2 * j - 1) = 2 * t + 1 - 2 * j from by omega]
      linear_combination (2 * (1 / 2 : ℝ) ^ (2 * t + 1 - 2 * j) * v ^ (2 * j - 1)) * hchoose
  rw [hexp, hreindex, Finset.sum_congr rfl hterm]

/-- **`eq:dense-rho-centered` (line 1552).**  For odd `n = 2t+1`, `m = n + 2r`:
`n·ρ_{n,m}(½+v) = Σ_{j=0}^{t} aⱼ·(2(r+j)v^{2j} − j·v^{2j-1})` (the `j=0` term is `2r·a₀`).
Combines `rho_derivative` with the even/odd half-expansions; every `aⱼ > 0`.  This is the
object on which `prop:dense-gamma-positive` takes a gamma expectation, term by term. -/
lemma rho_centered (t r : ℕ) (v : ℝ) :
    (2 * (t : ℝ) + 1) * rho (2 * t + 1) (2 * t + 1 + 2 * r) (1 / 2 + v)
      = ∑ j ∈ Finset.range (t + 1),
          aCoef t j * (2 * ((r : ℝ) + (j : ℝ)) * v ^ (2 * j) - (j : ℝ) * v ^ (2 * j - 1)) := by
  rw [rho_derivative t r (1 / 2 + v), show (1 : ℝ) - (1 / 2 + v) = 1 / 2 - v from by ring,
      An_half_expansion, An_deriv_half_expansion, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0; simp; ring
  · have hpow : v ^ (2 * j) = v * v ^ (2 * j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]; push_cast; ring
