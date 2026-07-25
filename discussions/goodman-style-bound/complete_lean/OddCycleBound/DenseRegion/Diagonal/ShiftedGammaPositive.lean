/-
# Dense region (Phase D) — shifted-gamma positivity (paper §4, `prop:dense-gamma-positive`, line 1526)

Given the uniform odd-to-even gamma moment inequality (`lem:gamma-moment`, here supplied as the
hypothesis `hmoment`), the shifted-gamma expectation of `ρ` is nonnegative for `q ≤ 1/3`:

`E ρ_{n,m}(q + xY) ≥ 0`,  `Y ~ Γ(r,1)`,  `x ≥ 0`,  `n = 2t+1`,  `m = n + 2r`.

The proof substitutes `z = x/δ` (`δ = ½ − q ≥ 1/6`) so that `q + xy − ½ = δ(zy − 1)`, expands `ρ` by
the centered identity `rho_centered`, and applies the moment inequality to each `j`-block; the
density threshold `q ≤ 1/3` enters exactly through `2δ − 1/3 = 2(1/3 − q) ≥ 0`.

We keep the moment inequality abstract (`hmoment`), so this file is complete and certificate-free;
`GammaMoment.lean` will discharge `hmoment` (that is the file's hard analytic content, D6).
-/
import OddCycleBound.DenseRegion.Diagonal.GammaMoment
import OddCycleBound.DenseRegion.Diagonal.RhoIdentities

open MeasureTheory Set
open scoped BigOperators

namespace OddCycleBound.DenseRegion

/-- **`prop:dense-gamma-positive` modulo the moment inequality.**  If the uniform gamma moment
inequality `hmoment` holds, then `gExp r (ρ_{n,m}(q + x·)) ≥ 0` (`= Γ(r)·E ρ(q+xY) ≥ 0`) for
`0 ≤ q ≤ 1/3` and `x ≥ 0`, where `n = 2t+1`, `m = n + 2r`. -/
theorem shifted_gamma_positive_of_moment_bound (t r : ℕ) (hr : 1 ≤ r)
    (hmoment : ∀ j : ℕ, 1 ≤ j → ∀ z : ℝ, 0 ≤ z →
      3 * (j : ℝ) * gExp r (fun y => (z * y - 1) ^ (2 * j - 1))
        ≤ ((r : ℝ) + j) * gExp r (fun y => (z * y - 1) ^ (2 * j)))
    (q x : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hx : 0 ≤ x) :
    0 ≤ gExp r (fun y => rho (2 * t + 1) (2 * t + 1 + 2 * r) (q + x * y)) := by
  set δ : ℝ := 1 / 2 - q with hδdef
  have hδ16 : 1 / 6 ≤ δ := by rw [hδdef]; linarith
  have hδpos : 0 < δ := by linarith
  set z : ℝ := x / δ with hzdef
  have hz : 0 ≤ z := by rw [hzdef]; positivity
  have hδz : δ * z = x := by rw [hzdef]; field_simp
  -- `(x·−δ)^k = δ^k (z·−1)^k`, hence `gExp r ((x·−δ)^k) = δ^k · gExp r ((z·−1)^k)`
  have hpt : ∀ (k : ℕ) (y : ℝ), (x * y - δ) ^ k = δ ^ k * (z * y - 1) ^ k := by
    intro k y
    rw [← mul_pow]; congr 1; rw [mul_sub, mul_one, ← mul_assoc, hδz]
  have hscale : ∀ k : ℕ, gExp r (fun y => (x * y - δ) ^ k)
      = δ ^ k * gExp r (fun y => (z * y - 1) ^ k) := fun k => by
    rw [show (fun y => (x * y - δ) ^ k) = (fun y => δ ^ k * (z * y - 1) ^ k) from
        funext (fun y => hpt k y), gExp_const_mul]
  -- integrability of `weight · (x·−δ)^k` and `weight · c·(x·−δ)^k`
  have hint : ∀ k : ℕ,
      IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * (x * y - δ) ^ k) (Set.Ioi (0 : ℝ)) :=
    fun k => (gExp_affinePow_integrableOn r k x (-δ)).congr_fun
      (fun y _ => by rw [sub_eq_add_neg]) measurableSet_Ioi
  have hintc : ∀ (c : ℝ) (k : ℕ),
      IntegrableOn (fun y => y ^ (r - 1) * Real.exp (-y) * (c * (x * y - δ) ^ k)) (Set.Ioi (0 : ℝ)) :=
    fun c k => IntegrableOn.congr_fun ((hint k).const_mul c)
      (fun y _ => by ring) measurableSet_Ioi
  -- even gamma moment nonnegative
  have hG2j : ∀ j : ℕ, 0 ≤ gExp r (fun y => (z * y - 1) ^ (2 * j)) :=
    fun j => gExp_nonneg r _ (fun y _ => by rw [pow_mul]; positivity)
  -- `gExp` of each `j`-block, in evaluated form
  have hFval : ∀ j : ℕ,
      gExp r (fun y => aCoef t j * (2 * ((r : ℝ) + j) * (x * y - δ) ^ (2 * j)
          - (j : ℝ) * (x * y - δ) ^ (2 * j - 1)))
        = aCoef t j * (2 * ((r : ℝ) + j) * gExp r (fun y => (x * y - δ) ^ (2 * j))
            - (j : ℝ) * gExp r (fun y => (x * y - δ) ^ (2 * j - 1))) := by
    intro j
    rw [gExp_const_mul r (aCoef t j),
        gExp_sub r _ _ (hintc (2 * ((r : ℝ) + j)) (2 * j)) (hintc (j : ℝ) (2 * j - 1)),
        gExp_const_mul r (2 * ((r : ℝ) + j)), gExp_const_mul r (j : ℝ)]
  -- each block's `gExp` is nonnegative
  have hblock : ∀ j : ℕ,
      0 ≤ gExp r (fun y => aCoef t j * (2 * ((r : ℝ) + j) * (x * y - δ) ^ (2 * j)
          - (j : ℝ) * (x * y - δ) ^ (2 * j - 1))) := by
    intro j
    rw [hFval j]
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      simp only [Nat.cast_zero, add_zero, mul_zero, zero_mul, sub_zero, Nat.mul_zero, pow_zero]
      have h1 : gExp r (fun _ : ℝ => (1 : ℝ)) = (Nat.factorial (r - 1) : ℝ) := by
        simpa using gExp_monomial r 0
      have haC0 : (0 : ℝ) ≤ aCoef t 0 := (aCoef_pos t 0 (Nat.zero_le t)).le
      rw [h1]; positivity
    · rw [hscale (2 * j), hscale (2 * j - 1)]
      set G2 : ℝ := gExp r (fun y => (z * y - 1) ^ (2 * j)) with hG2def
      set G1 : ℝ := gExp r (fun y => (z * y - 1) ^ (2 * j - 1)) with hG1def
      have hG2nn : 0 ≤ G2 := hG2j j
      have hmom : 3 * (j : ℝ) * G1 ≤ ((r : ℝ) + j) * G2 := hmoment j hj1 z hz
      have haC : 0 ≤ aCoef t j := by unfold aCoef; positivity
      have hpowsplit : δ ^ (2 * j) = δ ^ (2 * j - 1) * δ := by rw [← pow_succ]; congr 1; omega
      have hbracket : 0 ≤ 2 * ((r : ℝ) + j) * δ * G2 - (j : ℝ) * G1 := by
        nlinarith [hmom, hG2nn,
          mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) + j)
            (by linarith : (0 : ℝ) ≤ 2 * δ - 1 / 3)) hG2nn]
      have hkey : 0 ≤ aCoef t j * (δ ^ (2 * j - 1) * (2 * ((r : ℝ) + j) * δ * G2 - (j : ℝ) * G1)) :=
        mul_nonneg haC (mul_nonneg (by positivity) hbracket)
      calc (0 : ℝ)
          ≤ aCoef t j * (δ ^ (2 * j - 1) * (2 * ((r : ℝ) + j) * δ * G2 - (j : ℝ) * G1)) := hkey
        _ = aCoef t j * (2 * ((r : ℝ) + j) * (δ ^ (2 * j) * G2)
              - (j : ℝ) * (δ ^ (2 * j - 1) * G1)) := by rw [hpowsplit]; ring
  -- assemble: `(2t+1)·gExp(ρ) = Σ_j block_j ≥ 0`
  have hpos2t1 : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  rw [← mul_nonneg_iff_of_pos_left hpos2t1,
      ← gExp_const_mul r (2 * (t : ℝ) + 1) (fun y => rho (2 * t + 1) (2 * t + 1 + 2 * r) (q + x * y))]
  have hcentered : (fun y => (2 * (t : ℝ) + 1) * rho (2 * t + 1) (2 * t + 1 + 2 * r) (q + x * y))
      = fun y => ∑ j ∈ Finset.range (t + 1),
          aCoef t j * (2 * ((r : ℝ) + j) * (x * y - δ) ^ (2 * j)
            - (j : ℝ) * (x * y - δ) ^ (2 * j - 1)) := by
    funext y
    rw [show q + x * y = 1 / 2 + (x * y - δ) from by rw [hδdef]; ring, rho_centered]
  rw [hcentered, gExp_finset_sum r _ _ ?_]
  · exact Finset.sum_nonneg (fun j _ => hblock j)
  · intro j _
    rw [show (fun y => y ^ (r - 1) * Real.exp (-y)
            * (aCoef t j * (2 * ((r : ℝ) + j) * (x * y - δ) ^ (2 * j)
                - (j : ℝ) * (x * y - δ) ^ (2 * j - 1))))
          = fun y => aCoef t j
              * ((y ^ (r - 1) * Real.exp (-y) * (2 * ((r : ℝ) + j) * (x * y - δ) ^ (2 * j)))
                - (y ^ (r - 1) * Real.exp (-y) * ((j : ℝ) * (x * y - δ) ^ (2 * j - 1))))
          from by funext y; ring]
    exact (((hintc (2 * ((r : ℝ) + j)) (2 * j)).sub (hintc (j : ℝ) (2 * j - 1))).const_mul (aCoef t j))

end OddCycleBound.DenseRegion
