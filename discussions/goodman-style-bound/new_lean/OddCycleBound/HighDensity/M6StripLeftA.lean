/-
# High-density theorem — residual strip left-estimate, A-branch made unconditional (M6)

Mirror of `M6StripLeftB.diagKernel_nonneg_strip_left_b` for the A-branch (`θ = r/m ≤ 1/6`).
Discharges the `hSD : D ≤ Σ` hypothesis of `diagKernel_nonneg_strip_left` using the power-lifted
factor bounds (`M6TailRatio`, with the case-a third factor `((1/2+θ)/(5/12+θ))` via
`tail_pow_ratio_a`) and the constant inequality `eq:constant-A`: `constA_m500` for `m ≥ 500`
(uniform) glued with the finite sweep `constA_finite_B0` for `63 ≤ m ≤ 499`.  Reuses the algebraic
identity `sig1_eq` from `M6StripLeftB`.
-/

import OddCycleBound.HighDensity.M6TailRatio
import OddCycleBound.HighDensity.M6LeftEstimate
import OddCycleBound.HighDensity.AppConstantsTail
import OddCycleBound.HighDensity.M6StripLeftB
import OddCycleBound.HighDensity.Sweep.Aggregate

namespace OddCycleBound.HighDensity

set_option maxHeartbeats 1600000 in
/-- **A-branch residual strip, unconditional** (`lem:left-estimate`(a) + `app:constants`
`eq:constant-A`).  For the residual case with `θ = r/m ≤ 1/6`, `0 < ℓ < q + r/m`, `m ≥ 63`,
`diagKernel ≥ 0`.  Discharges `hSD` (`D ≤ Σ`) via `sig1_eq` + `cn_core` + the power-lifted factor
bounds + `eq:constant-A` (`constA_m500` for `m ≥ 500`, `constA_finite_B0` finite sweep for
`63 ≤ m ≤ 499`). -/
theorem diagKernel_nonneg_strip_left_a {m r n t : ℕ} (hr2 : 2 ≤ r) (hmn : m = n + 2 * r)
    (hn2r : 2 * r < n) (hnt : n = 2 * t + 1) (hm63 : 63 ≤ m) {q ℓ : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓ0 : 0 < ℓ) (hℓr : ℓ < q + (r : ℝ) / (m : ℝ))
    (hθ16 : (r : ℝ) / m ≤ 1 / 6) :
    0 ≤ diagKernel m r q ℓ := by
  refine diagKernel_nonneg_strip_left hr2 hmn hn2r hnt hq0 hq hℓ0 hℓr ?_
  -- nat / cast facts
  have hmnat : 0 < m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmnat
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hrnat : 0 < r := by omega
  have hr1 : 1 ≤ r := hrnat
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrnat
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hn33 : 33 ≤ n := by omega
  have h2t1pos : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  have h2t1 : (2 * (t : ℝ) + 1) ≠ 0 := ne_of_gt h2t1pos
  -- θ range
  have hθ0 : (0 : ℝ) ≤ (r : ℝ) / m := by positivity
  have hθ14 : (r : ℝ) / m < 1 / 4 := by
    rw [div_lt_iff₀ hmpos]
    have h4r : (4 * r : ℕ) < m := by omega
    have : (4 : ℝ) * (r : ℝ) < (m : ℝ) := by exact_mod_cast h4r
    linarith
  -- substitution identities
  have hnval : (2 * (t : ℝ) + 1) = (m : ℝ) - 2 * (r : ℝ) := by
    have h1 : (m : ℝ) = (n : ℝ) + 2 * (r : ℝ) := by exact_mod_cast hmn
    have h2 : (n : ℝ) = 2 * (t : ℝ) + 1 := by exact_mod_cast hnt
    linarith
  have hnu_eq : (2 * (t : ℝ) + 1) / (m : ℝ) = 1 - 2 * ((r : ℝ) / m) := by rw [hnval]; field_simp
  have hrm : (r : ℝ) = (r : ℝ) / m * m := by field_simp
  -- positivity of key quantities
  have hepos : (0 : ℝ) < q + (1 / 2 - q) / 2 := by linarith
  have hf7 : (7 : ℝ) / 12 ≤ 1 - (q + (1 / 2 - q) / 2) := by linarith
  have hfepos : (0 : ℝ) < 1 - (q + (1 / 2 - q) / 2) := by linarith
  have hbpos : (0 : ℝ) < (2 * (t : ℝ) + 1) / m - q := by rw [hnu_eq]; linarith [hθ14]
  have hbapos : (0 : ℝ) < ((2 * (t : ℝ) + 1) / m - q) - (1 / 2 - q) := by
    rw [hnu_eq]; linarith [hθ14]
  have hlapos : (0 : ℝ) < ℓ + (1 / 2 - q) := by linarith
  have hlepos : (0 : ℝ) < ℓ + (1 / 2 - q) / 2 := by linarith
  have hnupos : (0 : ℝ) < (2 * (t : ℝ) + 1) / m := by positivity
  -- the identity Σ₁ = D·G
  have hid := sig1_eq (a := 1 / 2 - q) (fe := 1 - (q + (1 / 2 - q) / 2)) (eps := (1 / 2 - q) / 2)
    (la := ℓ + (1 / 2 - q)) (le := ℓ + (1 / 2 - q) / 2) (b := (2 * (t : ℝ) + 1) / m - q)
    (nu := (2 * (t : ℝ) + 1) / m) (r := r) (tt := t) (m := m) hm0 rfl hr1 hr0
    (ne_of_gt hbpos) (ne_of_gt hbapos) (ne_of_gt hlapos) (ne_of_gt hlepos) (ne_of_gt hnupos) h2t1
  -- D_raw = D (clean form)
  have hDeq : ((2 * (t : ℝ) + 1) / m - q) ^ (r - 1)
        * ((q + (1 / 2 - q)) ^ (2 * t) / (ℓ + (1 / 2 - q)) ^ m)
        * ((((2 * (t : ℝ) + 1) / m - q) - (1 / 2 - q))
          - (m : ℝ) / (2 * (t : ℝ) + 1)
            * ((q + ((2 * (t : ℝ) + 1) / m - q)) ^ 2 - (q + (1 / 2 - q)) ^ 2) / 2)
      = ((2 * (t : ℝ) + 1) / m - q) ^ (r - 1)
        * ((1 / 2 : ℝ) ^ (2 * t) / (ℓ + (1 / 2 - q)) ^ m)
        * (((2 * (t : ℝ) + 1) / m - q - (1 / 2 - q)) ^ 2 / (2 * ((2 * (t : ℝ) + 1) / m))) := by
    rw [show q + (1 / 2 - q) = (1 / 2 : ℝ) from by ring,
      show q + ((2 * (t : ℝ) + 1) / m - q) = (2 * (t : ℝ) + 1) / m from by ring]
    field_simp
    ring
  rw [hDeq]
  -- cn_core step
  have hc := cn_core (n := n) hn33 hepos hf7 (by linarith)
  rw [show n - 1 = 2 * t from by omega, show n = 2 * t + 1 from hnt] at hc
  have hmn1 : (1 : ℝ) ≤ (m : ℝ) / (2 * t + 1) := by
    rw [le_div_iff₀ h2t1pos]
    have : (2 * t + 1 : ℕ) ≤ m := by omega
    have : (2 * (t : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  have hfen : (0 : ℝ) ≤ (1 - (q + (1 / 2 - q) / 2)) ^ (2 * t + 1) := by positivity
  have hcn0 : (q + (1 / 2 - q) / 2) ^ (2 * t)
      ≤ 1 / 100 * ((m : ℝ) / (2 * t + 1)) * (1 - (q + (1 / 2 - q) / 2)) ^ (2 * t + 1) := by
    nlinarith [hc, mul_le_mul_of_nonneg_right hmn1 hfen]
  have hsfpos : (0 : ℝ) ≤ ((1 / 2 - q) / 2) ^ r / ((r : ℝ) * (ℓ + (1 / 2 - q) / 2) ^ m) :=
    div_nonneg (pow_nonneg (by linarith) r) (mul_nonneg hrpos.le (pow_nonneg hlepos.le m))
  -- factor lower bounds
  have hnrm : (n : ℝ) = (m : ℝ) - 2 * (r : ℝ) := by
    rw [show (n : ℝ) = 2 * (t : ℝ) + 1 from by exact_mod_cast hnt]; exact hnval
  have hf2 := tail_pow_p (n := n) (r := r) (m := m) hmnat hnrm hq
  rw [show n = 2 * t + 1 from hnt,
    show 2 * ((1 - q) - (1 - 2 * q) / 4) = 2 * (1 - (q + (1 / 2 - q) / 2)) from by ring] at hf2
  have hf3 := tail_pow_eps (r := r) (m := m) hmnat hq hθ0 (le_of_lt hθ14)
  rw [show ((1 - 2 * q) / 4 : ℝ) = (1 / 2 - q) / 2 from by ring,
    show ((1 - 2 * ((r : ℝ) / m)) - q) = ((2 * (t : ℝ) + 1) / m - q) from by rw [hnu_eq]] at hf3
  have hf4 := tail_pow_ratio_a (m := m) (θ := (r : ℝ) / m) hq hθ0 hℓ0 (le_of_lt hℓr)
  rw [show ((1 - 2 * q) / 4 : ℝ) = (1 / 2 - q) / 2 from by ring] at hf4
  have hbam : ((2 * (t : ℝ) + 1) / m - q) - (1 / 2 - q) = 1 / 2 - 2 * ((r : ℝ) / m) := by
    rw [hnu_eq]; ring
  have hbge : (2 / 3 - 2 * ((r : ℝ) / m)) ≤ (2 * (t : ℝ) + 1) / m - q := by rw [hnu_eq]; linarith
  have hLpos : (0 : ℝ) < 1 / 2 - 2 * ((r : ℝ) / m) := by linarith [hθ14]
  have hL2pos : (0 : ℝ) < (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2 := pow_pos hLpos 2
  have hf1 : (2 / 3 - 2 * ((r : ℝ) / m)) / ((r : ℝ) / m * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2) / (m : ℝ)
      ≤ ((2 * (t : ℝ) + 1) / m - q)
        / ((r : ℝ) * (((2 * (t : ℝ) + 1) / m - q) - (1 / 2 - q)) ^ 2) := by
    rw [hbam, div_div,
      div_le_div_iff₀ (mul_pos (mul_pos (div_pos hrpos hmpos) hL2pos) hmpos)
        (mul_pos hrpos hL2pos),
      show (r : ℝ) * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2 = (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2 * (r : ℝ)
        from by ring,
      show (r : ℝ) / m * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2 * (m : ℝ)
          = (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2 * (r : ℝ) from by field_simp]
    nlinarith [mul_nonneg (mul_nonneg (by linarith [hbge] :
      (0 : ℝ) ≤ (2 * (t : ℝ) + 1) / m - q - (2 / 3 - 2 * ((r : ℝ) / m))) hL2pos.le) hrpos.le]
  -- B₁^m expansion
  have hB1 : ((7 / 6) ^ (1 - 2 * ((r : ℝ) / m)) * (8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))
        * ((1 / 2 + (r : ℝ) / m) / (5 / 12 + (r : ℝ) / m) : ℝ)) ^ m
      = ((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m
        * (((8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))) ^ m * ((1 / 2 + (r : ℝ) / m) / (5 / 12 + (r : ℝ) / m) : ℝ) ^ m) := by
    rw [mul_pow, mul_pow]; ring
  -- G ≥ P/m · B₁^m
  have hPnn : (0 : ℝ) ≤ (2 / 3 - 2 * ((r : ℝ) / m))
      / ((r : ℝ) / m * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2) / (m : ℝ) := by
    apply div_nonneg (div_nonneg (by linarith [hθ14]) (by positivity)) hmpos.le
  -- factor nonnegativities
  have h34nn : (0 : ℝ) ≤ ((1 / 2 + (r : ℝ) / m) / (5 / 12 + (r : ℝ) / m) : ℝ) ^ m := by positivity
  have hf3nn : (0 : ℝ) ≤ ((1 / 2 - q) / 2 / ((2 * (t : ℝ) + 1) / m - q)) ^ r :=
    pow_nonneg (div_nonneg (by linarith) hbpos.le) r
  have hf4nn : (0 : ℝ) ≤ ((ℓ + (1 / 2 - q)) / (ℓ + (1 / 2 - q) / 2)) ^ m :=
    pow_nonneg (div_nonneg hlapos.le hlepos.le) m
  have hg2nn : (0 : ℝ) ≤ (2 * (1 - (q + (1 / 2 - q) / 2))) ^ (2 * t + 1) :=
    pow_nonneg (by linarith) _
  have h8nn : (0 : ℝ) ≤ ((8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))) ^ m :=
    pow_nonneg (Real.rpow_nonneg (by linarith [hθ14]) _) m
  have h76nn : (0 : ℝ) ≤ ((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m :=
    pow_nonneg (Real.rpow_nonneg (by norm_num) _) m
  have h234 : ((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m
        * (((8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))) ^ m * ((1 / 2 + (r : ℝ) / m) / (5 / 12 + (r : ℝ) / m) : ℝ) ^ m)
      ≤ (2 * (1 - (q + (1 / 2 - q) / 2))) ^ (2 * t + 1)
        * (((1 / 2 - q) / 2 / ((2 * (t : ℝ) + 1) / m - q)) ^ r
          * ((ℓ + (1 / 2 - q)) / (ℓ + (1 / 2 - q) / 2)) ^ m) :=
    mul_le_mul hf2 (mul_le_mul hf3 hf4 h34nn hf3nn) (mul_nonneg h8nn h34nn) hg2nn
  have hGexpr : (2 / 3 - 2 * ((r : ℝ) / m)) / ((r : ℝ) / m * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2) / (m : ℝ)
        * (((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m
          * (((8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))) ^ m * ((1 / 2 + (r : ℝ) / m) / (5 / 12 + (r : ℝ) / m) : ℝ) ^ m))
      ≤ ((2 * (t : ℝ) + 1) / m - q)
          / ((r : ℝ) * (((2 * (t : ℝ) + 1) / m - q) - (1 / 2 - q)) ^ 2)
        * ((2 * (1 - (q + (1 / 2 - q) / 2))) ^ (2 * t + 1)
          * (((1 / 2 - q) / 2 / ((2 * (t : ℝ) + 1) / m - q)) ^ r
            * ((ℓ + (1 / 2 - q)) / (ℓ + (1 / 2 - q) / 2)) ^ m)) :=
    mul_le_mul hf1 h234 (mul_nonneg h76nn (mul_nonneg h8nn h34nn)) (le_trans hPnn hf1)
  -- eq:constant-A  (m ≥ 500 uniform  ∪  63 ≤ m ≤ 499 finite sweep)
  have hmodd : m % 2 = 1 := by omega
  have hθ0s : (0 : ℝ) < (r : ℝ) / m := by positivity
  have h6rle : 6 * r ≤ m := by
    have hle : (6 : ℝ) * r ≤ m := by
      have := (div_le_iff₀ hmpos).mp hθ16; linarith
    exact_mod_cast hle
  have h6r : 6 * r < m := by omega
  have hCB : (1 : ℝ) ≤ 99 / (100 * (m : ℝ))
      * ((2 / 3 - 2 * ((r : ℝ) / m)) / (((r : ℝ) / m) * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2))
      * (B0 ((r : ℝ) / m)) ^ m := by
    rcases le_or_gt 500 m with h500 | h500
    · exact constA_m500 h500 hθ0s hθ16
    · exact constA_finite_B0 hmodd hm63 (by omega) hr2 h6r
  simp only [B0] at hCB
  rw [hB1] at hCB
  -- G ≥ 1
  have hG1 : (1 : ℝ) ≤ 99 / 100
      * (((2 * (t : ℝ) + 1) / m - q)
          / ((r : ℝ) * (((2 * (t : ℝ) + 1) / m - q) - (1 / 2 - q)) ^ 2)
        * ((2 * (1 - (q + (1 / 2 - q) / 2))) ^ (2 * t + 1)
          * (((1 / 2 - q) / 2 / ((2 * (t : ℝ) + 1) / m - q)) ^ r
            * ((ℓ + (1 / 2 - q)) / (ℓ + (1 / 2 - q) / 2)) ^ m))) := by
    have hstep := mul_le_mul_of_nonneg_left hGexpr (show (0 : ℝ) ≤ 99 / 100 by norm_num)
    have heq : 99 / (100 * (m : ℝ))
          * ((2 / 3 - 2 * ((r : ℝ) / m)) / ((r : ℝ) / m * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2))
          * (((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m
            * (((8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))) ^ m * ((1 / 2 + (r : ℝ) / m) / (5 / 12 + (r : ℝ) / m) : ℝ) ^ m))
        = 99 / 100 * ((2 / 3 - 2 * ((r : ℝ) / m))
              / ((r : ℝ) / m * (1 / 2 - 2 * ((r : ℝ) / m)) ^ 2) / (m : ℝ)
            * (((7 / 6 : ℝ) ^ (1 - 2 * ((r : ℝ) / m))) ^ m
              * (((8 - 24 * ((r : ℝ) / m)) ^ (-((r : ℝ) / m))) ^ m * ((1 / 2 + (r : ℝ) / m) / (5 / 12 + (r : ℝ) / m) : ℝ) ^ m))) := by
      ring
    rw [heq] at hCB
    exact le_trans hCB hstep
  -- Dcl = D_raw is nonneg
  have hDcpos : (0 : ℝ) ≤ ((2 * (t : ℝ) + 1) / m - q) ^ (r - 1)
      * ((1 / 2 : ℝ) ^ (2 * t) / (ℓ + (1 / 2 - q)) ^ m)
      * (((2 * (t : ℝ) + 1) / m - q - (1 / 2 - q)) ^ 2 / (2 * ((2 * (t : ℝ) + 1) / m))) := by
    have := hbpos; have := hlapos; have := hbapos; have := hnupos; positivity
  -- Dcl ≤ 99/100 · Σ₁
  have hDS : ((2 * (t : ℝ) + 1) / m - q) ^ (r - 1)
        * ((1 / 2 : ℝ) ^ (2 * t) / (ℓ + (1 / 2 - q)) ^ m)
        * (((2 * (t : ℝ) + 1) / m - q - (1 / 2 - q)) ^ 2 / (2 * ((2 * (t : ℝ) + 1) / m)))
      ≤ 99 / 100 * ((m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + (1 / 2 - q) / 2)) ^ (2 * t + 1)
          * (((1 / 2 - q) / 2) ^ r / ((r : ℝ) * (ℓ + (1 / 2 - q) / 2) ^ m))) := by
    have h := mul_le_mul_of_nonneg_left hG1 hDcpos
    rw [mul_one] at h
    calc ((2 * (t : ℝ) + 1) / m - q) ^ (r - 1)
          * ((1 / 2 : ℝ) ^ (2 * t) / (ℓ + (1 / 2 - q)) ^ m)
          * (((2 * (t : ℝ) + 1) / m - q - (1 / 2 - q)) ^ 2 / (2 * ((2 * (t : ℝ) + 1) / m)))
        ≤ _ := h
      _ = 99 / 100 * (((2 * (t : ℝ) + 1) / m - q) ^ (r - 1)
              * ((1 / 2 : ℝ) ^ (2 * t) / (ℓ + (1 / 2 - q)) ^ m)
              * (((2 * (t : ℝ) + 1) / m - q - (1 / 2 - q)) ^ 2 / (2 * ((2 * (t : ℝ) + 1) / m)))
            * (((2 * (t : ℝ) + 1) / m - q)
                / ((r : ℝ) * (((2 * (t : ℝ) + 1) / m - q) - (1 / 2 - q)) ^ 2)
              * ((2 * (1 - (q + (1 / 2 - q) / 2))) ^ (2 * t + 1)
                * (((1 / 2 - q) / 2 / ((2 * (t : ℝ) + 1) / m - q)) ^ r
                  * ((ℓ + (1 / 2 - q)) / (ℓ + (1 / 2 - q) / 2)) ^ m)))) := by ring
      _ = 99 / 100 * ((m : ℝ) / (2 * (t : ℝ) + 1) * (1 - (q + (1 / 2 - q) / 2)) ^ (2 * t + 1)
            * (((1 / 2 - q) / 2) ^ r / ((r : ℝ) * (ℓ + (1 / 2 - q) / 2) ^ m))) := by
        rw [← hid]
  -- 99/100 · Σ₁ ≤ Σ_raw  (cn_core step) and conclude
  have hp := mul_nonneg (show (0 : ℝ) ≤ 1 / 100 * ((m : ℝ) / (2 * (t : ℝ) + 1))
      * (1 - (q + (1 / 2 - q) / 2)) ^ (2 * t + 1) - (q + (1 / 2 - q) / 2) ^ (2 * t)
      by linarith [hcn0]) hsfpos
  nlinarith [hDS, hp]

/-- **Residual strip-left, both branches** (`lem:left-estimate`, `app:constants`).  For the
residual strip (`m ≥ 63`, `r ≥ 2`, `n = m − 2r > 2r`, `0 < ℓ < q + r/m`) and the strip-left case
condition `6r < m ∨ ℓ ≤ 2/5`, the diagonal kernel is nonnegative — the A-branch (`θ < 1/6`) via
`diagKernel_nonneg_strip_left_a` and the B-branch (`θ ≥ 1/6`, `ℓ ≤ 2/5`) via
`diagKernel_nonneg_strip_left_b`.  This is exactly the shape consumed as `Hleft` by
`StripAssembly.diagKernel_nonneg`. -/
theorem diagKernel_nonneg_strip_left_ab {m r n t : ℕ} (hr2 : 2 ≤ r) (hmn : m = n + 2 * r)
    (hn2r : 2 * r < n) (hnt : n = 2 * t + 1) (hm63 : 63 ≤ m) {q ℓ : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) (hℓ0 : 0 < ℓ) (hℓr : ℓ < q + (r : ℝ) / (m : ℝ))
    (hcase : 6 * r < m ∨ ℓ ≤ 2 / 5) :
    0 ≤ diagKernel m r q ℓ := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  by_cases h6r : 6 * r < m
  · -- A-branch: `θ = r/m ≤ 1/6`
    have hθ16 : (r : ℝ) / m ≤ 1 / 6 := by
      rw [div_le_iff₀ hmpos]
      have : (6 : ℝ) * r ≤ m := by exact_mod_cast (show 6 * r ≤ m by omega)
      linarith
    exact diagKernel_nonneg_strip_left_a hr2 hmn hn2r hnt hm63 hq0 hq hℓ0 hℓr hθ16
  · -- B-branch: `θ = r/m ≥ 1/6`, and the case condition forces `ℓ ≤ 2/5`
    have hℓ25 : ℓ ≤ 2 / 5 := hcase.resolve_left h6r
    have hθ16 : 1 / 6 ≤ (r : ℝ) / m := by
      rw [le_div_iff₀ hmpos]
      have : (m : ℝ) ≤ 6 * r := by exact_mod_cast (show m ≤ 6 * r by omega)
      linarith
    exact diagKernel_nonneg_strip_left_b hr2 hmn hn2r hnt hm63 hq0 hq hℓ0 hℓr hθ16 hℓ25

end OddCycleBound.HighDensity
