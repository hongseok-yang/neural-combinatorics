import OddCycleBound.RegionII.Scalar.Huber

/-!
# Exact Huber shape elimination

This file contains the scalar geometry behind the corrected Region-II Huber
reduction.  Its hypotheses are exactly the direct channel, the squared safe
channel, and the normalized frontier-shape budget.  In particular, the proof
never divides by `K`; the branch `K = 0` is handled explicitly.
-/

open Set

noncomputable section

namespace OddCycleBound.RegionII.Scalar

/-- The safe-channel threshold `H` from the corrected manuscript. -/
noncomputable def shapeThreshold
    (alpha q L z K : Real) : Real :=
  ((alpha - q) * z + (alpha - L) * K) / (2 * Real.sqrt z)

/-- The safe threshold retains a frontier-gap term and half of the safe
spectral payment. -/
theorem shapeThreshold_lower
    {alpha q L z K : Real}
    (halpha : 0 < alpha)
    (hd : 0 <= alpha - q) (hf : 0 <= alpha - L)
    (hK : 0 <= K) (hz : 2 * alpha <= z) (hz1 : z <= 1) :
    (alpha - q) * Real.sqrt (2 * alpha) / 2 +
        (alpha - L) * K / 2 <=
      shapeThreshold alpha q L z K := by
  let d := alpha - q
  let f := alpha - L
  let r := Real.sqrt z
  let s := Real.sqrt (2 * alpha)
  have hzpos : 0 < z := by nlinarith
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hzpos
  have hrsq : r ^ 2 = z := by
    dsimp [r]
    exact Real.sq_sqrt (le_of_lt hzpos)
  have hsle : s <= r := by
    dsimp [s, r]
    exact Real.sqrt_le_sqrt hz
  have hr0 : 0 <= r := le_of_lt hrpos
  have hr1 : r <= 1 := by
    nlinarith [sq_nonneg (r - 1)]
  have hdpart : d * s / 2 <= d * r / 2 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsle (by simpa [d] using hd)) (by norm_num)
  have hfK : 0 <= f * K :=
    mul_nonneg (by simpa [f] using hf) hK
  have hfpart : f * K / 2 <= f * K / (2 * r) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * r)).2
    have hmul : f * K * r <= f * K := by
      nlinarith [mul_nonneg hfK (sub_nonneg.mpr hr1)]
    nlinarith
  calc
    (alpha - q) * Real.sqrt (2 * alpha) / 2 +
          (alpha - L) * K / 2 = d * s / 2 + f * K / 2 := rfl
    _ <= d * r / 2 + f * K / (2 * r) := add_le_add hdpart hfpart
    _ = shapeThreshold alpha q L z K := by
      change d * r / 2 + f * K / (2 * r) =
        (d * z + f * K) / (2 * r)
      field_simp [ne_of_gt hrpos]
      nlinarith [hrsq]

/-- If the coupling coefficient is nonpositive, the safe channel pays the
full product of the frontier and safe gaps. -/
theorem safe_payment_of_nonpos_c
    {alpha q L z b K c gsSq : Real}
    (halpha : 0 < alpha) (hd : 0 < alpha - q) (hf : 0 < alpha - L)
    (hb : 0 <= b) (hK : 0 <= K) (hgs : 0 <= gsSq)
    (hz : 2 * alpha <= z) (hc : c <= 0)
    (hsafe : max (shapeThreshold alpha q L z K - b * c) 0 ^ 2 <=
      gsSq * K) :
    (alpha - q) * (alpha - L) <= gsSq := by
  let d := alpha - q
  let f := alpha - L
  let r := Real.sqrt z
  let H := shapeThreshold alpha q L z K
  have hzpos : 0 < z := by nlinarith
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hzpos
  have hrsq : r ^ 2 = z := by
    dsimp [r]
    exact Real.sq_sqrt (le_of_lt hzpos)
  have hHmul : 2 * r * H = d * z + f * K := by
    dsimp [H, d, f, r, shapeThreshold]
    field_simp [ne_of_gt hrpos]
  have hHpos : 0 < H := by
    have hdz : 0 < d * z := mul_pos (by simpa [d] using hd) hzpos
    have hfK : 0 <= f * K :=
      mul_nonneg (le_of_lt (by simpa [f] using hf)) hK
    nlinarith
  have hbc : b * c <= 0 := mul_nonpos_of_nonneg_of_nonpos hb hc
  have hactive : max (H - b * c) 0 = H - b * c :=
    max_eq_left (by linarith)
  have hKpos : 0 < K := by
    by_contra hnot
    have hKzero : K = 0 := le_antisymm (le_of_not_gt hnot) hK
    rw [hactive, hKzero, mul_zero] at hsafe
    nlinarith [sq_nonneg (H - b * c)]
  have hAMGM : d * f * K <= H ^ 2 := by
    have hsq : 0 <= (d * z - f * K) ^ 2 := sq_nonneg _
    have hcore : 4 * d * f * z * K <= (d * z + f * K) ^ 2 := by
      nlinarith
    have hzH : (2 * r * H) ^ 2 = 4 * z * H ^ 2 := by
      nlinarith [hrsq]
    have hnumEq : (d * z + f * K) ^ 2 = 4 * z * H ^ 2 := by
      rw [← hHmul, hzH]
    rw [hnumEq] at hcore
    have hzmul : z * (d * f * K) <= z * H ^ 2 := by
      nlinarith
    exact le_of_mul_le_mul_left hzmul hzpos
  have hHsafe : H ^ 2 <= gsSq * K := by
    rw [hactive] at hsafe
    nlinarith [sq_nonneg (b * c), mul_nonneg (le_of_lt hHpos) (neg_nonneg.mpr hbc)]
  have hcancel : d * f <= gsSq := by
    have hmul : (d * f) * K <= gsSq * K := by
      nlinarith [hAMGM.trans hHsafe]
    exact le_of_mul_le_mul_right hmul hKpos
  simpa [d, f] using hcancel

/-- For a positive coupling coefficient, the safe channel pays twice the
safe gap times the positive part of the residual frontier demand.  The proof
contains the corrected `K = 0` branch. -/
theorem safe_payment_of_pos_c
    {alpha q L z b K c gsSq : Real}
    (halpha : 0 < alpha)
    (hd : 0 <= alpha - q) (hf : 0 <= alpha - L)
    (hb : 0 <= b) (hK : 0 <= K) (hgs : 0 <= gsSq)
    (hz : 2 * alpha <= z) (hz1 : z <= 1) (hc : 0 < c)
    (hsafe : max (shapeThreshold alpha q L z K - b * c) 0 ^ 2 <=
      gsSq * K) :
    2 * (alpha - L) *
        max ((alpha - q) * Real.sqrt (2 * alpha) / 2 - b * c) 0 <=
      gsSq := by
  let d := alpha - q
  let f := alpha - L
  let s := Real.sqrt (2 * alpha)
  let H := shapeThreshold alpha q L z K
  let w := max (d * s / 2 - b * c) 0
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hHlower : d * s / 2 + f * K / 2 <= H := by
    simpa [d, f, s, H] using
      shapeThreshold_lower halpha hd hf hK hz hz1
  by_cases hKzero : K = 0
  · subst K
    have hmaxZero : max (H - b * c) 0 = 0 := by
      simp only [mul_zero] at hsafe
      nlinarith [sq_nonneg (max (H - b * c) 0)]
    have hHbc : H - b * c <= 0 := by
      exact max_eq_right_iff.mp hmaxZero
    have hwZero : w = 0 := by
      apply max_eq_right
      linarith
    rw [show max ((alpha - q) * Real.sqrt (2 * alpha) / 2 - b * c) 0 = w by rfl,
      hwZero]
    simpa using hgs
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    by_cases hbase : d * s / 2 - b * c <= 0
    · have hwZero : w = 0 := max_eq_right hbase
      rw [show max ((alpha - q) * Real.sqrt (2 * alpha) / 2 - b * c) 0 = w by rfl,
        hwZero]
      simpa using hgs
    · have hw : w = d * s / 2 - b * c :=
        max_eq_left (le_of_not_ge hbase)
      have hcomp : w + f * K / 2 <= H - b * c := by
        rw [hw]
        linarith
      have hrightPos : 0 <= w + f * K / 2 := by
        have hw0 : 0 <= w := le_max_right _ _
        exact add_nonneg hw0 (div_nonneg (mul_nonneg hf hK) (by norm_num))
      have hmaxComp : w + f * K / 2 <= max (H - b * c) 0 :=
        hcomp.trans (le_max_left _ _)
      have hsquareComp : (w + f * K / 2) ^ 2 <=
          max (H - b * c) 0 ^ 2 := by
        exact (sq_le_sq₀ hrightPos (le_max_right _ _)).2 hmaxComp
      have hAMGM : 2 * f * K * w <= (w + f * K / 2) ^ 2 := by
        nlinarith [sq_nonneg (w - f * K / 2)]
      have hmul : 2 * f * K * w <= gsSq * K :=
        hAMGM.trans (hsquareComp.trans hsafe)
      have hcancel : 2 * f * w <= gsSq := by
        have hmul' : (2 * f * w) * K <= gsSq * K := by
          nlinarith [hmul]
        exact le_of_mul_le_mul_right hmul' hKpos
      simpa [d, f, s, w] using hcancel

set_option maxHeartbeats 1000000 in
/-- Exact Huber elimination for abstract frontier-shape data.  The parameters
`C`, `xi`, and `rho` are the manuscript normalizations. -/
theorem exact_huber_shape_elimination
    {alpha q L A B c gsSq z b K : Real}
    (halpha : 0 < alpha) (halphaHalf : alpha < 1 / 2)
    (hqalpha : q < alpha) (hLalpha : L < alpha)
    (hA : 0 <= A) (hB : 0 < B)
    (hb : 0 <= b) (hK : 0 <= K) (hgs : 0 <= gsSq)
    (hz : 2 * alpha <= z) (hshape : z + b ^ 2 + K = 1)
    (hdirect : 2 * c * Real.sqrt z + 2 * alpha * b <= z - 2 * alpha)
    (hsafe : max (shapeThreshold alpha q L z K - b * c) 0 ^ 2 <=
      gsSq * K) :
    let e := 1 - 2 * alpha
    let d := alpha - q
    let f := alpha - L
    let C := B * f * Real.sqrt (2 * alpha) * e ^ 2 / (4 * alpha ^ 2)
    let xi := 4 * alpha ^ 2 * d / e ^ 2
    let rho := (A / B) *
      (Real.sqrt alpha / (2 * Real.sqrt 2 * f))
    C * psi xi rho <= A * c ^ 2 + B * gsSq := by
  dsimp only
  let e := 1 - 2 * alpha
  let d := alpha - q
  let f := alpha - L
  let s := Real.sqrt (2 * alpha)
  let C := B * f * s * e ^ 2 / (4 * alpha ^ 2)
  let xi := 4 * alpha ^ 2 * d / e ^ 2
  let rho := (A / B) *
    (Real.sqrt alpha / (2 * Real.sqrt 2 * f))
  have he : 0 < e := by dsimp [e]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hf : 0 < f := by dsimp [f]; linarith
  have hspos : 0 < s := by dsimp [s]; positivity
  have hssq : s ^ 2 = 2 * alpha := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  have hs1 : s <= 1 := by
    have hs0 : 0 <= s := le_of_lt hspos
    nlinarith [sq_nonneg (s - 1)]
  have hC : 0 < C := by dsimp [C]; positivity
  have hxi : 0 <= xi := by dsimp [xi]; positivity
  have hrho : 0 <= rho := by dsimp [rho]; positivity
  by_cases hc : c <= 0
  · have hsafePay := safe_payment_of_nonpos_c
      halpha (by simpa [d] using hd) (by simpa [f] using hf)
      hb hK hgs hz hc hsafe
    have hpsi : psi xi rho <= xi := by
      have h0 := psi_le_huberObjective
        (xi := xi) (rho := rho) hrho (show (0 : Real) ∈ Icc 0 1 by norm_num)
      simpa [huberObjective, max_eq_left hxi] using h0
    have hCxi : C * xi = B * f * s * d := by
      dsimp [C, xi]
      field_simp [ne_of_gt he, ne_of_gt halpha]
    have hsCompare : B * f * s * d <= B * f * d := by
      have hBf : 0 <= B * f := mul_nonneg (le_of_lt hB) (le_of_lt hf)
      nlinarith [mul_nonneg hBf (sub_nonneg.mpr hs1), le_of_lt hd]
    have hsafeB : B * f * d <= B * gsSq := by
      have hmul := mul_le_mul_of_nonneg_left hsafePay (le_of_lt hB)
      simpa [d, f, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hAc : 0 <= A * c ^ 2 := mul_nonneg hA (sq_nonneg c)
    calc
      C * psi xi rho <= C * xi :=
        mul_le_mul_of_nonneg_left hpsi (le_of_lt hC)
      _ = B * f * s * d := hCxi
      _ <= B * f * d := hsCompare
      _ <= B * gsSq := hsafeB
      _ <= A * c ^ 2 + B * gsSq := by linarith
  · have hcpos : 0 < c := lt_of_not_ge hc
    have hz1 : z <= 1 := by
      nlinarith [sq_nonneg b]
    let r := Real.sqrt z
    have hzpos : 0 < z := by nlinarith
    have hrpos : 0 < r := by dsimp [r]; exact Real.sqrt_pos.2 hzpos
    have hrsq : r ^ 2 = z := by
      dsimp [r]
      exact Real.sq_sqrt (le_of_lt hzpos)
    have hsr : s <= r := by
      dsimp [s, r]
      exact Real.sqrt_le_sqrt hz
    have hdirectS : 2 * c * s + 2 * alpha * b <= z - 2 * alpha := by
      have hcs : 2 * c * s <= 2 * c * r := by
        exact mul_le_mul_of_nonneg_left hsr (by positivity)
      change 2 * c * s + 2 * alpha * b <= z - 2 * alpha
      have hdirect' : 2 * c * r + 2 * alpha * b <= z - 2 * alpha := by
        simpa [r] using hdirect
      linarith
    have hbudget : b ^ 2 + 2 * alpha * b + 2 * c * s <= e := by
      dsimp [e]
      nlinarith
    have hcsE : 2 * c * s <= e := by
      nlinarith [sq_nonneg b, mul_nonneg (le_of_lt halpha) hb, hK]
    let v := 2 * c * s / e
    have hv0 : 0 <= v := by dsimp [v]; positivity
    have hv1 : v <= 1 := by
      dsimp [v]
      exact (div_le_one he).2 hcsE
    have hv : v ∈ Icc (0 : Real) 1 := ⟨hv0, hv1⟩
    have hbBound : b <= (e - 2 * c * s) / (2 * alpha) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * alpha)).2
      nlinarith [sq_nonneg b]
    have hbcBound : b * c <= c * (e - 2 * c * s) / (2 * alpha) := by
      have hmul := mul_le_mul_of_nonneg_right hbBound (le_of_lt hcpos)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
    let t := xi - v + v ^ 2
    let factor := s * e ^ 2 / (8 * alpha ^ 2)
    have hfactor : 0 < factor := by dsimp [factor]; positivity
    have hfactorEq : factor * t =
        d * s / 2 - c * (e - 2 * c * s) / (2 * alpha) := by
      dsimp [factor, t, xi, v]
      field_simp [ne_of_gt he, ne_of_gt halpha]
      linear_combination
        (-4 * e * c + 8 * s * c ^ 2) * hssq
    have hbaseNorm : factor * t <= d * s / 2 - b * c := by
      rw [hfactorEq]
      linarith
    have hmaxNorm : factor * max t 0 <=
        max (d * s / 2 - b * c) 0 := by
      by_cases ht : t <= 0
      · rw [max_eq_right ht]
        simp only [mul_zero]
        exact le_max_right _ _
      · rw [max_eq_left (le_of_not_ge ht)]
        exact hbaseNorm.trans (le_max_left _ _)
    have hsafePay := safe_payment_of_pos_c
      halpha (le_of_lt (by simpa [d] using hd))
      (le_of_lt (by simpa [f] using hf)) hb hK hgs hz hz1 hcpos hsafe
    have hCfactor : C = 2 * B * f * factor := by
      dsimp [C, factor]
      ring
    have hmaxPay : C * max t 0 <= B * gsSq := by
      have hscale : 0 <= 2 * B * f := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hmaxNorm hscale
      have hsafeB := mul_le_mul_of_nonneg_left hsafePay (le_of_lt hB)
      rw [hCfactor]
      calc
        2 * B * f * factor * max t 0 =
            2 * B * f * (factor * max t 0) := by ring
        _ <= 2 * B * f * max (d * s / 2 - b * c) 0 := hscaled
        _ <= B * gsSq := by
          simpa [d, f, s, mul_assoc, mul_comm, mul_left_comm] using hsafeB
    let ra := Real.sqrt alpha
    let rtwo := Real.sqrt 2
    have hraSq : ra ^ 2 = alpha := by
      dsimp [ra]
      exact Real.sq_sqrt (le_of_lt halpha)
    have hrtwoSq : rtwo ^ 2 = 2 := by
      dsimp [rtwo]
      exact Real.sq_sqrt (by norm_num)
    have hrtwoPos : 0 < rtwo := by dsimp [rtwo]; positivity
    have hsEq : s = rtwo * ra := by
      dsimp [s, rtwo, ra]
      rw [Real.sqrt_mul (by norm_num : (0 : Real) <= 2)]
    have hsRoot : s * Real.sqrt alpha = Real.sqrt 2 * alpha := by
      rw [hsEq]
      change rtwo * ra * ra = rtwo * alpha
      calc
        rtwo * ra * ra = rtwo * ra ^ 2 := by ring
        _ = rtwo * alpha := by rw [hraSq]
    have hratio : s * Real.sqrt alpha * s ^ 2 =
        2 * Real.sqrt 2 * alpha ^ 2 := by
      rw [hssq, hsRoot]
      ring
    have hcoeff : C * rho * v ^ 2 = A * c ^ 2 := by
      calc
        C * rho * v ^ 2 = A * c ^ 2 *
            (s * Real.sqrt alpha * s ^ 2 /
              (2 * Real.sqrt 2 * alpha ^ 2)) := by
          dsimp [C, rho, v]
          field_simp [ne_of_gt hB, ne_of_gt hf, ne_of_gt he,
            ne_of_gt halpha, ne_of_gt hrtwoPos]
          ring
        _ = A * c ^ 2 := by
          rw [hratio]
          field_simp [ne_of_gt hrtwoPos, ne_of_gt halpha]
    have hpsi := psi_le_huberObjective
      (xi := xi) (rho := rho) hrho hv
    calc
      C * psi xi rho <= C * huberObjective xi rho v :=
        mul_le_mul_of_nonneg_left hpsi (le_of_lt hC)
      _ = C * rho * v ^ 2 + C * max t 0 := by
        unfold huberObjective
        dsimp [t]
        ring
      _ = A * c ^ 2 + C * max t 0 := by rw [hcoeff]
      _ <= A * c ^ 2 + B * gsSq := add_le_add (le_refl _) hmaxPay

/-- Sign-free form of exact Huber elimination.  The two direct inequalities
are precisely the positive-part estimates for the two orientations of the
frontier eigenfunction. -/
theorem exact_huber_shape_elimination_two_sided
    {alpha q L A B c gsSq z b K : Real}
    (halpha : 0 < alpha) (halphaHalf : alpha < 1 / 2)
    (hqalpha : q < alpha) (hLalpha : L < alpha)
    (hA : 0 <= A) (hB : 0 < B)
    (hK : 0 <= K) (hgs : 0 <= gsSq)
    (hz : 2 * alpha <= z) (hshape : z + b ^ 2 + K = 1)
    (hdirect : 2 * c * Real.sqrt z + 2 * alpha * b <= z - 2 * alpha)
    (hdirectNeg : -2 * c * Real.sqrt z - 2 * alpha * b <= z - 2 * alpha)
    (hsafe : max (shapeThreshold alpha q L z K - b * c) 0 ^ 2 <=
      gsSq * K) :
    let e := 1 - 2 * alpha
    let d := alpha - q
    let f := alpha - L
    let C := B * f * Real.sqrt (2 * alpha) * e ^ 2 / (4 * alpha ^ 2)
    let xi := 4 * alpha ^ 2 * d / e ^ 2
    let rho := (A / B) *
      (Real.sqrt alpha / (2 * Real.sqrt 2 * f))
    C * psi xi rho <= A * c ^ 2 + B * gsSq := by
  dsimp only
  by_cases hb : 0 <= b
  · exact exact_huber_shape_elimination halpha halphaHalf hqalpha hLalpha
      hA hB hb hK hgs hz hshape hdirect hsafe
  · have hbneg : b < 0 := lt_of_not_ge hb
    have hshape' : z + (-b) ^ 2 + K = 1 := by
      simpa only [neg_sq] using hshape
    have hdirect' : 2 * (-c) * Real.sqrt z + 2 * alpha * (-b) <=
        z - 2 * alpha := by
      linarith
    have hsafe' :
        max (shapeThreshold alpha q L z K - (-b) * (-c)) 0 ^ 2 <=
          gsSq * K := by
      simpa only [neg_mul_neg] using hsafe
    have hpay := exact_huber_shape_elimination
      (alpha := alpha) (q := q) (L := L) (A := A) (B := B)
      (c := -c) (gsSq := gsSq) (z := z) (b := -b) (K := K)
      halpha halphaHalf hqalpha hLalpha hA hB (by linarith) hK hgs hz
      hshape' hdirect' hsafe'
    simpa only [neg_sq] using hpay

end OddCycleBound.RegionII.Scalar
