import OddCycleBound.RegionII.Certificate.ZoneBBox

/-!
# Analytic interpretation of a Zone-B rational box

The certifier bounds the real chart variables by monotone substitutions at
the four rational endpoints.  This file proves those substitutions for
`x`, the maximization parameter `A`, `log (1/x)`, and the elementary
square-root envelope.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

def bAReal (P : AdmissibleParams) : Real :=
  P.x * (1 + P.kappa) / P.kappa

def bLambdaReal (P : AdmissibleParams) : Real := Real.log (1 / P.x)

def bEllBar (e : Real) : Real := Real.sqrt (2 * e / (1 - e))

def bRhoUnder (e k : Real) : Real :=
  (1 - Real.exp (-(1737 / 100 : Real) * (1 + k) * e)) / 4

def bEpsBar (e k rho : Real) : Real :=
  min (1 / 4) (e / (4 * (1 - e) ^ 2 * k * (1 + rho)))

def bPiUnder (e k : Real) : Real :=
  Real.sqrt (1 - e) * (1 - bEllBar e) * (1 - bEllBar e ^ 14) *
    (1 - bEpsBar e k (bRhoUnder e k)) / (1 + bEllBar e)

def bLambdaBar (P : AdmissibleParams) : Real :=
  P.x ^ 13 * (2 * P.e / (1 - P.e)) ^ 6 * bEllBar P.e *
    (1 - P.e) ^ 2 / (15 * P.e)

def bK1Real (P : AdmissibleParams) : Real :=
  P.x ^ 14 * max 0 (14 - bAReal P) / 15

def bWReal (phi : Real) : Real :=
  (Real.sqrt (phi ^ 2 + 4 * phi) - phi) / 2

lemma bWReal_nonneg {phi : Real} (hphi : 0 <= phi) : 0 <= bWReal phi := by
  have hsqrt : phi <= Real.sqrt (phi ^ 2 + 4 * phi) := by
    apply (Real.le_sqrt hphi (by nlinarith)).2
    nlinarith
  unfold bWReal
  linarith

lemma bWReal_le_one {phi : Real} (hphi : 0 <= phi) : bWReal phi <= 1 := by
  have hsquare : phi ^ 2 + 4 * phi <= (phi + 2) ^ 2 := by ring_nf; norm_num
  have hsqrt : Real.sqrt (phi ^ 2 + 4 * phi) <= phi + 2 := by
    exact (Real.sqrt_le_iff.mpr ⟨by linarith, hsquare⟩)
  unfold bWReal
  linarith

lemma bWReal_quadratic {phi : Real} (hphi : 0 <= phi) :
    bWReal phi ^ 2 + phi * bWReal phi = phi := by
  have hdisc : 0 <= phi ^ 2 + 4 * phi := by nlinarith
  have hsquare := Real.sq_sqrt hdisc
  unfold bWReal
  nlinarith

lemma bWReal_monotone {a b : Real} (ha : 0 <= a) (hab : a <= b) :
    bWReal a <= bWReal b := by
  have hb : 0 <= b := ha.trans hab
  have hwa0 := bWReal_nonneg ha
  have hwb0 := bWReal_nonneg hb
  have hwa1 := bWReal_le_one ha
  have hqa := bWReal_quadratic ha
  have hqb := bWReal_quadratic hb
  have hsub : bWReal a ^ 2 + b * bWReal a <= b := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab)
      (sub_nonpos.mpr hwa1)]
  by_contra hnot
  have hlt : bWReal b < bWReal a := lt_of_not_ge hnot
  have hfactor : 0 < bWReal a + bWReal b + b := by
    nlinarith
  nlinarith [mul_pos (sub_pos.mpr hlt) hfactor]

def bPhiReal (e k : Real) : Real :=
  2 * (1 - e) * e * (1 + k) ^ 2 /
    (k * (1 + e + 2 * k * e) ^ 2)

def bK2Real (P : AdmissibleParams) : Real :=
  Real.exp (-bPhiReal P.e P.kappa - 2 * bWReal (bPhiReal P.e P.kappa))

namespace BBoxContext

variable {P : AdmissibleParams} {box : RatBox} (H : BBoxContext P box)

include H

lemma placed_rat :
    zoneBRoot.e1 <= box.e1 ∧ box.e1 <= box.e2 ∧ box.e2 <= zoneBRoot.e2 ∧
      zoneBRoot.k1 <= box.k1 ∧ box.k1 <= box.k2 ∧ box.k2 <= zoneBRoot.k2 := by
  simpa [wellPlacedB] using H.placed

lemma e_bounds :
    (box.e1 : Real) <= P.e ∧ P.e <= (box.e2 : Real) :=
  ⟨H.point.1, H.point.2.1⟩

lemma k_bounds :
    (box.k1 : Real) <= P.kappa ∧ P.kappa <= (box.k2 : Real) :=
  H.point.2.2

lemma e1_pos : (0 : Real) < box.e1 := by
  have hq := (H.placed_rat).1
  have hqR : (zoneBRoot.e1 : Real) <= (box.e1 : Real) := by
    exact_mod_cast hq
  have : (0 : Real) < (zoneBRoot.e1 : Real) := by
    norm_num [zoneBRoot]
  exact this.trans_le hqR

lemma e2_lt_one : (box.e2 : Real) < 1 := by
  have hq := (H.placed_rat).2.2.1
  have hqR : (box.e2 : Real) <= (zoneBRoot.e2 : Real) := by
    exact_mod_cast hq
  have : (zoneBRoot.e2 : Real) < 1 := by
    norm_num [zoneBRoot]
  exact hqR.trans_lt this

lemma k1_pos : (0 : Real) < box.k1 := by
  have hq := (H.placed_rat).2.2.2.1
  have hqR : (zoneBRoot.k1 : Real) <= (box.k1 : Real) := by
    exact_mod_cast hq
  have : (0 : Real) < (zoneBRoot.k1 : Real) := by
    norm_num [zoneBRoot, kappaXiQ]
  exact this.trans_le hqR

lemma k2_le_one : (box.k2 : Real) <= 1 := by
  have hq := (H.placed_rat).2.2.2.2.2
  norm_num [zoneBRoot] at hq
  exact_mod_cast hq

lemma x_bounds :
    (bXMin box : Real) <= P.x ∧ P.x <= (bXMax box : Real) := by
  constructor
  · rw [bXMin, P.x_eq_chartXR, cast_chartXQ]
    exact chartXR_antitone P.e_pos.le H.e_bounds.2 H.e2_lt_one
      P.kappa_pos.le H.k_bounds.2
  · rw [bXMax, P.x_eq_chartXR, cast_chartXQ]
    exact chartXR_antitone H.e1_pos.le H.e_bounds.1
      (P.e_lt_third.trans (by norm_num)) H.k1_pos.le H.k_bounds.1

lemma xMin_pos : (0 : Real) < bXMin box := by
  rw [bXMin, cast_chartXQ]
  unfold chartXR
  have hnum : 0 < 1 - (box.e2 : Real) := by linarith [H.e2_lt_one]
  have hk2 : (0 : Real) <= box.k2 := H.k1_pos.le.trans H.k_bounds.1 |>.trans H.k_bounds.2
  exact div_pos hnum (chartXR_den_pos (H.e1_pos.le.trans H.e_bounds.1 |>.trans H.e_bounds.2) hk2)

lemma xMax_lt_one : (bXMax box : Real) < 1 := by
  rw [bXMax, cast_chartXQ]
  unfold chartXR
  have hden := chartXR_den_pos H.e1_pos.le H.k1_pos.le
  apply (div_lt_one hden).2
  have hprod : 0 < (box.k1 : Real) * (box.e1 : Real) :=
    mul_pos H.k1_pos H.e1_pos
  have he1 : (0 : Real) < box.e1 := H.e1_pos
  nlinarith

lemma ratio_endpoint_bounds :
    (1 + (box.k2 : Real)) / (box.k2 : Real) <=
        (1 + P.kappa) / P.kappa ∧
      (1 + P.kappa) / P.kappa <=
        (1 + (box.k1 : Real)) / (box.k1 : Real) := by
  have hk := P.kappa_pos
  have hk1 := H.k1_pos
  have hk2 : (0 : Real) < box.k2 := hk.trans_le H.k_bounds.2
  constructor
  · rw [div_le_div_iff₀ hk2 hk]
    nlinarith [H.k_bounds.2]
  · rw [div_le_div_iff₀ hk hk1]
    nlinarith [H.k_bounds.1]

lemma A_bounds :
    (bAMin box : Real) <= bAReal P ∧ bAReal P <= (bAMax box : Real) := by
  have hx0 : (0 : Real) <= bXMin box := H.xMin_pos.le
  have hxp : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
  have hxM : 0 <= (bXMax box : Real) := hxp.trans H.x_bounds.2
  have hk2 : (0 : Real) < box.k2 := P.kappa_pos.trans_le H.k_bounds.2
  have hr0 : 0 <= (1 + (box.k2 : Real)) / (box.k2 : Real) :=
    div_nonneg (by linarith) hk2.le
  have hrp : 0 <= (1 + P.kappa) / P.kappa :=
    div_nonneg (by linarith [P.kappa_pos]) P.kappa_pos.le
  constructor
  · rw [bAMin, bAReal]
    push_cast
    calc
      (bXMin box : Real) * (1 + (box.k2 : Real)) / (box.k2 : Real) =
          (bXMin box : Real) *
            ((1 + (box.k2 : Real)) / (box.k2 : Real)) := by ring
      _ <= P.x * ((1 + (box.k2 : Real)) / (box.k2 : Real)) :=
        mul_le_mul_of_nonneg_right H.x_bounds.1 hr0
      _ <= P.x * ((1 + P.kappa) / P.kappa) :=
        mul_le_mul_of_nonneg_left H.ratio_endpoint_bounds.1 hxp
      _ = P.x * (1 + P.kappa) / P.kappa := by ring
  · rw [bAMax, bAReal]
    push_cast
    calc
      P.x * (1 + P.kappa) / P.kappa =
          P.x * ((1 + P.kappa) / P.kappa) := by ring
      _ <= (bXMax box : Real) * ((1 + P.kappa) / P.kappa) :=
        mul_le_mul_of_nonneg_right H.x_bounds.2 hrp
      _ <= (bXMax box : Real) *
          ((1 + (box.k1 : Real)) / (box.k1 : Real)) :=
        mul_le_mul_of_nonneg_left H.ratio_endpoint_bounds.2 hxM
      _ = (bXMax box : Real) * (1 + (box.k1 : Real)) /
          (box.k1 : Real) := by ring

lemma lamMin_le_lambda : (bLamMin box : Real) <= bLambdaReal P := by
  have hx : 0 < P.x := div_pos P.alpha_pos P.p_pos
  have hlog := Real.log_le_sub_one_of_pos hx
  have hneg : 1 - P.x <= Real.log (1 / P.x) := by
    rw [Real.log_div (by norm_num : (1 : Real) ≠ 0) hx.ne', Real.log_one]
    linarith
  rw [bLamMin, bLambdaReal]
  push_cast
  exact (sub_le_sub_left H.x_bounds.2 1).trans hneg

lemma ellSq_le_l2Up :
    2 * P.e / (1 - P.e) <= (bL2Up box : Real) := by
  have hdP : 0 < 1 - P.e := by linarith [P.e_lt_third]
  have hd2 : 0 < 1 - (box.e2 : Real) := by linarith [H.e2_lt_one]
  rw [bL2Up]
  push_cast
  rw [div_le_div_iff₀ hdP hd2]
  nlinarith [H.e_bounds.2]

lemma ellBar_le_lUp (E : BVerifiedEvidence box) :
    bEllBar P.e <= (bLUp box : Real) := by
  have hsqrt := (sqrtBracketOK_sound E.sqrtL).2
  rw [bEllBar]
  exact (Real.sqrt_le_sqrt H.ellSq_le_l2Up).trans hsqrt

lemma lUp_lt_one (E : BVerifiedEvidence box) :
    (bLUp box : Real) < 1 := by
  norm_cast
  exact E.lUp_lt_one

lemma tRho_nonneg : (0 : Real) <= bTRho box := by
  rw [bTRho]
  push_cast
  exact mul_nonneg
    (mul_nonneg (by norm_num) (by linarith [H.k1_pos])) H.e1_pos.le

lemma tRho_le_real : (bTRho box : Real) <=
    (1737 / 100 : Real) * (1 + P.kappa) * P.e := by
  rw [bTRho]
  push_cast
  have hc : (0 : Real) <= 1737 / 100 := by norm_num
  have h1k : 0 <= 1 + (box.k1 : Real) := by linarith [H.k1_pos]
  calc
    (1737 / 100 : Real) * (1 + (box.k1 : Real)) * (box.e1 : Real) <=
        (1737 / 100 : Real) * (1 + P.kappa) * (box.e1 : Real) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [H.k_bounds.1]) hc)
        H.e1_pos.le
    _ <= (1737 / 100 : Real) * (1 + P.kappa) * P.e := by
      exact mul_le_mul_of_nonneg_left H.e_bounds.1
        (mul_nonneg hc (by linarith [P.kappa_pos]))

lemma rhoLo_nonneg : (0 : Real) <= bRhoLo box := by
  have hexp := expNegUpB_le_one (t := bTRho box) (by
    have : (0 : Real) <= (bTRho box : Real) := H.tRho_nonneg
    exact_mod_cast this)
  rw [bRhoLo]
  push_cast
  linarith

lemma rhoLo_le_rhoUnder : (bRhoLo box : Real) <=
    bRhoUnder P.e P.kappa := by
  have htQ : (0 : ℚ) <= bTRho box := by
    have htR := H.tRho_nonneg
    exact_mod_cast htR
  have hsound := expNegUpB_sound htQ
  have hexpMono :
      Real.exp (-((1737 / 100 : Real) * (1 + P.kappa) * P.e)) <=
        Real.exp (-(bTRho box : Real)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg H.tRho_le_real)
  have hupper :
      Real.exp (-(1737 / 100 : Real) * (1 + P.kappa) * P.e) <=
        (expNegUpB (bTRho box) : Real) := by
    calc
      Real.exp (-(1737 / 100 : Real) * (1 + P.kappa) * P.e) =
          Real.exp (-((1737 / 100 : Real) * (1 + P.kappa) * P.e)) := by
        congr 1
        ring
      _ <= Real.exp (-(bTRho box : Real)) := hexpMono
      _ <= (expNegUpB (bTRho box) : Real) := hsound
  rw [bRhoLo, bRhoUnder]
  push_cast
  linarith

lemma epsBar_le_epsUp :
    bEpsBar P.e P.kappa (bRhoUnder P.e P.kappa) <=
      (bEpsUp box : Real) := by
  have hnum := kappaXi_monotone P.e_pos.le H.e_bounds.2 H.e2_lt_one
  have hk := P.kappa_pos
  have hk1 := H.k1_pos
  have hrhoLo := H.rhoLo_nonneg
  have hrho := H.rhoLo_le_rhoUnder
  have hdenLo : 0 < 4 * (box.k1 : Real) * (1 + (bRhoLo box : Real)) := by
    positivity
  have hden : 0 < 4 * P.kappa * (1 + bRhoUnder P.e P.kappa) := by
    have hrho0 : 0 <= bRhoUnder P.e P.kappa := hrhoLo.trans hrho
    positivity
  have hfrac :
      P.e / ((1 - P.e) ^ 2) /
          (4 * P.kappa * (1 + bRhoUnder P.e P.kappa)) <=
        (box.e2 : Real) / (1 - (box.e2 : Real)) ^ 2 /
          (4 * (box.k1 : Real) * (1 + (bRhoLo box : Real))) := by
    have hdenOrder :
        4 * (box.k1 : Real) * (1 + (bRhoLo box : Real)) <=
          4 * P.kappa * (1 + bRhoUnder P.e P.kappa) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr H.k_bounds.1)
        (by linarith : 0 <= 1 + (bRhoLo box : Real)),
        mul_nonneg P.kappa_pos.le (sub_nonneg.mpr hrho)]
    calc
      P.e / (1 - P.e) ^ 2 /
          (4 * P.kappa * (1 + bRhoUnder P.e P.kappa)) <=
        ((box.e2 : Real) / (1 - (box.e2 : Real)) ^ 2) /
          (4 * P.kappa * (1 + bRhoUnder P.e P.kappa)) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ <= ((box.e2 : Real) / (1 - (box.e2 : Real)) ^ 2) /
          (4 * (box.k1 : Real) * (1 + (bRhoLo box : Real))) := by
        exact div_le_div_of_nonneg_left
          (div_nonneg (P.e_pos.le.trans H.e_bounds.2) (sq_nonneg _))
          hdenLo hdenOrder
  have hdirect :
      P.e /
          (4 * (1 - P.e) ^ 2 * P.kappa *
            (1 + bRhoUnder P.e P.kappa)) <=
        (box.e2 : Real) /
          (4 * (1 - (box.e2 : Real)) ^ 2 * (box.k1 : Real) *
            (1 + (bRhoLo box : Real))) := by
    calc
      P.e /
          (4 * (1 - P.e) ^ 2 * P.kappa *
            (1 + bRhoUnder P.e P.kappa)) =
        P.e / (1 - P.e) ^ 2 /
          (4 * P.kappa * (1 + bRhoUnder P.e P.kappa)) := by
        field_simp [P.kappa_pos.ne',
          (by linarith [P.e_lt_third] : (1 - P.e) ≠ 0),
          (by
            have hrho0 : 0 <= bRhoUnder P.e P.kappa := hrhoLo.trans hrho
            linarith : (1 + bRhoUnder P.e P.kappa) ≠ 0)]
      _ <= (box.e2 : Real) / (1 - (box.e2 : Real)) ^ 2 /
          (4 * (box.k1 : Real) * (1 + (bRhoLo box : Real))) := hfrac
      _ = (box.e2 : Real) /
          (4 * (1 - (box.e2 : Real)) ^ 2 * (box.k1 : Real) *
            (1 + (bRhoLo box : Real))) := by
        field_simp [H.k1_pos.ne',
          (by linarith [H.e2_lt_one] : (1 - (box.e2 : Real)) ≠ 0),
          (by linarith [hrhoLo] : (1 + (bRhoLo box : Real)) ≠ 0)]
  rw [bEpsBar, bEpsUp]
  push_cast
  exact min_le_min le_rfl hdirect

lemma ellBar_nonneg : 0 <= bEllBar P.e := by
  unfold bEllBar
  exact Real.sqrt_nonneg _

lemma ellBar_lt_one (E : BVerifiedEvidence box) : bEllBar P.e < 1 :=
  (H.ellBar_le_lUp E).trans_lt (H.lUp_lt_one E)

lemma ellBar_pow_fourteen_le_l14Up (E : BVerifiedEvidence box) :
    bEllBar P.e ^ 14 <= (bL14Up box : Real) := by
  have harg : 0 <= 2 * P.e / (1 - P.e) :=
    div_nonneg (mul_nonneg (by norm_num) P.e_pos.le)
      (by linarith [P.e_lt_third])
  have hsquare : bEllBar P.e ^ 2 = 2 * P.e / (1 - P.e) := by
    unfold bEllBar
    exact Real.sq_sqrt harg
  have hpow : bEllBar P.e ^ 14 <= (bL2Up box : Real) ^ 7 := by
    rw [show bEllBar P.e ^ 14 = (bEllBar P.e ^ 2) ^ 7 by ring, hsquare]
    exact pow_le_pow_left₀ harg H.ellSq_le_l2Up 7
  have hone : bEllBar P.e ^ 14 <= 1 := by
    exact pow_le_one₀ H.ellBar_nonneg (H.ellBar_lt_one E).le
  rw [bL14Up]
  push_cast
  exact le_min hone hpow

lemma rootOneMinusE_le_sqrt (E : BVerifiedEvidence box) :
    (bRootOneMinusE box : Real) <= Real.sqrt (1 - P.e) := by
  have hbracket := (sqrtBracketOK_sound E.sqrtOneMinusE).1
  have hargs : (1 - (box.e2 : Real)) <= 1 - P.e := by
    linarith [H.e_bounds.2]
  have hbracket' : (bRootOneMinusE box : Real) <=
      Real.sqrt (1 - (box.e2 : Real)) := by
    simpa only [Rat.cast_sub, Rat.cast_one] using hbracket
  exact hbracket'.trans (Real.sqrt_le_sqrt hargs)

lemma epsUp_le_quarter : (bEpsUp box : Real) <= 1 / 4 := by
  rw [bEpsUp]
  push_cast
  exact min_le_left _ _

lemma epsBar_nonneg :
    0 <= bEpsBar P.e P.kappa (bRhoUnder P.e P.kappa) := by
  have hrho : 0 <= bRhoUnder P.e P.kappa :=
    H.rhoLo_nonneg.trans H.rhoLo_le_rhoUnder
  unfold bEpsBar
  apply le_min (by norm_num)
  exact div_nonneg P.e_pos.le
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _)) P.kappa_pos.le)
      (by linarith))

lemma piLo_le_piUnder (E : BVerifiedEvidence box) :
    (bPiLo box : Real) <= bPiUnder P.e P.kappa := by
  let rlo : Real := (bRootOneMinusE box : Real)
  let r : Real := Real.sqrt (1 - P.e)
  let l : Real := bEllBar P.e
  let lu : Real := (bLUp box : Real)
  let l14u : Real := (bL14Up box : Real)
  let eps : Real := bEpsBar P.e P.kappa (bRhoUnder P.e P.kappa)
  let epsu : Real := (bEpsUp box : Real)
  have hrlo : 0 <= rlo := by
    have hraw := E.sqrtOneMinusE
    simp only [sqrtBracketOK, decide_eq_true_eq] at hraw
    have hq : 0 <= bRootOneMinusE box := hraw.1
    dsimp [rlo]
    exact_mod_cast hq
  have hr : 0 <= r := by exact Real.sqrt_nonneg _
  have hroot : rlo <= r := by simpa [rlo, r] using H.rootOneMinusE_le_sqrt E
  have hl : 0 <= l := by simpa [l] using H.ellBar_nonneg
  have hlu : 0 <= lu := hl.trans (by simpa [l, lu] using H.ellBar_le_lUp E)
  have hlu1 : lu < 1 := by simpa [lu] using H.lUp_lt_one E
  have hl14u : l ^ 14 <= l14u := by
    simpa [l, l14u] using H.ellBar_pow_fourteen_le_l14Up E
  have hl14uOne : l14u <= 1 := by
    dsimp [l14u]
    rw [bL14Up]
    push_cast
    exact min_le_left _ _
  have heps : 0 <= eps := by simpa [eps] using H.epsBar_nonneg
  have hepsu : eps <= epsu := by simpa [eps, epsu] using H.epsBar_le_epsUp
  have hepsuQuarter : epsu <= 1 / 4 := by
    simpa [epsu] using H.epsUp_le_quarter
  have hrootFactor : rlo * (1 - lu) <= r * (1 - l) := by
    exact mul_le_mul hroot (by linarith [H.ellBar_le_lUp E])
      (by linarith [hlu1]) hr
  have hthird :
      rlo * (1 - lu) * (1 - l14u) <=
        r * (1 - l) * (1 - l ^ 14) := by
    exact mul_le_mul hrootFactor (by linarith [hl14u])
      (by linarith [hl14uOne])
      (mul_nonneg hr (by linarith [H.ellBar_lt_one E]))
  have hnum :
      rlo * (1 - lu) * (1 - l14u) * (1 - epsu) <=
        r * (1 - l) * (1 - l ^ 14) * (1 - eps) := by
    exact mul_le_mul hthird (by linarith [hepsu])
      (by linarith [hepsuQuarter])
      (mul_nonneg
        (mul_nonneg hr (by linarith [H.ellBar_lt_one E]))
        (by exact sub_nonneg.mpr (pow_le_one₀ hl (H.ellBar_lt_one E).le)))
  have hnumLo : 0 <= rlo * (1 - lu) * (1 - l14u) * (1 - epsu) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hrlo (by linarith [hlu1]))
        (by linarith [hl14uOne]))
      (by linarith [hepsuQuarter])
  have hnumR : 0 <= r * (1 - l) * (1 - l ^ 14) * (1 - eps) :=
    hnumLo.trans hnum
  have hden : 0 < 1 + l := by linarith
  have hdenu : 0 < 1 + lu := by linarith
  have hdens : 1 + l <= 1 + lu := by
    linarith [H.ellBar_le_lUp E]
  rw [bPiLo, bPiUnder]
  push_cast
  change rlo * (1 - lu) * (1 - l14u) * (1 - epsu) / (1 + lu) <=
    r * (1 - l) * (1 - l ^ 14) * (1 - eps) / (1 + l)
  rw [div_le_div_iff₀ hdenu hden]
  calc
    (rlo * (1 - lu) * (1 - l14u) * (1 - epsu)) * (1 + l) <=
        (r * (1 - l) * (1 - l ^ 14) * (1 - eps)) * (1 + l) :=
      mul_le_mul_of_nonneg_right hnum hden.le
    _ <= (r * (1 - l) * (1 - l ^ 14) * (1 - eps)) * (1 + lu) :=
      mul_le_mul_of_nonneg_left hdens hnumR

lemma tail_ratio_le_endpoint :
    (1 - P.e) ^ 2 / P.e <=
      (1 - (box.e1 : Real)) ^ 2 / (box.e1 : Real) := by
  rw [div_le_div_iff₀ P.e_pos H.e1_pos]
  have he := H.e_bounds.1
  have he1third : (box.e1 : Real) < 1 :=
    he.trans_lt P.e_lt_third |>.trans (by norm_num)
  have hprod : (box.e1 : Real) * P.e < 1 := by
    calc
      (box.e1 : Real) * P.e <= 1 * P.e :=
        mul_le_mul_of_nonneg_right he1third.le P.e_pos.le
      _ = P.e := by ring
      _ < 1 := P.e_lt_third.trans (by norm_num)
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hprod.le)]

lemma lambdaBar_le_lambdaUp (E : BVerifiedEvidence box) :
    bLambdaBar P <= (bLambdaUp box : Real) := by
  have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
  have hxM0 : 0 <= (bXMax box : Real) := hx0.trans H.x_bounds.2
  have hl20 : 0 <= 2 * P.e / (1 - P.e) :=
    div_nonneg (mul_nonneg (by norm_num) P.e_pos.le)
      (by linarith [P.e_lt_third])
  have hl2u0 : 0 <= (bL2Up box : Real) := hl20.trans H.ellSq_le_l2Up
  have hl0 := H.ellBar_nonneg
  have hlu0 : 0 <= (bLUp box : Real) := hl0.trans (H.ellBar_le_lUp E)
  have htail0 : 0 <= (1 - P.e) ^ 2 / P.e :=
    div_nonneg (sq_nonneg _) P.e_pos.le
  have h1 : P.x ^ 13 <= (bXMax box : Real) ^ 13 :=
    pow_le_pow_left₀ hx0 H.x_bounds.2 13
  have h2 : (2 * P.e / (1 - P.e)) ^ 6 <=
      (bL2Up box : Real) ^ 6 :=
    pow_le_pow_left₀ hl20 H.ellSq_le_l2Up 6
  have hp1 : P.x ^ 13 * (2 * P.e / (1 - P.e)) ^ 6 <=
      (bXMax box : Real) ^ 13 * (bL2Up box : Real) ^ 6 :=
    mul_le_mul h1 h2 (pow_nonneg hl20 6) (pow_nonneg hxM0 13)
  have hp2 :
      P.x ^ 13 * (2 * P.e / (1 - P.e)) ^ 6 * bEllBar P.e <=
        (bXMax box : Real) ^ 13 * (bL2Up box : Real) ^ 6 *
          (bLUp box : Real) :=
    mul_le_mul hp1 (H.ellBar_le_lUp E) hl0
      (mul_nonneg (pow_nonneg hxM0 13) (pow_nonneg hl2u0 6))
  have htail15 : (1 - P.e) ^ 2 / (15 * P.e) <=
      (1 - (box.e1 : Real)) ^ 2 / (15 * (box.e1 : Real)) := by
    calc
      (1 - P.e) ^ 2 / (15 * P.e) =
          ((1 - P.e) ^ 2 / P.e) / 15 := by ring
      _ <= (((1 - (box.e1 : Real)) ^ 2 / (box.e1 : Real)) / 15) :=
        div_le_div_of_nonneg_right H.tail_ratio_le_endpoint (by norm_num)
      _ = (1 - (box.e1 : Real)) ^ 2 /
          (15 * (box.e1 : Real)) := by ring
  have htail150 : 0 <= (1 - P.e) ^ 2 / (15 * P.e) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) P.e_pos.le)
  rw [bLambdaBar, bLambdaUp]
  push_cast
  calc
    P.x ^ 13 * (2 * P.e / (1 - P.e)) ^ 6 * bEllBar P.e *
        (1 - P.e) ^ 2 / (15 * P.e) =
      (P.x ^ 13 * (2 * P.e / (1 - P.e)) ^ 6 * bEllBar P.e) *
        ((1 - P.e) ^ 2 / (15 * P.e)) := by ring
    _ <= ((bXMax box : Real) ^ 13 * (bL2Up box : Real) ^ 6 *
        (bLUp box : Real)) *
          ((1 - (box.e1 : Real)) ^ 2 / (15 * (box.e1 : Real))) :=
      mul_le_mul hp2 htail15 htail150
        (mul_nonneg
          (mul_nonneg (pow_nonneg hxM0 13) (pow_nonneg hl2u0 6)) hlu0)
    _ = (bXMax box : Real) ^ 13 * (bL2Up box : Real) ^ 6 *
        (bLUp box : Real) * (1 - (box.e1 : Real)) ^ 2 /
          (15 * (box.e1 : Real)) := by ring

lemma k1Real_le_k1Up : bK1Real P <= (bK1Up box : Real) := by
  have hx0 : 0 <= P.x := div_nonneg P.alpha_nonneg P.p_pos.le
  have hxM0 : 0 <= (bXMax box : Real) := hx0.trans H.x_bounds.2
  have hpow : P.x ^ 14 <= (bXMax box : Real) ^ 14 :=
    pow_le_pow_left₀ hx0 H.x_bounds.2 14
  have hgap : max 0 (14 - bAReal P) <=
      max 0 (14 - (bAMin box : Real)) := by
    exact max_le_max le_rfl (sub_le_sub_left H.A_bounds.1 14)
  rw [bK1Real, bK1Up]
  push_cast
  exact div_le_div_of_nonneg_right
    (mul_le_mul hpow hgap (le_max_left 0 _) (pow_nonneg hxM0 14))
    (by norm_num)

lemma phiMin_nonneg : (0 : Real) <= bPhiMin box := by
  rw [bPhiMin]
  push_cast
  have hk2 : (0 : Real) < box.k2 := P.kappa_pos.trans_le H.k_bounds.2
  have he2nonneg : (0 : Real) <= box.e2 := P.e_pos.le.trans H.e_bounds.2
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (by linarith [H.e2_lt_one])) H.e1_pos.le)
      (sq_nonneg _))
    (mul_nonneg hk2.le (sq_nonneg _))

lemma phiMin_le_phiReal : (bPhiMin box : Real) <=
    bPhiReal P.e P.kappa := by
  let k := P.kappa
  let K : Real := (box.k2 : Real)
  let e := P.e
  let E : Real := (box.e2 : Real)
  let e0 : Real := (box.e1 : Real)
  let den := 1 + e + 2 * k * e
  let denUp := 1 + E + 2 * K * E
  have hk : 0 < k := P.kappa_pos
  have hK : 0 < K := by simpa [K] using P.kappa_pos.trans_le H.k_bounds.2
  have hkK : k <= K := by simpa [k, K] using H.k_bounds.2
  have hK1 : K <= 1 := by simpa [K] using H.k2_le_one
  have he : 0 < e := P.e_pos
  have heE : e <= E := by simpa [e, E] using H.e_bounds.2
  have he0e : e0 <= e := by simpa [e0, e] using H.e_bounds.1
  have hE1 : E < 1 := by simpa [E] using H.e2_lt_one
  have hratio : (1 + K) ^ 2 / K <= (1 + k) ^ 2 / k := by
    rw [div_le_div_iff₀ hK hk]
    have hfac : 0 <= (K - k) * (1 - k * K) := by
      exact mul_nonneg (sub_nonneg.mpr hkK)
        (by nlinarith [mul_le_mul hkK hK1 hK.le hK.le])
    nlinarith
  have hbase : (1 - E) * e0 <= (1 - e) * e := by
    have hleft : (1 - E) * e0 <= (1 - e) * e0 :=
      mul_le_mul_of_nonneg_right (by linarith [heE]) H.e1_pos.le
    have hright : (1 - e) * e0 <= (1 - e) * e :=
      mul_le_mul_of_nonneg_left he0e (by linarith [P.e_lt_third])
    exact hleft.trans hright
  have hden : 0 < den := by
    dsimp [den, e, k]
    exact chartXR_den_pos P.e_pos.le P.kappa_pos.le
  have hdenUp : 0 < denUp := by
    dsimp [denUp]
    exact chartXR_den_pos (P.e_pos.le.trans heE) hK.le
  have hdenOrder : den <= denUp := by
    dsimp [den, denUp]
    have hprod : k * e <= K * E :=
      (mul_le_mul hkK heE he.le hK.le)
    linarith
  have hnum :
      2 * (1 - E) * e0 * ((1 + K) ^ 2 / K) <=
        2 * (1 - e) * e * ((1 + k) ^ 2 / k) := by
    have hr0 : 0 <= (1 + K) ^ 2 / K := div_nonneg (sq_nonneg _) hK.le
    have hb0 : 0 <= 2 * (1 - e) * e :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith [P.e_lt_third])) he.le
    calc
      2 * (1 - E) * e0 * ((1 + K) ^ 2 / K) <=
          2 * (1 - e) * e * ((1 + K) ^ 2 / K) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hbase]) hr0
      _ <= 2 * (1 - e) * e * ((1 + k) ^ 2 / k) :=
        mul_le_mul_of_nonneg_left hratio hb0
  have hnum0 : 0 <= 2 * (1 - E) * e0 * ((1 + K) ^ 2 / K) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hE1])) H.e1_pos.le)
      (div_nonneg (sq_nonneg _) hK.le)
  rw [bPhiMin, bPhiReal]
  push_cast
  change (2 * (1 - E) * e0 * (1 + K) ^ 2) /
      (K * denUp ^ 2) <=
    (2 * (1 - e) * e * (1 + k) ^ 2) / (k * den ^ 2)
  rw [show (2 * (1 - E) * e0 * (1 + K) ^ 2) / (K * denUp ^ 2) =
      (2 * (1 - E) * e0 * ((1 + K) ^ 2 / K)) / denUp ^ 2 by
        field_simp [hK.ne'],
    show (2 * (1 - e) * e * (1 + k) ^ 2) / (k * den ^ 2) =
      (2 * (1 - e) * e * ((1 + k) ^ 2 / k)) / den ^ 2 by
        field_simp [hk.ne']]
  rw [div_le_div_iff₀ (sq_pos_of_pos hdenUp) (sq_pos_of_pos hden)]
  calc
    (2 * (1 - E) * e0 * ((1 + K) ^ 2 / K)) * den ^ 2 <=
        (2 * (1 - E) * e0 * ((1 + K) ^ 2 / K)) * denUp ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hden.le hdenOrder 2) hnum0
    _ <= (2 * (1 - e) * e * ((1 + k) ^ 2 / k)) * denUp ^ 2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg denUp)

lemma wLo_nonneg : (0 : Real) <= bWLo box := by
  rw [bWLo]
  push_cast
  exact le_max_left _ _

lemma wLo_le_wReal (E : BVerifiedEvidence box)
    (hinterior : ¬ bOnlyK14 box) :
    (bWLo box : Real) <= bWReal (bPhiReal P.e P.kappa) := by
  have hdiscEv : sqrtBracketOK (bDisc box) (bDiscLo box)
      (sqrtUpB (bDisc box)) = true := by
    cases E.maximum with
    | endpoint hgate _ => exact False.elim (hinterior hgate)
    | interior _ hsqrt _ => exact hsqrt
  have hsqrt := (sqrtBracketOK_sound hdiscEv).1
  have hsqrt' : (bDiscLo box : Real) <=
      Real.sqrt ((bPhiMin box : Real) ^ 2 + 4 * (bPhiMin box : Real)) := by
    simpa [bDisc] using hsqrt
  have hphi0 := H.phiMin_nonneg
  have hw0 := bWReal_nonneg hphi0
  have hraw :
      ((bDiscLo box : Real) - (bPhiMin box : Real)) / 2 <=
        bWReal (bPhiMin box : Real) := by
    unfold bWReal
    linarith
  have hmax :
      max 0 (((bDiscLo box : Real) - (bPhiMin box : Real)) / 2) <=
        bWReal (bPhiMin box : Real) := max_le hw0 hraw
  calc
    (bWLo box : Real) =
        max 0 (((bDiscLo box : Real) - (bPhiMin box : Real)) / 2) := by
      rw [bWLo]
      push_cast
      rfl
    _ <= bWReal (bPhiMin box : Real) := hmax
    _ <= bWReal (bPhiReal P.e P.kappa) :=
      bWReal_monotone hphi0 H.phiMin_le_phiReal

lemma k2Real_le_k2Up (E : BVerifiedEvidence box)
    (hinterior : ¬ bOnlyK14 box) :
    bK2Real P <= (bK2Up box : Real) := by
  have htR : (0 : Real) <= (bPhiMin box : Real) + 2 * (bWLo box : Real) :=
    add_nonneg H.phiMin_nonneg (mul_nonneg (by norm_num) H.wLo_nonneg)
  have htQ : (0 : ℚ) <= bPhiMin box + 2 * bWLo box := by
    exact_mod_cast htR
  have hsound := expNegUpB_sound htQ
  have harg :
      (bPhiMin box : Real) + 2 * (bWLo box : Real) <=
        bPhiReal P.e P.kappa + 2 * bWReal (bPhiReal P.e P.kappa) := by
    linarith [H.phiMin_le_phiReal, H.wLo_le_wReal E hinterior]
  rw [bK2Real, bK2Up]
  calc
    Real.exp (-bPhiReal P.e P.kappa -
        2 * bWReal (bPhiReal P.e P.kappa)) <=
      Real.exp (-((bPhiMin box : Real) + 2 * (bWLo box : Real))) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = Real.exp (-(bPhiMin box + 2 * bWLo box : ℚ) : Real) := by
      congr 1
      push_cast
      ring
    _ <= (expNegUpB (bPhiMin box + 2 * bWLo box) : Real) := hsound

lemma k1Real_nonneg : 0 <= bK1Real P := by
  unfold bK1Real
  exact div_nonneg
    (mul_nonneg (pow_nonneg (div_nonneg P.alpha_nonneg P.p_pos.le) 14)
      (le_max_left 0 _)) (by norm_num)

lemma k2Real_nonneg : 0 <= bK2Real P := (Real.exp_pos _).le

lemma k1_div_x_sq_le_checked :
    bK1Real P / P.x ^ 2 <=
      (bK1Up box : Real) / (bXMin box : Real) ^ 2 := by
  have hx : 0 < P.x := div_pos P.alpha_pos P.p_pos
  have hxmin := H.xMin_pos
  have hsq : (bXMin box : Real) ^ 2 <= P.x ^ 2 :=
    pow_le_pow_left₀ hxmin.le H.x_bounds.1 2
  have hk1up0 : 0 <= (bK1Up box : Real) := H.k1Real_nonneg.trans H.k1Real_le_k1Up
  calc
    bK1Real P / P.x ^ 2 <= (bK1Up box : Real) / P.x ^ 2 :=
      div_le_div_of_nonneg_right H.k1Real_le_k1Up (sq_nonneg _)
    _ <= (bK1Up box : Real) / (bXMin box : Real) ^ 2 :=
      div_le_div_of_nonneg_left hk1up0 (sq_pos_of_pos hxmin) hsq

lemma max_div_x_sq_le_checked (E : BVerifiedEvidence box)
    (hinterior : ¬ bOnlyK14 box) :
    max (bK1Real P) (bK2Real P) / P.x ^ 2 <=
      max (bK1Up box : Real) (bK2Up box : Real) /
        (bXMin box : Real) ^ 2 := by
  have hx : 0 < P.x := div_pos P.alpha_pos P.p_pos
  have hxmin := H.xMin_pos
  have hsq : (bXMin box : Real) ^ 2 <= P.x ^ 2 :=
    pow_le_pow_left₀ hxmin.le H.x_bounds.1 2
  have hmax : max (bK1Real P) (bK2Real P) <=
      max (bK1Up box : Real) (bK2Up box : Real) :=
    max_le_max H.k1Real_le_k1Up (H.k2Real_le_k2Up E hinterior)
  have hmax0 : 0 <= max (bK1Up box : Real) (bK2Up box : Real) :=
    H.k1Real_nonneg.trans (le_max_of_le_left H.k1Real_le_k1Up)
  calc
    max (bK1Real P) (bK2Real P) / P.x ^ 2 <=
        max (bK1Up box : Real) (bK2Up box : Real) / P.x ^ 2 :=
      div_le_div_of_nonneg_right hmax (sq_nonneg _)
    _ <= max (bK1Up box : Real) (bK2Up box : Real) /
        (bXMin box : Real) ^ 2 :=
      div_le_div_of_nonneg_left hmax0 (sq_pos_of_pos hxmin) hsq

inductive BEnvelopeSound (P : AdmissibleParams) (box : RatBox) : Prop where
  | endpoint
      (gate : bOnlyK14 box)
      (battle : bPiUnder P.e P.kappa >=
        bK1Real P / P.x ^ 2 + bLambdaBar P)
  | interior
      (gate : ¬ bOnlyK14 box)
      (battle : bPiUnder P.e P.kappa >=
        max (bK1Real P) (bK2Real P) / P.x ^ 2 + bLambdaBar P)

lemma verified_envelope_sound (E : BVerifiedEvidence box) :
    BEnvelopeSound P box := by
  have hpi := H.piLo_le_piUnder E
  have hlam := H.lambdaBar_le_lambdaUp E
  cases E.maximum with
  | endpoint hgate hbattle =>
      refine BEnvelopeSound.endpoint hgate ?_
      have hk := H.k1_div_x_sq_le_checked
      have hbattleR' :
          (bK1Up box : Real) /
              ((bXMin box : Real) * (bXMin box : Real)) +
              (bLambdaUp box : Real) <= (bPiLo box : Real) := by
        exact_mod_cast hbattle
      have hbattleR :
          (bK1Up box : Real) / (bXMin box : Real) ^ 2 +
              (bLambdaUp box : Real) <= (bPiLo box : Real) := by
        simpa [pow_two] using hbattleR'
      exact (add_le_add hk hlam).trans hbattleR |>.trans hpi
  | interior hgate _ hbattle =>
      refine BEnvelopeSound.interior hgate ?_
      have hk := H.max_div_x_sq_le_checked E hgate
      have hbattleR' :
          max (bK1Up box : Real) (bK2Up box : Real) /
                ((bXMin box : Real) * (bXMin box : Real)) +
              (bLambdaUp box : Real) <=
            (bPiLo box : Real) := by
        exact_mod_cast hbattle
      have hbattleR :
          max (bK1Up box : Real) (bK2Up box : Real) /
                (bXMin box : Real) ^ 2 + (bLambdaUp box : Real) <=
            (bPiLo box : Real) := by
        simpa [pow_two] using hbattleR'
      exact (add_le_add hk hlam).trans hbattleR |>.trans hpi

end BBoxContext

end OddCycleBound.RegionII.Certificate
