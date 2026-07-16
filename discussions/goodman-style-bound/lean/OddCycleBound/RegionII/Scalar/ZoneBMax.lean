import OddCycleBound.RegionII.Certificate.ZoneBTreeSound

/-!
# Corrected Zone-B cycle-length maximization

The interior maximum is bounded without choosing a numerical stationary
point.  After the substitutions `t = lambda (n-A)` and
`nu = lambda (A+1)`, the Padé lower bound
`2 z / (z+2) <= log (1+z)` gives the exact exponential majorant used by the
certificate.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

def bKAt (P : AdmissibleParams) (n : Nat) : Real :=
  P.x ^ n * (((n : Nat) : Real) - bAReal P) / (((n : Nat) : Real) + 1)

lemma bLambdaReal_pos (P : AdmissibleParams) : 0 < bLambdaReal P := by
  unfold bLambdaReal
  apply Real.log_pos
  exact (one_lt_div (div_pos P.alpha_pos P.p_pos)).2 P.x_lt_one

lemma bAReal_pos (P : AdmissibleParams) : 0 < bAReal P := by
  unfold bAReal
  exact div_pos (mul_pos (div_pos P.alpha_pos P.p_pos)
    (by linarith [P.kappa_pos])) P.kappa_pos

lemma x_pow_eq_exp_neg_lambda_mul (P : AdmissibleParams) (n : Nat) :
    P.x ^ n = Real.exp (-bLambdaReal P * (n : Real)) := by
  have hx : 0 < P.x := div_pos P.alpha_pos P.p_pos
  rw [← Real.exp_log hx, ← Real.exp_nat_mul]
  congr 1
  unfold bLambdaReal
  rw [Real.log_div (by norm_num : (1 : Real) ≠ 0) hx.ne', Real.log_one]
  ring

lemma bPhiReal_nonneg (P : AdmissibleParams) :
    0 <= bPhiReal P.e P.kappa := by
  unfold bPhiReal
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (by linarith [P.e_lt_third])) P.e_pos.le)
      (sq_nonneg _))
    (mul_nonneg P.kappa_pos.le (sq_nonneg _))

lemma one_sub_x_mul_A_eq_phi (P : AdmissibleParams) :
    (1 - P.x) * bAReal P = bPhiReal P.e P.kappa := by
  have hk : P.kappa ≠ 0 := P.kappa_pos.ne'
  have hden : 1 + P.e + 2 * P.kappa * P.e ≠ 0 :=
    (chartXR_den_pos P.e_pos.le P.kappa_pos.le).ne'
  have hden' : 1 + P.e + P.e * P.kappa * 2 ≠ 0 := by
    convert hden using 1 <;> ring
  have hden_eq : 1 + P.e + 2 * P.kappa * P.e =
      1 + P.e + P.e * P.kappa * 2 := by ring
  have hmx : 1 - P.x =
      2 * P.e * (1 + P.kappa) /
        (1 + P.e + 2 * P.kappa * P.e) := by
    rw [P.x_eq_chartXR]
    unfold chartXR
    rw [hden_eq, eq_div_iff hden']
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hden']
    ring
  have hA : bAReal P =
      (1 - P.e) * (1 + P.kappa) /
        (P.kappa * (1 + P.e + 2 * P.kappa * P.e)) := by
    unfold bAReal
    rw [P.x_eq_chartXR]
    unfold chartXR
    field_simp [hk, hden, hden'] <;> ring
  rw [hmx, hA]
  unfold bPhiReal
  rw [div_mul_div_comm]
  congr 1 <;> ring

lemma one_sub_x_le_lambda (P : AdmissibleParams) :
    1 - P.x <= bLambdaReal P := by
  have hx : 0 < P.x := div_pos P.alpha_pos P.p_pos
  have hlog := Real.log_le_sub_one_of_pos hx
  unfold bLambdaReal
  rw [Real.log_div (by norm_num : (1 : Real) ≠ 0) hx.ne', Real.log_one]
  linarith

lemma phi_le_lambda_mul_A (P : AdmissibleParams) :
    bPhiReal P.e P.kappa <= bLambdaReal P * bAReal P := by
  rw [← one_sub_x_mul_A_eq_phi P]
  exact mul_le_mul_of_nonneg_right (one_sub_x_le_lambda P)
    (bAReal_pos P).le

lemma phi_le_nu (P : AdmissibleParams) :
    bPhiReal P.e P.kappa <= bLambdaReal P * (bAReal P + 1) := by
  calc
    bPhiReal P.e P.kappa <= bLambdaReal P * bAReal P :=
      phi_le_lambda_mul_A P
    _ <= bLambdaReal P * (bAReal P + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (bLambdaReal_pos P).le

lemma exp_mul_ratio_le_exp_neg_two_w {t nu : Real}
    (ht : 0 < t) (hnu : 0 < nu) :
    Real.exp (-t) * (t / (t + nu)) <= Real.exp (-2 * bWReal nu) := by
  let w := bWReal nu
  have hw0 : 0 <= w := bWReal_nonneg hnu.le
  have hweq : w ^ 2 + nu * w = nu := bWReal_quadratic hnu.le
  have hden : 0 < nu + 2 * t := by positivity
  have hcore : 2 * w <= t + 2 * nu / (nu + 2 * t) := by
    field_simp [hden.ne']
    nlinarith [sq_nonneg (t - w), mul_nonneg hnu.le ht.le]
  let z := nu / t
  have hz : 0 <= z := div_nonneg hnu.le ht.le
  have hlog := Real.le_log_one_add_of_nonneg hz
  have hpade : 2 * nu / (nu + 2 * t) <= Real.log (1 + nu / t) := by
    have heq : 2 * (nu / t) / (nu / t + 2) =
        2 * nu / (nu + 2 * t) := by
      field_simp [ht.ne']
    rw [← heq]
    simpa [z] using hlog
  have htotal : 2 * w <= t + Real.log (1 + nu / t) :=
    hcore.trans (by simpa [add_comm] using add_le_add_left hpade t)
  have hratio : t / (t + nu) =
      Real.exp (-Real.log (1 + nu / t)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 + nu / t)]
    field_simp [ht.ne']
  rw [hratio, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma bKAt_le_k2Real_of_A_lt_n (P : AdmissibleParams) (n : Nat)
    (hnA : bAReal P < (n : Real)) :
    bKAt P n <= bK2Real P := by
  let lam := bLambdaReal P
  let A := bAReal P
  let s : Real := (n : Real) - A
  let t : Real := lam * s
  let nu : Real := lam * (A + 1)
  have hlam : 0 < lam := bLambdaReal_pos P
  have hs : 0 < s := by simpa [s, A] using sub_pos.mpr hnA
  have ht : 0 < t := mul_pos hlam hs
  have hA : 0 < A := by simpa [A] using bAReal_pos P
  have hnu : 0 < nu := mul_pos hlam (by linarith)
  have hn1 : (n : Real) + 1 ≠ 0 := by positivity
  have hratio : s / ((n : Real) + 1) = t / (t + nu) := by
    have hdenEq : t + nu = lam * ((n : Real) + 1) := by
      dsimp [t, nu, s]
      ring
    rw [hdenEq]
    change s / ((n : Real) + 1) =
      (lam * s) / (lam * ((n : Real) + 1))
    rw [mul_div_mul_left s ((n : Real) + 1) hlam.ne']
  have hexpSplit :
      Real.exp (-lam * (n : Real)) =
        Real.exp (-lam * A) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t, s]
    ring
  have hcore := exp_mul_ratio_le_exp_neg_two_w ht hnu
  have hfirst :
      bKAt P n <= Real.exp (-lam * A - 2 * bWReal nu) := by
    rw [bKAt, x_pow_eq_exp_neg_lambda_mul]
    change (Real.exp (-lam * (n : Real)) * s) /
        ((n : Real) + 1) <= _
    rw [mul_div_assoc]
    rw [hexpSplit, hratio]
    rw [show Real.exp (-lam * A - 2 * bWReal nu) =
        Real.exp (-lam * A) * Real.exp (-2 * bWReal nu) by
          rw [← Real.exp_add]
          congr 1
          ring]
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hcore (Real.exp_pos (-lam * A)).le
  have hphi0 := bPhiReal_nonneg P
  have hphiA : bPhiReal P.e P.kappa <= lam * A := by
    simpa [lam, A] using phi_le_lambda_mul_A P
  have hphiNu : bPhiReal P.e P.kappa <= nu := by
    simpa [lam, A, nu] using phi_le_nu P
  have hw : bWReal (bPhiReal P.e P.kappa) <= bWReal nu :=
    bWReal_monotone hphi0 hphiNu
  calc
    bKAt P n <= Real.exp (-lam * A - 2 * bWReal nu) := hfirst
    _ <= Real.exp (-bPhiReal P.e P.kappa -
        2 * bWReal (bPhiReal P.e P.kappa)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = bK2Real P := by rfl

lemma bKAt_nonpos_of_n_le_A (P : AdmissibleParams) (n : Nat)
    (hnA : (n : Real) <= bAReal P) : bKAt P n <= 0 := by
  unfold bKAt
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos
      (pow_nonneg (div_nonneg P.alpha_nonneg P.p_pos.le) n)
      (sub_nonpos.mpr hnA)) (by positivity)

lemma bKAt_le_k2Real (P : AdmissibleParams) (n : Nat) :
    bKAt P n <= bK2Real P := by
  by_cases hnA : (n : Real) <= bAReal P
  · exact (bKAt_nonpos_of_n_le_A P n hnA).trans (Real.exp_pos _).le
  · exact bKAt_le_k2Real_of_A_lt_n P n (lt_of_not_ge hnA)

lemma bKAt_le_k1Real_of_endpoint_gate (P : AdmissibleParams) (n : Nat)
    (hn : 14 <= n)
    (hA14 : bAReal P < 14)
    (hgate : bAReal P + 1 <=
      15 * (14 - bAReal P) * bLambdaReal P) :
    bKAt P n <= bK1Real P := by
  let lam := bLambdaReal P
  let A := bAReal P
  let d : Real := 14 - A
  let r : Real := (n : Real) - 14
  have hlam : 0 < lam := bLambdaReal_pos P
  have hA : 0 < A := by simpa [A] using bAReal_pos P
  have hd : 0 < d := by simpa [d, A] using sub_pos.mpr hA14
  have hnR : (14 : Real) <= (n : Real) := by exact_mod_cast hn
  have hr : 0 <= r := by simpa [r] using sub_nonneg.mpr hnR
  have h15r : 0 < 15 + r := by linarith
  have hden : 0 < d * (15 + r) := mul_pos hd h15r
  have hgate' : A + 1 <= 15 * d * lam := by
    simpa [A, d, lam] using hgate
  have hz : r * (A + 1) / (d * (15 + r)) <= lam * r := by
    rw [div_le_iff₀ hden]
    calc
      r * (A + 1) <= r * (15 * d * lam) :=
        mul_le_mul_of_nonneg_left hgate' hr
      _ = (lam * r * d) * 15 := by ring
      _ <= (lam * r * d) * (15 + r) :=
        mul_le_mul_of_nonneg_left (by linarith) <|
          mul_nonneg (mul_nonneg hlam.le hr) hd.le
      _ = lam * r * (d * (15 + r)) := by ring
  have hQeq :
      15 * (d + r) / (d * (15 + r)) =
        1 + r * (A + 1) / (d * (15 + r)) := by
    rw [div_eq_iff hden.ne']
    field_simp [hden.ne']
    dsimp [d]
    ring
  have hQ : 15 * (d + r) / (d * (15 + r)) <= Real.exp (lam * r) := by
    rw [hQeq]
    simpa [add_comm] using
      (add_le_add_left hz 1).trans (Real.add_one_le_exp (lam * r))
  have hratio : (d + r) / (15 + r) <= Real.exp (lam * r) * d / 15 := by
    rw [div_le_div_iff₀ h15r (by norm_num : (0 : Real) < 15)]
    have hQ' := (div_le_iff₀ hden).mp hQ
    nlinarith
  have hsplitN : (n : Real) - A = d + r := by
    dsimp [d, r]
    ring
  have hsplitD : (n : Real) + 1 = 15 + r := by
    dsimp [r]
    ring
  have hexp : Real.exp (-lam * (n : Real)) * Real.exp (lam * r) =
      Real.exp (-lam * 14) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  rw [bKAt, x_pow_eq_exp_neg_lambda_mul]
  change (Real.exp (-lam * (n : Real)) * ((n : Real) - A)) /
      ((n : Real) + 1) <= bK1Real P
  rw [mul_div_assoc, hsplitN, hsplitD]
  calc
    Real.exp (-lam * (n : Real)) * ((d + r) / (15 + r)) <=
        Real.exp (-lam * (n : Real)) *
          (Real.exp (lam * r) * d / 15) :=
      mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
    _ = (Real.exp (-lam * (n : Real)) * Real.exp (lam * r)) * d / 15 := by
      ring
    _ = Real.exp (-lam * 14) * d / 15 := by rw [hexp]
    _ = bK1Real P := by
      unfold bK1Real
      rw [max_eq_right hd.le, x_pow_eq_exp_neg_lambda_mul]
      rfl

namespace BBoxContext

variable {P : AdmissibleParams} {box : RatBox} (H : BBoxContext P box)

include H

lemma endpoint_gate_real (hgate : bOnlyK14 box) :
    bAReal P < 14 ∧
      bAReal P + 1 <=
        15 * (14 - bAReal P) * bLambdaReal P := by
  have hAmax : bAReal P <= (bAMax box : Real) := H.A_bounds.2
  have hA14 : (bAMax box : Real) < 14 := by exact_mod_cast hgate.1
  have hlamMin : (0 : Real) < bLamMin box := by
    rw [bLamMin]
    push_cast
    linarith [H.xMax_lt_one]
  have hgateR : (bAMax box : Real) + 1 <=
      15 * (14 - (bAMax box : Real)) * (bLamMin box : Real) := by
    exact_mod_cast hgate.2
  have hA : bAReal P < 14 := hAmax.trans_lt hA14
  constructor
  · exact hA
  · calc
      bAReal P + 1 <= (bAMax box : Real) + 1 := by linarith
      _ <= 15 * (14 - (bAMax box : Real)) * (bLamMin box : Real) := hgateR
      _ <= 15 * (14 - bAReal P) * (bLamMin box : Real) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by norm_num)) hlamMin.le
      _ <= 15 * (14 - bAReal P) * bLambdaReal P := by
        exact mul_le_mul_of_nonneg_left H.lamMin_le_lambda
          (mul_nonneg (by norm_num) (sub_nonneg.mpr hA.le))

lemma bKAt_le_k1Real (hgate : bOnlyK14 box) (n : Nat) (hn : 14 <= n) :
    bKAt P n <= bK1Real P :=
  bKAt_le_k1Real_of_endpoint_gate P n hn
    (H.endpoint_gate_real hgate).1 (H.endpoint_gate_real hgate).2

lemma BEnvelopeSound.battle_for_n (S : BEnvelopeSound P box)
    (n : Nat) (hn : 14 <= n) :
    bKAt P n / P.x ^ 2 + bLambdaBar P <= bPiUnder P.e P.kappa := by
  cases S with
  | endpoint hgate hbattle =>
      exact (add_le_add
        (div_le_div_of_nonneg_right (H.bKAt_le_k1Real hgate n hn) (sq_nonneg P.x))
        (le_refl _)).trans hbattle
  | interior hgate hbattle =>
      have hk : bKAt P n <= max (bK1Real P) (bK2Real P) :=
        (bKAt_le_k2Real P n).trans (le_max_right _ _)
      exact (add_le_add
        (div_le_div_of_nonneg_right hk (sq_nonneg P.x))
        (le_refl _)).trans hbattle

end BBoxContext

theorem zoneB_certificate_battle (P : AdmissibleParams)
    (heLo : 1 / 60 <= P.e)
    (heHi : P.e <= 2033 / 10000)
    (hxi : 1 <= P.xi)
    (hfrontier : P.kappa <= kappaMax P.e)
    (n : Nat) (hn : 14 <= n) :
    bKAt P n / P.x ^ 2 + bLambdaBar P <= bPiUnder P.e P.kappa := by
  obtain ⟨box, H, S⟩ :=
    zoneB_certificate_envelope P heLo heHi hxi hfrontier
  exact BBoxContext.BEnvelopeSound.battle_for_n H S n hn

end OddCycleBound.RegionII.Certificate
