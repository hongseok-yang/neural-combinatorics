import OddCycleBound.RegionII.Certificate.Coverage
import OddCycleBound.RegionII.Scalar.Payments

/-!
# Monotone interval bounds in chart coordinates

These lemmas form the reusable real-analysis layer underneath both finite
certificate soundness proofs.  They justify the endpoint substitutions made
by the executable rational checkers.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

def chartXR (e k : Real) : Real :=
  (1 - e) / (1 + e + 2 * k * e)

lemma cast_chartXQ (e k : ℚ) :
    (chartXQ e k : Real) = chartXR e k := by
  unfold chartXQ chartXR
  push_cast
  rfl

lemma chartXR_den_pos {e k : Real}
    (he : 0 <= e) (hk : 0 <= k) :
    0 < 1 + e + 2 * k * e := by
  nlinarith [mul_nonneg hk he]

lemma chartXR_antitone_k {e k1 k2 : Real}
    (he0 : 0 <= e) (he1 : e < 1) (hk0 : 0 <= k1) (hk : k1 <= k2) :
    chartXR e k2 <= chartXR e k1 := by
  have hk20 : 0 <= k2 := hk0.trans hk
  have hd1 := chartXR_den_pos he0 hk0
  have hd2 := chartXR_den_pos he0 hk20
  unfold chartXR
  rw [div_le_div_iff₀ hd2 hd1]
  have hn : 0 <= 1 - e := by linarith
  have hden :
      1 + e + 2 * k1 * e <= 1 + e + 2 * k2 * e := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) he0]
  exact mul_le_mul_of_nonneg_left hden hn

lemma chartXR_antitone_e {e1 e2 k : Real}
    (he0 : 0 <= e1) (he : e1 <= e2) (he2 : e2 < 1) (hk : 0 <= k) :
    chartXR e2 k <= chartXR e1 k := by
  have he20 : 0 <= e2 := he0.trans he
  have hd1 := chartXR_den_pos he0 hk
  have hd2 := chartXR_den_pos he20 hk
  unfold chartXR
  rw [div_le_div_iff₀ hd2 hd1]
  have hprod : 0 <= (e2 - e1) * (1 + k) :=
    mul_nonneg (sub_nonneg.mpr he) (by linarith)
  nlinarith

lemma chartXR_antitone {e1 e2 k1 k2 : Real}
    (he0 : 0 <= e1) (he : e1 <= e2) (he2 : e2 < 1)
    (hk0 : 0 <= k1) (hk : k1 <= k2) :
    chartXR e2 k2 <= chartXR e1 k1 := by
  exact (chartXR_antitone_k (e := e2) (k1 := k1) (k2 := k2)
    (he0.trans he) he2 hk0 hk).trans
      (chartXR_antitone_e (e1 := e1) (e2 := e2) (k := k1)
        he0 he he2 hk0)

lemma kappaXi_monotone {e E : Real}
    (he0 : 0 <= e) (heE : e <= E) (hE1 : E < 1) :
    e / (1 - e) ^ 2 <= E / (1 - E) ^ 2 := by
  have he1 : e < 1 := heE.trans_lt hE1
  have hd1 : 0 < (1 - e) ^ 2 := sq_pos_of_pos (by linarith)
  have hd2 : 0 < (1 - E) ^ 2 := sq_pos_of_pos (by linarith)
  rw [div_le_div_iff₀ hd1 hd2]
  have hfactor : 0 <= (E - e) * (1 - e * E) := by
    apply mul_nonneg (sub_nonneg.mpr heE)
    have hprod : e * E < 1 := by
      nlinarith [mul_nonneg he0 (he0.trans heE)]
    linarith
  nlinarith

lemma kappaMax_antitone {e E : Real}
    (he0 : 0 <= e) (heE : e <= E) (_hE1 : E < 1) :
    Scalar.kappaMax E <= Scalar.kappaMax e := by
  have hd1 : 0 < 1 + E := by linarith
  have hd2 : 0 < 1 + e := by linarith
  unfold Scalar.kappaMax
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith

lemma kappaQ_antitone {e E : Real}
    (he : 0 < e) (heE : e <= E) :
    Scalar.kappaQ E <= Scalar.kappaQ e := by
  have hE : 0 < E := he.trans_le heE
  have hd1 : 0 < 6 * E := by positivity
  have hd2 : 0 < 6 * e := by positivity
  unfold Scalar.kappaQ
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith

end OddCycleBound.RegionII.Certificate

namespace OddCycleBound.RegionII.Scalar.AdmissibleParams

variable (P : AdmissibleParams)

lemma x_eq_chartXR :
    P.x = Certificate.chartXR P.e P.kappa := by
  have hpChart :
      chartAlpha P.e + (1 + P.kappa) * P.e ≠ 0 := by
    change chartP P.e P.kappa ≠ 0
    rw [← P.p_eq_chart]
    exact P.p_pos.ne'
  have hrel :
      1 + P.e + 2 * P.kappa * P.e =
        2 * (chartAlpha P.e + (1 + P.kappa) * P.e) := by
    unfold chartAlpha
    ring
  rw [show P.x = P.alpha / P.p by rfl, P.alpha_eq_chart, P.p_eq_chart]
  unfold chartP Certificate.chartXR
  rw [hrel]
  unfold chartAlpha
  field_simp [hpChart]

end OddCycleBound.RegionII.Scalar.AdmissibleParams
