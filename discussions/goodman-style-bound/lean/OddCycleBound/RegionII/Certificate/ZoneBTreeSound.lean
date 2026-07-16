import OddCycleBound.RegionII.Certificate.ZoneBAnalyticBox

/-!
# Tree-level Zone-B envelope certificate

The two skip tokens are strictly separated one-sided domain tests.  They are
impossible for a point in the closed `xi >= 1` and frontier-ceiling domain. Every
remaining leaf supplies the real envelope inequality proved in
`ZoneBAnalyticBox`.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

lemma kappaXi_le_of_one_le_xi (P : AdmissibleParams) (hxi : 1 <= P.xi) :
    P.e / (1 - P.e) ^ 2 <= P.kappa := by
  rw [P.xi_chart] at hxi
  have hprod : P.e <= (1 - P.e) ^ 2 * P.kappa :=
    (one_le_div P.e_pos).mp hxi
  have hden : 0 < (1 - P.e) ^ 2 :=
    sq_pos_of_pos (by linarith [P.e_lt_third])
  exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hprod)

namespace BBoxContext

variable {P : AdmissibleParams} {box : RatBox} (H : BBoxContext P box)

include H

lemma not_skip_zoneC (hxi : 1 <= P.xi)
    (hskip : box.k2 < kappaXiQ box.e1) : False := by
  have hcurve := kappaXi_le_of_one_le_xi P hxi
  have hmono := kappaXi_monotone H.e1_pos.le H.e_bounds.1
    (P.e_lt_third.trans (by norm_num))
  have hcast : (kappaXiQ box.e1 : Real) =
      (box.e1 : Real) / (1 - (box.e1 : Real)) ^ 2 := by
    simp [kappaXiQ]
  have hskipR : (box.k2 : Real) < (kappaXiQ box.e1 : Real) := by
    exact_mod_cast hskip
  rw [hcast] at hskipR
  linarith [H.k_bounds.2]

lemma kappa_lt_cast_kappaBarQ_e1
    (hfrontier : P.kappa <= kappaMax P.e) :
    P.kappa <= (kappaBarQ box.e1 : Real) := by
  have he1e := H.e_bounds.1
  have hmax : P.kappa <=
      (1 - (box.e1 : Real)) / (1 + (box.e1 : Real)) := by
    have heP1 : P.e < 1 := P.e_lt_third.trans (by norm_num)
    have hmono := kappaMax_antitone H.e1_pos.le he1e heP1
    exact hfrontier.trans (by simpa [kappaMax] using hmono)
  have hq : P.kappa <=
      (1 - 3 * (box.e1 : Real)) / (6 * (box.e1 : Real)) := by
    have hmono := kappaQ_antitone H.e1_pos he1e
    exact P.kappa_lt_q.le.trans (by simpa [kappaQ] using hmono)
  rcases le_total ((1 - box.e1) / (1 + box.e1))
      ((1 - 3 * box.e1) / (6 * box.e1)) with hleft | hright
  · rw [kappaBarQ, min_eq_left hleft]
    simpa using hmax
  · rw [kappaBarQ, min_eq_right hright]
    simpa using hq

lemma not_skip_outside (hfrontier : P.kappa <= kappaMax P.e)
    (hskip : box.k1 > kappaBarQ box.e1) : False := by
  have hbar := H.kappa_lt_cast_kappaBarQ_e1 hfrontier
  have hskipR : (kappaBarQ box.e1 : Real) < (box.k1 : Real) := by
    exact_mod_cast hskip
  linarith [H.k_bounds.1]

end BBoxContext

theorem zoneB_certificate_envelope (P : AdmissibleParams)
    (heLo : (1 / 60 : Real) <= P.e)
    (heHi : P.e <= (2033 / 10000 : Real))
    (hxi : 1 <= P.xi)
    (hfrontier : P.kappa <= kappaMax P.e) :
    ∃ box, ∃ H : BBoxContext P box, BBoxContext.BEnvelopeSound P box := by
  have hkCurve := kappaXi_le_of_one_le_xi P hxi
  have hkRoot : (zoneBRoot.k1 : Real) <= P.kappa := by
    have hmono := kappaXi_monotone (by norm_num : (0 : Real) <= 1 / 60)
      heLo (P.e_lt_third.trans (by norm_num))
    have : (zoneBRoot.k1 : Real) =
        (1 / 60 : Real) / (1 - (1 / 60 : Real)) ^ 2 := by
      norm_num [zoneBRoot, kappaXiQ]
    rw [this]
    exact hmono.trans hkCurve
  have hkOne : P.kappa <= 1 := by
    have hmax := P.kappa_le_max
    have hmaxOne : kappaMax P.e <= 1 := by
      unfold kappaMax
      have hden : 0 < 1 + P.e := by linarith [P.e_pos]
      exact (div_le_one hden).2 (by linarith [P.e_pos])
    exact hmax.trans hmaxOne
  have hroot : zoneBRoot.Contains P.e P.kappa := by
    simpa [zoneBRoot, RatBox.Contains] using
      And.intro heLo (And.intro heHi (And.intro hkRoot hkOne))
  apply BoxTree.validB_covers
      (tree := zoneBBoxTree) (root := zoneBRoot)
      (e := P.e) (k := P.kappa)
      (Q := ∃ box, ∃ H : BBoxContext P box, BBoxContext.BEnvelopeSound P box)
      ?_ zoneB_boxTree_valid.2 hroot
  intro box token haccept hpoint
  simp only [leafAcceptedB, Bool.and_eq_true] at haccept
  let H : BBoxContext P box :=
    { point := hpoint
      placed := haccept.1 }
  cases token with
  | bSkipZoneC =>
      have hskip : box.k2 < kappaXiQ box.e1 :=
        of_decide_eq_true haccept.2
      exact False.elim (H.not_skip_zoneC hxi hskip)
  | bSkipOutside =>
      have hskip : box.k1 > kappaBarQ box.e1 :=
        of_decide_eq_true haccept.2
      exact False.elim (H.not_skip_outside hfrontier hskip)
  | bVerified =>
      have E := checkBVerified_evidence haccept.2
      exact ⟨box, H, H.verified_envelope_sound E⟩
  | splitE => simp at haccept
  | splitK => simp at haccept
  | cSkip => simp at haccept
  | cVerified m => simp at haccept
  | cBottom => simp at haccept

end OddCycleBound.RegionII.Certificate
