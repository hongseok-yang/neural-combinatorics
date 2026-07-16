import OddCycleBound.RegionII.Certificate.ZoneCBottomSound
import OddCycleBound.RegionII.Certificate.ZoneCChunked

/-!
# Tree-level soundness of the moderate Zone-C certificate

The executable tree covers a closed rational rectangle.  Regular and
bottom-out leaves were proved sound separately; this module supplies the
remaining geometric fact that a strictly skipped leaf cannot contain a point
in the closed `xi <= 1` and frontier-ceiling constraints.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

lemma kappa_le_kappaXi_of_xi_le_one (P : AdmissibleParams)
    (hxi : P.xi <= 1) :
    P.kappa <= P.e / (1 - P.e) ^ 2 := by
  rw [P.xi_chart] at hxi
  have hprod : (1 - P.e) ^ 2 * P.kappa <= P.e :=
    (div_le_one P.e_pos).mp hxi
  have hden : 0 < (1 - P.e) ^ 2 :=
    sq_pos_of_pos (by linarith [P.e_lt_third])
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hprod)

namespace CBoxContext

variable {P : AdmissibleParams} {box : RatBox}
  (H : CBoxContext P box)

include H

lemma kappa_le_cast_kappaXiQ_e2 (hxi : P.xi <= 1) :
    P.kappa <= (kappaXiQ box.e2 : Real) := by
  have he0 : 0 <= P.e := P.e_pos.le
  have heE := H.e_bounds.2
  have hmono := kappaXi_monotone he0 heE H.e2_lt_one
  have hpoint := kappa_le_kappaXi_of_xi_le_one P hxi
  have hcast : (kappaXiQ box.e2 : Real) =
      (box.e2 : Real) / (1 - (box.e2 : Real)) ^ 2 := by
    simp [kappaXiQ]
  rw [hcast]
  exact hpoint.trans hmono

lemma kappa_le_cast_kappaBarQ_e1
    (hfrontier : P.kappa <= kappaMax P.e) :
    P.kappa <= (kappaBarQ box.e1 : Real) := by
  have he1pos : (0 : Real) < box.e1 := by
    have hroot := (H.placed_rat).1
    have hrootR : (0 : Real) < (zoneCRoot.e1 : Real) := by
      norm_num [zoneCRoot]
    have hle : (zoneCRoot.e1 : Real) <= (box.e1 : Real) := by
      exact_mod_cast hroot
    exact hrootR.trans_le hle
  have he1e := H.e_bounds.1
  have hmax : P.kappa <=
      (1 - (box.e1 : Real)) / (1 + (box.e1 : Real)) := by
    have heP1 : P.e < 1 := P.e_lt_third.trans (by norm_num)
    have hmono := kappaMax_antitone he1pos.le he1e heP1
    exact hfrontier.trans (by simpa [kappaMax] using hmono)
  have hq : P.kappa <=
      (1 - 3 * (box.e1 : Real)) / (6 * (box.e1 : Real)) := by
    have hmono := kappaQ_antitone he1pos he1e
    exact P.kappa_lt_q.le.trans (by simpa [kappaQ] using hmono)
  rcases le_total ((1 - box.e1) / (1 + box.e1))
      ((1 - 3 * box.e1) / (6 * box.e1)) with hleft | hright
  · rw [kappaBarQ, min_eq_left hleft]
    simpa using hmax
  · rw [kappaBarQ, min_eq_right hright]
    simpa using hq

lemma not_cSkip
    (hxi : P.xi <= 1) (hfrontier : P.kappa <= kappaMax P.e)
    (hskip : box.k1 > min (kappaXiQ box.e2) (kappaBarQ box.e1)) : False := by
  have hxiEnd := H.kappa_le_cast_kappaXiQ_e2 hxi
  have hbarEnd := H.kappa_le_cast_kappaBarQ_e1 hfrontier
  have hthreshold :
      P.kappa <= (min (kappaXiQ box.e2) (kappaBarQ box.e1) : Real) := by
    exact le_min hxiEnd hbarEnd
  have hskipR :
      (min (kappaXiQ box.e2) (kappaBarQ box.e1) : Real) <
        (box.k1 : Real) := by
    exact_mod_cast hskip
  linarith [H.k_bounds.1]

end CBoxContext

theorem zoneC_certificate_sound_interior (P : AdmissibleParams)
    (heLo : (1 / 60 : Real) <= P.e)
    (heHi : P.e <= (1 / 3 - 1 / 1000 : Real))
    (hxi : P.xi <= 1)
    (hfrontier : P.kappa <= kappaMax P.e) :
    P.R <= P.C * psi P.xi P.rho := by
  have hroot : zoneCRoot.Contains P.e P.kappa := by
    have hk0 : (0 : Real) <= P.kappa := P.kappa_pos.le
    have hk1 : P.kappa <= 1 := by
      have hmax := P.kappa_le_max
      have hmaxOne : kappaMax P.e <= 1 := by
        unfold kappaMax
        have hden : 0 < 1 + P.e := by linarith [P.e_pos]
        apply (div_le_one hden).2
        linarith [P.e_pos]
      exact hmax.trans hmaxOne
    simpa [zoneCRoot, RatBox.Contains] using
      And.intro heLo (And.intro heHi (And.intro hk0 hk1))
  apply BoxTree.validC_covers
      (tree := zoneCChunkedTree) (root := zoneCRoot)
      (e := P.e) (k := P.kappa)
      (Q := P.R <= P.C * psi P.xi P.rho) ?_ zoneC_chunkedTree_valid hroot
  intro box token haccept hpoint
  simp only [leafAcceptedC, Bool.and_eq_true] at haccept
  let H : CBoxContext P box :=
    { point := hpoint
      placed := haccept.1 }
  cases token with
  | cSkip =>
      have hskip : box.k1 >
          min (kappaXiQ box.e2) (kappaBarQ box.e1) :=
        of_decide_eq_true haccept.2
      exact False.elim (H.not_cSkip hxi hfrontier hskip)
  | cVerified m =>
      exact checkCRegular_sound H m haccept.2 hxi
  | cBottom =>
      exact checkCBottom_sound H haccept.2 hxi
  | splitE => simp at haccept
  | splitK => simp at haccept
  | bSkipZoneC => simp at haccept
  | bSkipOutside => simp at haccept
  | bVerified => simp at haccept

end OddCycleBound.RegionII.Certificate
