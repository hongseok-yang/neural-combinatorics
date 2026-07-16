import OddCycleBound.RegionII.Certificate.ZoneCPaymentBox

/-!
# Soundness of the moderate Zone-C battle

The executable loop works with outward-rounded powers.  This file first
connects its rational battle expression to the exact three-geometric defect,
then proves the recursive loop sound.
-/

noncomputable section

namespace OddCycleBound.RegionII.Certificate

open OddCycleBound.RegionII.Scalar

def cBattleHeadR (b : CBoxData) (n : Nat) : Real :=
  (1 / (b.aLo : Real)) * (b.xUp : Real) ^ n +
    ((b.l2Up : Real) / (b.aLo : Real)) * (b.yUp : Real) ^ n

def cBattleExprR (b : CBoxData) (n : Nat) : Real :=
  cBattleHeadR b n -
    ((b.pLo : Real) * (b.qLo : Real) / (b.aUp : Real) ^ 3) *
      (b.sLo : Real) ^ n

structure CBattleStateBounds (b : CBoxData) (m : Nat)
    (xp yp sp : ℚ) : Prop where
  xp_nonneg : 0 <= xp
  yp_nonneg : 0 <= yp
  sp_nonneg : 0 <= sp
  xpow_le : b.xUp ^ (m - 2) <= xp
  ypow_le : b.yUp ^ (m - 2) <= yp
  spow_ge : sp <= b.sLo ^ (m - 2)

namespace CBattleStateBounds

variable {b : CBoxData} {m : Nat} {xp yp sp : ℚ}

lemma step (H : CBattleStateBounds b m xp yp sp)
    (hm : 2 <= m)
    (hx : 0 <= b.xUp) (hy : 0 <= b.yUp) (hs : 0 <= b.sLo) :
    CBattleStateBounds b (m + 1)
      (roundUp (xp * roundUp b.xUp (10 ^ 12)) (10 ^ 12))
      (roundUp (yp * roundUp b.yUp (10 ^ 12)) (10 ^ 12))
      (roundDown (sp * roundDown b.sLo (10 ^ 12)) (10 ^ 12)) := by
  have hden : 0 < (10 ^ 12 : Nat) := by norm_num
  have hxr0 := roundUp_nonneg hx hden
  have hyr0 := roundUp_nonneg hy hden
  have hsr0 := roundDown_nonneg hs hden
  have hxpNext0 := roundUp_nonneg (mul_nonneg H.xp_nonneg hxr0) hden
  have hypNext0 := roundUp_nonneg (mul_nonneg H.yp_nonneg hyr0) hden
  have hspNext0 := roundDown_nonneg (mul_nonneg H.sp_nonneg hsr0) hden
  have hexp : m + 1 - 2 = (m - 2) + 1 := by omega
  refine ⟨hxpNext0, hypNext0, hspNext0, ?_, ?_, ?_⟩
  · rw [hexp, pow_succ]
    exact (mul_le_mul H.xpow_le (le_roundUp b.xUp hden)
      hx H.xp_nonneg).trans (le_roundUp _ hden)
  · rw [hexp, pow_succ]
    exact (mul_le_mul H.ypow_le (le_roundUp b.yUp hden)
      hy H.yp_nonneg).trans (le_roundUp _ hden)
  · rw [hexp, pow_succ]
    calc
      roundDown (sp * roundDown b.sLo (10 ^ 12)) (10 ^ 12) <=
          sp * roundDown b.sLo (10 ^ 12) := roundDown_le _ hden
      _ <= b.sLo ^ (m - 2) * b.sLo :=
        mul_le_mul H.spow_ge (roundDown_le b.sLo hden) hsr0
          (pow_nonneg hs _)
      _ = b.sLo ^ (m - 2 + 1) := (pow_succ _ _).symm

lemma battleExpr_le_state
    (H : CBattleStateBounds b m xp yp sp)
    (ha : 0 < (b.aLo : Real))
    (hl2 : 0 <= (b.l2Up : Real))
    (hcoeff : 0 <=
      (b.pLo : Real) * (b.qLo : Real) / (b.aUp : Real) ^ 3) :
    cBattleExprR b (m - 2) <= (cBattleExprQ b xp yp sp : Real) := by
  have hxp : (b.xUp : Real) ^ (m - 2) <= (xp : Real) := by
    exact_mod_cast H.xpow_le
  have hyp : (b.yUp : Real) ^ (m - 2) <= (yp : Real) := by
    exact_mod_cast H.ypow_le
  have hsp : (sp : Real) <= (b.sLo : Real) ^ (m - 2) := by
    exact_mod_cast H.spow_ge
  have hxterm :
      (1 / (b.aLo : Real)) * (b.xUp : Real) ^ (m - 2) <=
        (1 / (b.aLo : Real)) * (xp : Real) :=
    mul_le_mul_of_nonneg_left hxp (one_div_nonneg.mpr ha.le)
  have hyterm :
      ((b.l2Up : Real) / (b.aLo : Real)) *
          (b.yUp : Real) ^ (m - 2) <=
        ((b.l2Up : Real) / (b.aLo : Real)) * (yp : Real) :=
    mul_le_mul_of_nonneg_left hyp (div_nonneg hl2 ha.le)
  have hsterm :
      - ((b.pLo : Real) * (b.qLo : Real) / (b.aUp : Real) ^ 3) *
          (b.sLo : Real) ^ (m - 2) <=
        - ((b.pLo : Real) * (b.qLo : Real) / (b.aUp : Real) ^ 3) *
          (sp : Real) := by
    nlinarith
  unfold cBattleExprR cBattleHeadR cBattleExprQ cBattleHeadQ
  push_cast
  linarith

lemma battleHead_le_state
    (H : CBattleStateBounds b m xp yp sp)
    (ha : 0 < (b.aLo : Real))
    (hl2 : 0 <= (b.l2Up : Real)) :
    cBattleHeadR b (m - 2) <= (cBattleHeadQ b xp yp : Real) := by
  have hxp : (b.xUp : Real) ^ (m - 2) <= (xp : Real) := by
    exact_mod_cast H.xpow_le
  have hyp : (b.yUp : Real) ^ (m - 2) <= (yp : Real) := by
    exact_mod_cast H.ypow_le
  unfold cBattleHeadR cBattleHeadQ
  push_cast
  exact add_le_add
    (mul_le_mul_of_nonneg_left hxp (one_div_nonneg.mpr ha.le))
    (mul_le_mul_of_nonneg_left hyp (div_nonneg hl2 ha.le))

end CBattleStateBounds

lemma initialCBattleStateBounds (b : CBoxData) (m : Nat)
    (hx : 0 <= b.xUp) (hy : 0 <= b.yUp) (hs : 0 <= b.sLo) :
    CBattleStateBounds b m
      (directedPowUp b.xUp (m - 2))
      (directedPowUp b.yUp (m - 2))
      (directedPowDown b.sLo (m - 2)) := by
  refine ⟨?_, ?_, directedPowDown_nonneg hs _,
    directedPowUp_sound hx _, directedPowUp_sound hy _,
    directedPowDown_sound hs _⟩
  · exact (pow_nonneg hx _).trans (directedPowUp_sound hx _)
  · exact (pow_nonneg hy _).trans (directedPowUp_sound hy _)

theorem checkCBattleAux_sound_between
    (b : CBoxData) (c : ℚ) (target fuel m M : Nat) (xp yp sp : ℚ)
    (hcheck : checkCBattleAux b c target fuel m xp yp sp = true)
    (hstate : CBattleStateBounds b m xp yp sp)
    (hm2 : 2 <= m) (hmM : m <= M) (hMt : M <= target)
    (hx : 0 <= b.xUp) (hy : 0 <= b.yUp) (hs : 0 <= b.sLo)
    (ha : 0 < (b.aLo : Real)) (hl2 : 0 <= (b.l2Up : Real))
    (hcoeff : 0 <=
      (b.pLo : Real) * (b.qLo : Real) / (b.aUp : Real) ^ 3) :
    cBattleExprR b (M - 2) <= (c : Real) * (M : Real) := by
  induction fuel generalizing m xp yp sp with
  | zero =>
      simp [checkCBattleAux] at hcheck
  | succ fuel ih =>
      rw [checkCBattleAux] at hcheck
      split at hcheck
      next htarget =>
        subst m
        have hM : M = target := Nat.le_antisymm hMt hmM
        subst M
        have hq : cBattleHeadQ b xp yp <= c * target := by
          simpa only [decide_eq_true_eq] using hcheck
        have hqR :
            (cBattleHeadQ b xp yp : Real) <= (c : Real) * (target : Real) := by
          exact_mod_cast hq
        have hdrop :
            cBattleExprR b (target - 2) <= cBattleHeadR b (target - 2) := by
          unfold cBattleExprR
          have hpow : 0 <= (b.sLo : Real) ^ (target - 2) :=
            pow_nonneg (by exact_mod_cast hs) _
          nlinarith
        exact hdrop.trans ((hstate.battleHead_le_state ha hl2).trans hqR)
      next htarget =>
        split at hcheck
        next hgood =>
          rcases hgood with ⟨hmt, hq⟩
          by_cases hMm : M = m
          · subst M
            have hqR :
                (cBattleExprQ b xp yp sp : Real) <=
                  (c : Real) * (m : Real) := by
              exact_mod_cast hq
            exact (hstate.battleExpr_le_state ha hl2 hcoeff).trans hqR
          · have hmLtM : m < M := lt_of_le_of_ne hmM (Ne.symm hMm)
            have hnext := hstate.step hm2 hx hy hs
            exact ih (m + 1)
              (roundUp (xp * roundUp b.xUp (10 ^ 12)) (10 ^ 12))
              (roundUp (yp * roundUp b.yUp (10 ^ 12)) (10 ^ 12))
              (roundDown (sp * roundDown b.sLo (10 ^ 12)) (10 ^ 12))
              hcheck hnext (by omega) (by omega)
        next hgood =>
          simp at hcheck

theorem checkCBattleAux_sound_tail
    (b : CBoxData) (c : ℚ) (target fuel m : Nat) (xp yp sp : ℚ)
    (hcheck : checkCBattleAux b c target fuel m xp yp sp = true)
    (hstate : CBattleStateBounds b m xp yp sp)
    (hm2 : 2 <= m) (hmt : m <= target)
    (hx : 0 <= b.xUp) (hy : 0 <= b.yUp) (hs : 0 <= b.sLo)
    (ha : 0 < (b.aLo : Real)) (hl2 : 0 <= (b.l2Up : Real)) :
    cBattleHeadR b (target - 2) <= (c : Real) * (target : Real) := by
  induction fuel generalizing m xp yp sp with
  | zero =>
      simp [checkCBattleAux] at hcheck
  | succ fuel ih =>
      rw [checkCBattleAux] at hcheck
      split at hcheck
      next htarget =>
        subst m
        have hq : cBattleHeadQ b xp yp <= c * target := by
          simpa only [decide_eq_true_eq] using hcheck
        have hqR :
            (cBattleHeadQ b xp yp : Real) <= (c : Real) * (target : Real) := by
          exact_mod_cast hq
        exact (hstate.battleHead_le_state ha hl2).trans hqR
      next htarget =>
        split at hcheck
        next hgood =>
          have hnext := hstate.step hm2 hx hy hs
          exact ih (m + 1)
            (roundUp (xp * roundUp b.xUp (10 ^ 12)) (10 ^ 12))
            (roundUp (yp * roundUp b.yUp (10 ^ 12)) (10 ^ 12))
            (roundDown (sp * roundDown b.sLo (10 ^ 12)) (10 ^ 12))
            hcheck hnext (by omega) (by omega)
        next hgood =>
          simp at hcheck

lemma checkCBattle_evidence {b : CBoxData} {target : Nat}
    (hcheck : checkCBattle b target = true) :
    b.mPlus <= target ∧ target <= 500001 ∧
      checkCBattleAux b b.cLo target (target - b.mPlus + 1) b.mPlus
        (directedPowUp b.xUp (b.mPlus - 2))
        (directedPowUp b.yUp (b.mPlus - 2))
        (directedPowDown b.sLo (b.mPlus - 2)) = true := by
  rw [checkCBattle] at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i hbounds
    push_neg at hbounds
    exact ⟨hbounds.1, hbounds.2, hcheck⟩

lemma CBoxData.fifteen_le_mPlus (b : CBoxData) : 15 <= b.mPlus := by
  unfold CBoxData.mPlus
  dsimp only
  split
  · exact le_min (le_max_left _ _) (by norm_num)
  · norm_num

lemma CBoxData.mPlus_le_cap (b : CBoxData) : b.mPlus <= 500000 := by
  unfold CBoxData.mPlus
  exact min_le_right _ _

lemma checkCRegular_evidence {box : RatBox} {target : Nat}
    (hcheck : checkCRegular box target = true) :
    (makeCBox box).sqrtOK = true ∧
      0 < (makeCBox box).fLo ∧
      0 < (makeCBox box).sLo ∧
      (makeCBox box).sLo < (makeCBox box).xUp ∧
      box.k1 ≠ 0 ∧
      0 < (makeCBox box).cLo ∧
      checkCBattle (makeCBox box) target = true := by
  rw [checkCRegular] at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i hshape
    split at hcheck
    · simp at hcheck
    · rename_i hc
      have hshape' := hshape
      simp at hshape'
      have hc' : 0 < (makeCBox box).cLo := lt_of_not_ge hc
      exact ⟨hshape'.1.1.1.1, hshape'.1.1.1.2, hshape'.1.1.2,
        hshape'.1.2, hshape'.2, hc', hcheck⟩

lemma cBattleHeadR_antitone {b : CBoxData} {n₁ n₂ : Nat}
    (hx0 : 0 <= (b.xUp : Real)) (hx1 : (b.xUp : Real) <= 1)
    (hy0 : 0 <= (b.yUp : Real)) (hy1 : (b.yUp : Real) <= 1)
    (ha : 0 < (b.aLo : Real)) (hl2 : 0 <= (b.l2Up : Real))
    (hn : n₁ <= n₂) :
    cBattleHeadR b n₂ <= cBattleHeadR b n₁ := by
  unfold cBattleHeadR
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hx0 hx1 hn) (one_div_nonneg.mpr ha.le))
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hy0 hy1 hn) (div_nonneg hl2 ha.le))

namespace CAnalyticBoxContext

variable {P : AdmissibleParams} {box : RatBox}
  (H : CAnalyticBoxContext P box)

include H

lemma xUp_le_one :
    ((makeCBox box).xUp : Real) <= 1 := by
  simp only [makeCBox, cast_chartXQ]
  unfold chartXR
  have he1 : (0 : Real) <= box.e1 := H.base.e1_nonneg
  have hk1 : (0 : Real) <= box.k1 := H.base.k1_nonneg
  have hden := chartXR_den_pos he1 hk1
  rw [div_le_one hden]
  nlinarith [mul_nonneg hk1 he1]

lemma yUp_nonneg :
    (0 : Real) <= ((makeCBox box).yUp : Real) :=
  P.y_nonneg.trans H.y_le_yUp

lemma yUp_le_one :
    ((makeCBox box).yUp : Real) <= 1 := by
  have hq : (makeCBox box).yUp <= (1 / 2 : ℚ) := by
    rw [show (makeCBox box).yUp =
      min (min (cLUp box / (makeCBox box).pLo) (1 / 2))
        (makeCBox box).sUp by rfl]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hR : ((makeCBox box).yUp : Real) <= (1 / 2 : Real) := by
    have hcast :
        ((makeCBox box).yUp : Real) <= (((1 / 2 : ℚ)) : Real) := by
      exact_mod_cast hq
    norm_num at hcast ⊢
    exact hcast
  linarith

lemma boxCoeff_le :
    ((makeCBox box).pLo : Real) * ((makeCBox box).qLo : Real) /
        ((makeCBox box).aUp : Real) ^ 3 <=
      P.p * P.q / P.alpha ^ 3 := by
  have hp := H.base.makeCBox_p.1
  have hq := H.base.makeCBox_q.1
  have ha := H.base.makeCBox_alpha.2
  have hnum :
      ((makeCBox box).pLo : Real) * ((makeCBox box).qLo : Real) <=
        P.p * P.q :=
    mul_le_mul hp hq H.qLo_pos.le P.p_pos.le
  have hden :
      P.alpha ^ 3 <= ((makeCBox box).aUp : Real) ^ 3 :=
    pow_le_pow_left₀ P.alpha_nonneg ha 3
  rw [div_le_div_iff₀ (pow_pos H.aUp_pos 3) (pow_pos P.alpha_pos 3)]
  exact mul_le_mul hnum hden (pow_pos P.alpha_pos 3).le
    (mul_nonneg P.p_pos.le P.q_nonneg)

lemma normalized_R_le_boxBattle :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      cBattleExprR (makeCBox box) (P.m - 2) := by
  let n := P.m - 2
  have hxPow :
      P.x ^ n <= ((makeCBox box).xUp : Real) ^ n :=
    pow_le_pow_left₀
      (div_nonneg P.alpha_nonneg P.p_pos.le)
      H.base.makeCBox_x.2 n
  have hyPow :
      P.y ^ n <= ((makeCBox box).yUp : Real) ^ n :=
    pow_le_pow_left₀ P.y_nonneg H.y_le_yUp n
  have hsPow :
      ((makeCBox box).sLo : Real) ^ n <= P.s ^ n :=
    pow_le_pow_left₀ H.sLo_pos.le H.sLo_le_s n
  have hfirst :
      P.x ^ n / P.alpha <=
        (1 / ((makeCBox box).aLo : Real)) *
          ((makeCBox box).xUp : Real) ^ n := by
    have ha := H.base.makeCBox_alpha.1
    have hp :
        P.x ^ n * ((makeCBox box).aLo : Real) <=
          ((makeCBox box).xUp : Real) ^ n * P.alpha :=
      mul_le_mul hxPow ha H.aLo_pos.le (pow_nonneg H.xUp_nonneg n)
    calc
      P.x ^ n / P.alpha <=
          ((makeCBox box).xUp : Real) ^ n /
            ((makeCBox box).aLo : Real) := by
        rw [div_le_div_iff₀ P.alpha_pos H.aLo_pos]
        simpa [mul_comm] using hp
      _ = (1 / ((makeCBox box).aLo : Real)) *
          ((makeCBox box).xUp : Real) ^ n := by ring
  have hsecond :
      P.ell ^ 2 * P.y ^ n / P.alpha <=
        (((makeCBox box).l2Up : Real) / ((makeCBox box).aLo : Real)) *
          ((makeCBox box).yUp : Real) ^ n := by
    have hell := H.makeCBox_ell_sq.2
    have hprod :
        P.ell ^ 2 * P.y ^ n <=
          ((makeCBox box).l2Up : Real) *
            ((makeCBox box).yUp : Real) ^ n :=
      mul_le_mul hell hyPow (pow_nonneg P.y_nonneg n)
        (by
          exact (sq_nonneg P.ell).trans hell)
    have ha := H.base.makeCBox_alpha.1
    have hcross :
        (P.ell ^ 2 * P.y ^ n) * ((makeCBox box).aLo : Real) <=
          (((makeCBox box).l2Up : Real) *
            ((makeCBox box).yUp : Real) ^ n) * P.alpha :=
      mul_le_mul hprod ha H.aLo_pos.le
        (mul_nonneg
          ((sq_nonneg P.ell).trans hell)
          (pow_nonneg H.yUp_nonneg n))
    calc
      P.ell ^ 2 * P.y ^ n / P.alpha <=
          (((makeCBox box).l2Up : Real) *
            ((makeCBox box).yUp : Real) ^ n) /
              ((makeCBox box).aLo : Real) := by
        rw [div_le_div_iff₀ P.alpha_pos H.aLo_pos]
        exact hcross
      _ = (((makeCBox box).l2Up : Real) /
          ((makeCBox box).aLo : Real)) *
            ((makeCBox box).yUp : Real) ^ n := by ring
  have hnegative :
      - (P.p * P.q / P.alpha ^ 3) * P.s ^ n <=
        - (((makeCBox box).pLo : Real) *
            ((makeCBox box).qLo : Real) /
            ((makeCBox box).aUp : Real) ^ 3) *
          ((makeCBox box).sLo : Real) ^ n := by
    have hprod :
        (((makeCBox box).pLo : Real) *
            ((makeCBox box).qLo : Real) /
            ((makeCBox box).aUp : Real) ^ 3) *
            ((makeCBox box).sLo : Real) ^ n <=
          (P.p * P.q / P.alpha ^ 3) * P.s ^ n :=
      mul_le_mul H.boxCoeff_le hsPow (pow_nonneg H.sLo_pos.le n)
        (div_nonneg (mul_nonneg P.p_pos.le P.q_nonneg)
          (pow_pos P.alpha_pos 3).le)
    linarith
  rw [P.R_three_geometric]
  unfold cBattleExprR cBattleHeadR
  dsimp [n] at hfirst hsecond hnegative ⊢
  linarith

lemma g2Prime_le_log_one_add_G2 :
    ((makeCBox box).g2Lo : Real) -
        ((makeCBox box).g2Lo : Real) ^ 2 / 2 <=
      Real.log (1 + P.G2) := by
  let t : Real := ((makeCBox box).g2Lo : Real)
  have ht : 0 <= t := H.g2Lo_nonneg
  have hden : 0 < t + 2 := by linarith
  have hcubic : 0 <= t ^ 3 := pow_nonneg ht 3
  have hsecant : t - t ^ 2 / 2 <= 2 * t / (t + 2) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hlogt : 2 * t / (t + 2) <= Real.log (1 + t) :=
    Real.le_log_one_add_of_nonneg ht
  have hone : 0 < 1 + t := by linarith
  have hmono : Real.log (1 + t) <= Real.log (1 + P.G2) := by
    apply Real.log_le_log hone
    dsimp [t]
    linarith [H.g2Lo_le_G2]
  exact hsecant.trans (hlogt.trans hmono)

lemma mPlus_le_of_R_pos (hR : 0 < P.R) :
    (makeCBox box).mPlus <= P.m := by
  let b := makeCBox box
  let t : ℚ := b.g2Lo - b.g2Lo ^ 2 / 2
  by_cases ht : 0 < t
  · have htR : (0 : Real) < (t : Real) := by exact_mod_cast ht
    have hprimeLog : (t : Real) <= Real.log (1 + P.G2) := by
      simpa [b, t] using H.g2Prime_le_log_one_add_G2
    have hgate := P.secant_gate hR
    have hprimeRatio :
        (t : Real) < ((P.m - 2 : Nat) : Real) * P.d / P.q :=
      lt_of_le_of_lt hprimeLog (hgate.1.trans_le hgate.2)
    have hcross :
        (t : Real) * P.q < ((P.m - 2 : Nat) : Real) * P.d := by
      exact (lt_div_iff₀ P.q_pos).mp (by simpa [div_eq_mul_inv, mul_assoc] using hprimeRatio)
    have hqLo : (b.qLo : Real) <= P.q := by
      simpa [b] using H.base.makeCBox_q.1
    have hqLoPos : (0 : Real) < (b.qLo : Real) := by
      simpa [b] using H.qLo_pos
    have hdUp : P.d <= (b.dUp : Real) := by
      simpa [b] using H.base.makeCBox_d.2
    have hdUpPos : (0 : Real) < (b.dUp : Real) := P.d_pos.trans_le hdUp
    have hnum :
        (b.qLo : Real) * (t : Real) <
          ((P.m - 2 : Nat) : Real) * (b.dUp : Real) := by
      have hleft : (b.qLo : Real) * (t : Real) <= P.q * (t : Real) :=
        mul_le_mul_of_nonneg_right hqLo htR.le
      have hright :
          ((P.m - 2 : Nat) : Real) * P.d <=
            ((P.m - 2 : Nat) : Real) * (b.dUp : Real) :=
        mul_le_mul_of_nonneg_left hdUp (by positivity)
      have hcross' : P.q * (t : Real) <
          ((P.m - 2 : Nat) : Real) * P.d := by
        simpa [mul_comm] using hcross
      exact lt_of_le_of_lt hleft (hcross'.trans_le hright)
    have hratioR :
        (b.qLo : Real) * (t : Real) / (b.dUp : Real) <
          ((P.m - 2 : Nat) : Real) := by
      exact (div_lt_iff₀ hdUpPos).2 (by simpa [mul_comm] using hnum)
    have hratioQ : b.qLo * t / b.dUp < (P.m - 2 : Nat) := by
      exact_mod_cast hratioR
    have hratioQ0 : 0 <= b.qLo * t / b.dUp := by
      have hqLoQ : 0 <= b.qLo := by exact_mod_cast hqLoPos.le
      have hdUpQ : 0 <= b.dUp := by exact_mod_cast hdUpPos.le
      exact div_nonneg (mul_nonneg hqLoQ ht.le) hdUpQ
    have hfloor :
        (Rat.floor (b.qLo * t / b.dUp)).toNat < P.m - 2 := by
      rw [show Rat.floor (b.qLo * t / b.dUp) =
        ⌊b.qLo * t / b.dUp⌋ by rfl, Int.floor_toNat]
      exact (Nat.floor_lt hratioQ0).2 hratioQ
    change CBoxData.mPlus b <= P.m
    dsimp [t] at ht hfloor
    simp only [CBoxData.mPlus, ht]
    exact (min_le_left _ _).trans
      (max_le P.m_ge_fifteen (by omega))
  · change CBoxData.mPlus b <= P.m
    dsimp [t] at ht
    simp only [CBoxData.mPlus, ht]
    exact (min_le_left _ _).trans P.m_ge_fifteen

lemma checkedBattle_bounds_normalized_R
    (target : Nat)
    (hcheck : checkCBattle (makeCBox box) target = true)
    (hstart : (makeCBox box).mPlus <= P.m)
    (hc : 0 <= (makeCBox box).cLo) :
    P.R / (P.alpha ^ 3 * P.p ^ (P.m - 2)) <=
      (P.m : Real) * ((makeCBox box).cLo : Real) := by
  let b := makeCBox box
  have hev := checkCBattle_evidence hcheck
  have hstartTarget : b.mPlus <= target := hev.1
  have haux := hev.2.2
  have hxQ : 0 <= b.xUp := by
    exact_mod_cast H.xUp_nonneg
  have hyQ : 0 <= b.yUp := by
    exact_mod_cast H.yUp_nonneg
  have hsQ : 0 <= b.sLo := by
    exact_mod_cast H.sLo_pos.le
  have hstate := initialCBattleStateBounds b b.mPlus hxQ hyQ hsQ
  have hm2 : 2 <= b.mPlus :=
    le_trans (by norm_num) b.fifteen_le_mPlus
  have hl2 : 0 <= (b.l2Up : Real) := by
    have hsquare : 0 <= P.ell ^ 2 := sq_nonneg P.ell
    exact hsquare.trans H.makeCBox_ell_sq.2
  have hcoeff : 0 <=
      (b.pLo : Real) * (b.qLo : Real) / (b.aUp : Real) ^ 3 := by
    exact div_nonneg
      (mul_nonneg H.pLo_pos.le H.qLo_pos.le)
      (pow_nonneg H.aUp_pos.le 3)
  have hnormal := H.normalized_R_le_boxBattle
  by_cases hmTarget : P.m <= target
  · have hloop := checkCBattleAux_sound_between b b.cLo target
      (target - b.mPlus + 1) b.mPlus P.m
      (directedPowUp b.xUp (b.mPlus - 2))
      (directedPowUp b.yUp (b.mPlus - 2))
      (directedPowDown b.sLo (b.mPlus - 2))
      haux hstate hm2 hstart hmTarget hxQ hyQ hsQ H.aLo_pos hl2 hcoeff
    exact hnormal.trans (hloop.trans_eq (by ring))
  · have htargetM : target <= P.m := Nat.le_of_lt (lt_of_not_ge hmTarget)
    have htail := checkCBattleAux_sound_tail b b.cLo target
      (target - b.mPlus + 1) b.mPlus
      (directedPowUp b.xUp (b.mPlus - 2))
      (directedPowUp b.yUp (b.mPlus - 2))
      (directedPowDown b.sLo (b.mPlus - 2))
      haux hstate hm2 hstartTarget hxQ hyQ hsQ H.aLo_pos hl2
    have hdrop :
        cBattleExprR b (P.m - 2) <= cBattleHeadR b (P.m - 2) := by
      unfold cBattleExprR
      have hnonneg : 0 <=
          ((b.pLo : Real) * (b.qLo : Real) / (b.aUp : Real) ^ 3) *
            (b.sLo : Real) ^ (P.m - 2) :=
        mul_nonneg hcoeff (pow_nonneg (by exact_mod_cast hsQ) _)
      linarith
    have hmono : cBattleHeadR b (P.m - 2) <=
        cBattleHeadR b (target - 2) :=
      cBattleHeadR_antitone H.xUp_nonneg H.xUp_le_one
        H.yUp_nonneg H.yUp_le_one H.aLo_pos hl2
        (Nat.sub_le_sub_right htargetM 2)
    have hcMono : (b.cLo : Real) * (target : Real) <=
        (P.m : Real) * (b.cLo : Real) := by
      have hcast : (target : Real) <= (P.m : Real) := by exact_mod_cast htargetM
      have hcR : (0 : Real) <= (b.cLo : Real) := by exact_mod_cast hc
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hcast hcR
    exact hnormal.trans (hdrop.trans (hmono.trans (htail.trans (by
      simpa [mul_comm] using hcMono))))

end CAnalyticBoxContext

theorem checkCRegular_sound {P : AdmissibleParams} {box : RatBox}
    (H : CBoxContext P box) (target : Nat)
    (hcheck : checkCRegular box target = true)
    (hxi : P.xi <= 1) :
    P.R <= P.C * psi P.xi P.rho := by
  have hev := checkCRegular_evidence hcheck
  let HA : CAnalyticBoxContext P box :=
    { toCBoxContext := H
      sqrtOK := hev.1 }
  by_cases hR : 0 < P.R
  · have hfLo : (0 : Real) < ((makeCBox box).fLo : Real) := by
      exact_mod_cast hev.2.1
    have hnorm := HA.checkedBattle_bounds_normalized_R target
      hev.2.2.2.2.2.2
      (HA.mPlus_le_of_R_pos hR)
      hev.2.2.2.2.2.1.le
    have hpay := HA.cLo_le_normalized_payment hxi hfLo
    have hden : 0 < P.alpha ^ 3 * P.p ^ (P.m - 2) :=
      mul_pos (pow_pos P.alpha_pos 3) (pow_pos P.p_pos _)
    exact (div_le_div_iff_of_pos_right hden).1 (hnorm.trans hpay)
  · have hRnonpos : P.R <= 0 := le_of_not_gt hR
    exact hRnonpos.trans
      (mul_nonneg P.C_pos.le (psi_nonneg P.rho_pos.le))

end OddCycleBound.RegionII.Certificate
