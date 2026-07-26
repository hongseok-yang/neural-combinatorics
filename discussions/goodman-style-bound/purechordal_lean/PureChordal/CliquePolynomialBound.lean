import PureChordal.Algebra
import PureChordal.MoonMoser
import Mathlib.Tactic

/-!
# Clique-density polynomial bound

Moon--Moser propagates the sharp adjacent-clique lower bound.  We retain a
cross-multiplied formulation throughout, so no clique density is divided by
until its positivity has been established.
-/

namespace PureChordal

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The coefficient in the adjacent step from `K_{j-1}` to `K_j`. -/
def cliqueStepFactor (j : ℕ) (p : ℝ) : ℝ :=
  1 - ((j - 1 : ℕ) : ℝ) * (1 - p)

@[simp] lemma cliqueStepFactor_two (p : ℝ) :
    cliqueStepFactor 2 p = p := by
  simp [cliqueStepFactor]

lemma cliqueStepFactor_nonneg
    {r j : ℕ} {p : ℝ}
    (hr : 3 ≤ r) (hj : j ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ p) :
    0 ≤ cliqueStepFactor j p := by
  let A : ℝ := ((j - 1 : ℕ) : ℝ)
  let R : ℝ := ((r - 1 : ℕ) : ℝ)
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < r - 1 by omega)
  have hAR : A ≤ R := by
    dsimp [A, R]
    exact_mod_cast Nat.sub_le_sub_right hj 1
  have hA0 : 0 ≤ A := by positivity
  have hq : 1 - p ≤ 1 / R := by
    dsimp [R]
    linarith
  have hmul : A * (1 - p) ≤ A * (1 / R) :=
    mul_le_mul_of_nonneg_left hq hA0
  have htail : A * (1 / R) ≤ 1 := by
    calc
      A * (1 / R) ≤ R * (1 / R) :=
        mul_le_mul_of_nonneg_right hAR (by positivity)
      _ = 1 := by field_simp
  dsimp [cliqueStepFactor]
  dsimp [A] at hmul htail
  linarith

lemma cliqueStepFactor_pos_of_lt
    {r j : ℕ} {p : ℝ}
    (hr : 3 ≤ r) (hj : j < r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ p) :
    0 < cliqueStepFactor j p := by
  let A : ℝ := ((j - 1 : ℕ) : ℝ)
  let R : ℝ := ((r - 1 : ℕ) : ℝ)
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < r - 1 by omega)
  have hAR : A < R := by
    dsimp [A, R]
    exact_mod_cast (show j - 1 < r - 1 by omega)
  have hA0 : 0 ≤ A := by positivity
  have hq : 1 - p ≤ 1 / R := by
    dsimp [R]
    linarith
  have hmul : A * (1 - p) ≤ A * (1 / R) :=
    mul_le_mul_of_nonneg_left hq hA0
  have htail : A * (1 / R) < 1 := by
    calc
      A * (1 / R) < R * (1 / R) :=
        mul_lt_mul_of_pos_right hAR (by positivity)
      _ = 1 := by field_simp
  dsimp [cliqueStepFactor]
  dsimp [A] at hmul htail
  linarith

private theorem cliqueDensity_step_lower_and_pos
    (W : Graphon Ω μ) {r : ℕ} (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W) :
    ∀ j, 2 ≤ j → j ≤ r →
      cliqueStepFactor j (cliqueDensity 2 W) *
          cliqueDensity (j - 1) W ≤ cliqueDensity j W ∧
        (j < r → 0 < cliqueDensity j W) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj2 hjr
      by_cases hjbase : j = 2
      · subst j
        constructor
        · simp
        · intro h2r
          simpa using
            (cliqueStepFactor_pos_of_lt hr h2r hp)
      · have hj3 : 3 ≤ j := by omega
        let m := j - 1
        have hm2 : 2 ≤ m := by dsimp [m]; omega
        have hmj : m < j := by dsimp [m]; omega
        have hmle : m ≤ r := by dsimp [m]; omega
        have hmlt : m < r := by dsimp [m]; omega
        have ihm := ih m hmj hm2 hmle
        have hstepm := ihm.1
        have htm : 0 < cliqueDensity m W := ihm.2 hmlt
        have htm1 : 0 < cliqueDensity (m - 1) W := by
          by_cases hm_base : m = 2
          · have hm1eq : m - 1 = 1 := by omega
            rw [hm1eq, cliqueDensity_one]
            norm_num
          · have hm3 : 3 ≤ m := by omega
            have hm1j : m - 1 < j := by omega
            have hm1le : m - 1 ≤ r := by omega
            exact (ih (m - 1) hm1j (by omega) hm1le).2 (by omega)
        have hmm :=
          cliqueDensity_moonMoser_succ (m - 1) W
        have hmm' :
            (m : ℝ) * cliqueDensity m W ^ 2 ≤
              cliqueDensity (m - 1) W * cliqueDensity m W +
                ((m - 1 : ℕ) : ℝ) *
                  cliqueDensity (m - 1) W *
                    cliqueDensity (m + 1) W := by
          have hidx : m - 1 + 1 = m := by omega
          have hidx' : m - 1 + 2 = m + 1 := by omega
          have hcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ m)]
            push_cast
            ring
          simpa only [hidx, hidx', hcast] using hmm
        let cm := cliqueStepFactor m (cliqueDensity 2 W)
        let cn := cliqueStepFactor (m + 1) (cliqueDensity 2 W)
        have hcoefficient :
            (m : ℝ) * cm - 1 = ((m - 1 : ℕ) : ℝ) * cn := by
          dsimp [cm, cn, cliqueStepFactor]
          rw [Nat.cast_sub (by omega : 1 ≤ m)]
          push_cast
          ring
        have hstepm' :
            cm * cliqueDensity (m - 1) W ≤ cliqueDensity m W := by
          simpa [cm] using hstepm
        have hbracket :
            ((m - 1 : ℕ) : ℝ) * cn *
                cliqueDensity (m - 1) W ≤
              (m : ℝ) * cliqueDensity m W -
                cliqueDensity (m - 1) W := by
          rw [← hcoefficient]
          nlinarith
        have hbmul := mul_le_mul_of_nonneg_left hbracket htm.le
        have hrearrange :
            cliqueDensity m W *
                ((m : ℝ) * cliqueDensity m W -
                  cliqueDensity (m - 1) W) ≤
              ((m - 1 : ℕ) : ℝ) *
                cliqueDensity (m - 1) W *
                  cliqueDensity (m + 1) W := by
          nlinarith [hmm']
        have hfactorpos :
            0 < ((m - 1 : ℕ) : ℝ) * cliqueDensity (m - 1) W :=
          mul_pos (by exact_mod_cast (show 0 < m - 1 by omega)) htm1
        have hcancel :
            ((m - 1 : ℕ) : ℝ) * cliqueDensity (m - 1) W *
                (cn * cliqueDensity m W) ≤
              ((m - 1 : ℕ) : ℝ) * cliqueDensity (m - 1) W *
                cliqueDensity (m + 1) W := by
          calc
            ((m - 1 : ℕ) : ℝ) * cliqueDensity (m - 1) W *
                (cn * cliqueDensity m W) =
                cliqueDensity m W *
                  (((m - 1 : ℕ) : ℝ) * cn *
                    cliqueDensity (m - 1) W) := by ring
            _ ≤ cliqueDensity m W *
                ((m : ℝ) * cliqueDensity m W -
                  cliqueDensity (m - 1) W) := hbmul
            _ ≤ _ := hrearrange
        have hnext :
            cn * cliqueDensity m W ≤ cliqueDensity (m + 1) W :=
          le_of_mul_le_mul_left hcancel hfactorpos
        have hj_eq : j = m + 1 := by dsimp [m]; omega
        constructor
        · simpa [cn, hj_eq] using hnext
        · intro hjrlt
          have hcnpos :
              0 < cn :=
            cliqueStepFactor_pos_of_lt hr (by omega : m + 1 < r) hp
          have hprod : 0 < cn * cliqueDensity m W :=
            mul_pos hcnpos htm
          simpa [hj_eq] using (lt_of_lt_of_le hprod hnext)

/-- The one-step clique-density lower bound, valid up to the threshold clique
size `r`. -/
theorem cliqueDensity_step_lower
    (W : Graphon Ω μ) {r : ℕ} (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W)
    {j : ℕ} (hj2 : 2 ≤ j) (hjr : j ≤ r) :
    cliqueStepFactor j (cliqueDensity 2 W) *
        cliqueDensity (j - 1) W ≤ cliqueDensity j W :=
  (cliqueDensity_step_lower_and_pos W hr hp j hj2 hjr).1

lemma cliquePoly_nonneg_of_threshold
    {r s : ℕ} {p : ℝ} (hr : 3 ≤ r) (hsr : s ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ p) :
    0 ≤ cliquePoly s p := by
  apply cliquePoly_nonneg
  intro a ha
  have h :=
    cliqueStepFactor_nonneg (r := r) (j := a + 1)
      hr (by omega) hp
  simpa [cliqueStepFactor] using h

lemma cliquePoly_pos_of_lt_threshold
    {r s : ℕ} {p : ℝ} (hr : 3 ≤ r) (hsr : s < r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ p) :
    0 < cliquePoly s p := by
  apply cliquePoly_pos
  intro a ha
  have h :=
    cliqueStepFactor_pos_of_lt (r := r) (j := a + 1)
      hr (by omega) hp
  simpa [cliqueStepFactor] using h

/-- Every clique density up to `r` dominates the explicit polynomial
`A_j(p)`. -/
theorem cliqueDensity_ge_cliquePoly
    (W : Graphon Ω μ) {r : ℕ} (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W) :
    ∀ {j : ℕ}, j ≤ r →
      cliquePoly j (cliqueDensity 2 W) ≤ cliqueDensity j W := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjr
      by_cases hj0 : j = 0
      · subst j
        simp
      by_cases hj1 : j = 1
      · subst j
        simp
      have hj2 : 2 ≤ j := by omega
      have hjprev : j - 1 < j := by omega
      have hprev :
          cliquePoly (j - 1) (cliqueDensity 2 W) ≤
            cliqueDensity (j - 1) W :=
        ih (j - 1) hjprev (by omega)
      have hfactor :
          0 ≤ cliqueStepFactor j (cliqueDensity 2 W) :=
        cliqueStepFactor_nonneg hr hjr hp
      have hstep :=
        cliqueDensity_step_lower W hr hp hj2 hjr
      have hj_eq : j - 1 + 1 = j := by omega
      calc
        cliquePoly j (cliqueDensity 2 W) =
            cliqueStepFactor j (cliqueDensity 2 W) *
              cliquePoly (j - 1) (cliqueDensity 2 W) := by
          rw [← hj_eq, cliquePoly_succ]
          simp [cliqueStepFactor, mul_comm]
        _ ≤ cliqueStepFactor j (cliqueDensity 2 W) *
              cliqueDensity (j - 1) W :=
          mul_le_mul_of_nonneg_left hprev hfactor
        _ ≤ cliqueDensity j W := hstep

/-- Iterated adjacent-ratio bound in cross-multiplied form.  This is valid
even at the boundary where `A_r(p)` or `t_r` vanishes. -/
theorem cliqueDensity_mul_cliquePoly_le
    (W : Graphon Ω μ) {r s j : ℕ} (hr : 3 ≤ r)
    (hp : 1 - 1 / (((r - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 W)
    (hsj : s ≤ j) (hjr : j ≤ r) :
    cliqueDensity s W * cliquePoly j (cliqueDensity 2 W) ≤
      cliqueDensity j W * cliquePoly s (cliqueDensity 2 W) := by
  induction j, hsj using Nat.le_induction with
  | base => simp
  | succ n hsn ih =>
      have hn1r : n + 1 ≤ r := by omega
      by_cases hn0 : n = 0
      · subst n
        have hs0 : s = 0 := by omega
        subst s
        simp
      · have hn1two : 2 ≤ n + 1 := by omega
        have hfactor :
            0 ≤ cliqueStepFactor (n + 1) (cliqueDensity 2 W) :=
          cliqueStepFactor_nonneg hr hn1r hp
        have hstep :=
          cliqueDensity_step_lower W hr hp hn1two hn1r
        have hAs :
            0 ≤ cliquePoly s (cliqueDensity 2 W) :=
          cliquePoly_nonneg_of_threshold hr (by omega) hp
        calc
          cliqueDensity s W *
              cliquePoly (n + 1) (cliqueDensity 2 W) =
              cliqueStepFactor (n + 1) (cliqueDensity 2 W) *
                (cliqueDensity s W *
                  cliquePoly n (cliqueDensity 2 W)) := by
            rw [cliquePoly_succ]
            simp [cliqueStepFactor]
            ring
          _ ≤ cliqueStepFactor (n + 1) (cliqueDensity 2 W) *
                (cliqueDensity n W *
                  cliquePoly s (cliqueDensity 2 W)) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hfactor
          _ = (cliqueStepFactor (n + 1) (cliqueDensity 2 W) *
                cliqueDensity n W) *
                  cliquePoly s (cliqueDensity 2 W) := by ring
          _ ≤ cliqueDensity (n + 1) W *
                cliquePoly s (cliqueDensity 2 W) :=
            mul_le_mul_of_nonneg_right hstep hAs

end PureChordal
