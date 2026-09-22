import Taeyoung.Methods.Atlas126.Cert.HighSlackChunks.Part000
import Taeyoung.Methods.Atlas126.HighScaledSlack

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126

open HighSlackData

private theorem region0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highScaledSlackTarget x d u := by
  rcases le_total u (1/2 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (1/2 : ℝ) := hs
    have hb := leaf1 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (1/2 : ℝ) ≤ u := hs
    rcases le_total x (1/2 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (1/2 : ℝ) := hs
      have hb := leaf3 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hx0 : (1/2 : ℝ) ≤ x := hs
      rcases le_total x (3/4 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (3/4 : ℝ) := hs
        have hb := leaf5 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hx0 : (3/4 : ℝ) ≤ x := hs
        have hb := leaf6 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]

theorem junctionFaceHS {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ highScaledSlackTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1


end Taeyoung.Methods.Atlas126
