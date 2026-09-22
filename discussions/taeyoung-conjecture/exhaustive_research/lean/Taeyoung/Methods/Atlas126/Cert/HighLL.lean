import Taeyoung.Methods.Atlas126.Cert.HighLLChunks.Part000
import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Atlas126.LocalHighLL

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126

open HighLLData

private theorem region13 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (7/8 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (3/4 : ℝ))
     :
    0 ≤ highLLTarget x d u := by
  rcases le_total d (15/16 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (15/16 : ℝ) := hs
    have hb := leaf14 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hd0 : (15/16 : ℝ) ≤ d := hs
    have hb := leaf15 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highLLTarget x d u := by
  rcases le_total d (1/2 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/2 : ℝ) := hs
    have hb := leaf1 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hd0 : (1/2 : ℝ) ≤ d := hs
    rcases le_total u (1/2 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/2 : ℝ) := hs
      rcases le_total d (3/4 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (3/4 : ℝ) := hs
        have hb := leaf4 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hd0 : (3/4 : ℝ) ≤ d := hs
        rcases le_total d (7/8 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (7/8 : ℝ) := hs
          have hb := leaf6 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hd0 : (7/8 : ℝ) ≤ d := hs
          have hb := leaf7 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
    ·
      have hu0 : (1/2 : ℝ) ≤ u := hs
      rcases le_total d (3/4 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (3/4 : ℝ) := hs
        have hb := leaf9 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hd0 : (3/4 : ℝ) ≤ d := hs
        rcases le_total u (3/4 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (3/4 : ℝ) := hs
          rcases le_total d (7/8 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (7/8 : ℝ) := hs
            have hb := leaf12 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hd0 : (7/8 : ℝ) ≤ d := hs
            exact region13 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hu0 : (3/4 : ℝ) ≤ u := hs
          exact highLLLocal (by linarith only [hx0]) (by linarith only [hx1]) (by linarith only [hd0]) (by linarith only [hd1]) (by linarith only [hu0]) (by linarith only [hu1]) 

theorem junctionFaceHLL {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ highLLTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1


end Taeyoung.Methods.Atlas126
