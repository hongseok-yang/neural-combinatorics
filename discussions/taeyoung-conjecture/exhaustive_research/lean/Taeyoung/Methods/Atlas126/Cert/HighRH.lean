import Taeyoung.Methods.Atlas126.Cert.HighRHChunks.Part000
import Taeyoung.Methods.Atlas126.HighRh
import Taeyoung.Methods.Atlas126.HighRhLocal

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126

open HighRHData

private theorem region15 {x d u : ℝ}
    (hx0 : (7/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (1/2 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highRhTarget x d u := by
  rcases le_total u (1/2 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (1/2 : ℝ) := hs
    rcases le_total u (1/4 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/4 : ℝ) := hs
      rcases le_total u (1/8 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (1/8 : ℝ) := hs
        have hb := leaf18 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (1/8 : ℝ) ≤ u := hs
        have hb := leaf19 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hu0 : (1/4 : ℝ) ≤ u := hs
      have hb := leaf20 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hu0 : (1/2 : ℝ) ≤ u := hs
    have hb := leaf21 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region10 {x d u : ℝ}
    (hx0 : (3/4 : ℝ) ≤ x)
    (hx1 : x ≤ (7/8 : ℝ))
    (hd0 : (1/2 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
     :
    0 ≤ highRhTarget x d u := by
  rcases le_total u (1/4 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (1/4 : ℝ) := hs
    have hb := leaf11 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (1/4 : ℝ) ≤ u := hs
    have hb := leaf12 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
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
    0 ≤ highRhTarget x d u := by
  rcases le_total d (1/2 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/2 : ℝ) := hs
    exact highRhLocal0 (by linarith only [hx0]) (by linarith only [hx1]) (by linarith only [hd0]) (by linarith only [hd1]) (by linarith only [hu0]) (by linarith only [hu1]) 
  ·
    have hd0 : (1/2 : ℝ) ≤ d := hs
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
        rcases le_total u (1/2 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (1/2 : ℝ) := hs
          have hb := leaf6 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (1/2 : ℝ) ≤ u := hs
          have hb := leaf7 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
      ·
        have hx0 : (3/4 : ℝ) ≤ x := hs
        rcases le_total x (7/8 : ℝ) with hs | hs
        ·
          have hx1 : x ≤ (7/8 : ℝ) := hs
          rcases le_total u (1/2 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (1/2 : ℝ) := hs
            exact region10 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hu0 : (1/2 : ℝ) ≤ u := hs
            have hb := leaf13 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
        ·
          have hx0 : (7/8 : ℝ) ≤ x := hs
          rcases le_total x (15/16 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (15/16 : ℝ) := hs
            exact region15 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hx0 : (15/16 : ℝ) ≤ x := hs
            exact highRhLocal1 (by linarith only [hx0]) (by linarith only [hx1]) (by linarith only [hd0]) (by linarith only [hd1]) (by linarith only [hu0]) (by linarith only [hu1]) 

theorem junctionFaceHR {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ highRhTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1


end Taeyoung.Methods.Atlas126
