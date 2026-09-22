import Taeyoung.Methods.Atlas126.Cert.HighTHChunks.Part000
import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Atlas126.LocalHighTH

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126

open HighTHData

private theorem region20 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1/32 : ℝ))
    (hd0 : (31/32 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/32 : ℝ))
     :
    0 ≤ highTHTarget x d u := by
  rcases le_total x (1/64 : ℝ) with hs | hs
  ·
    have hx1 : x ≤ (1/64 : ℝ) := hs
    rcases le_total d (63/64 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (63/64 : ℝ) := hs
      have hb := leaf22 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hd0 : (63/64 : ℝ) ≤ d := hs
      rcases le_total u (1/64 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (1/64 : ℝ) := hs
        exact highTHLocal (by linarith only [hx0]) (by linarith only [hx1]) (by linarith only [hd0]) (by linarith only [hd1]) (by linarith only [hu0]) (by linarith only [hu1]) 
      ·
        have hu0 : (1/64 : ℝ) ≤ u := hs
        have hb := leaf25 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
  ·
    have hx0 : (1/64 : ℝ) ≤ x := hs
    have hb := leaf26 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region13 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1/16 : ℝ))
    (hd0 : (7/8 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/8 : ℝ))
     :
    0 ≤ highTHTarget x d u := by
  rcases le_total d (15/16 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (15/16 : ℝ) := hs
    have hb := leaf14 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hd0 : (15/16 : ℝ) ≤ d := hs
    rcases le_total u (1/16 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/16 : ℝ) := hs
      rcases le_total x (1/32 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (1/32 : ℝ) := hs
        rcases le_total d (31/32 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (31/32 : ℝ) := hs
          have hb := leaf18 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hd0 : (31/32 : ℝ) ≤ d := hs
          rcases le_total u (1/32 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (1/32 : ℝ) := hs
            exact region20 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hu0 : (1/32 : ℝ) ≤ u := hs
            have hb := leaf27 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
      ·
        have hx0 : (1/32 : ℝ) ≤ x := hs
        have hb := leaf28 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hu0 : (1/16 : ℝ) ≤ u := hs
      have hb := leaf29 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region7 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1/4 : ℝ))
    (hd0 : (3/4 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
     :
    0 ≤ highTHTarget x d u := by
  rcases le_total u (1/4 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (1/4 : ℝ) := hs
    rcases le_total x (1/8 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (1/8 : ℝ) := hs
      rcases le_total d (7/8 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (7/8 : ℝ) := hs
        have hb := leaf10 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hd0 : (7/8 : ℝ) ≤ d := hs
        rcases le_total u (1/8 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (1/8 : ℝ) := hs
          rcases le_total x (1/16 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (1/16 : ℝ) := hs
            exact region13 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hx0 : (1/16 : ℝ) ≤ x := hs
            have hb := leaf30 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
        ·
          have hu0 : (1/8 : ℝ) ≤ u := hs
          have hb := leaf31 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
    ·
      have hx0 : (1/8 : ℝ) ≤ x := hs
      have hb := leaf32 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hu0 : (1/4 : ℝ) ≤ u := hs
    have hb := leaf33 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
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
    0 ≤ highTHTarget x d u := by
  rcases le_total x (1/2 : ℝ) with hs | hs
  ·
    have hx1 : x ≤ (1/2 : ℝ) := hs
    rcases le_total d (1/2 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (1/2 : ℝ) := hs
      have hb := leaf2 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hd0 : (1/2 : ℝ) ≤ d := hs
      rcases le_total u (1/2 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (1/2 : ℝ) := hs
        rcases le_total x (1/4 : ℝ) with hs | hs
        ·
          have hx1 : x ≤ (1/4 : ℝ) := hs
          rcases le_total d (3/4 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (3/4 : ℝ) := hs
            have hb := leaf6 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hd0 : (3/4 : ℝ) ≤ d := hs
            exact region7 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hx0 : (1/4 : ℝ) ≤ x := hs
          have hb := leaf34 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
      ·
        have hu0 : (1/2 : ℝ) ≤ u := hs
        have hb := leaf35 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
  ·
    have hx0 : (1/2 : ℝ) ≤ x := hs
    have hb := leaf36 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

theorem junctionFaceHTH {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ highTHTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1


end Taeyoung.Methods.Atlas126
