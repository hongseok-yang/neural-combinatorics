import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part000
import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part001
import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part002
import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part003
import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part004
import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part005
import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part006
import Taeyoung.Methods.Atlas126.Cert.LowCSChunks.Part007
import Taeyoung.Methods.Atlas126.LowCandidates

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126

open LowCSData

private theorem region65 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (1/36 : ℝ) ≤ d)
    (hd1 : d ≤ (1/18 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (3/8 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total u (5/16 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (5/16 : ℝ) := hs
    rcases le_total u (9/32 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (9/32 : ℝ) := hs
      rcases le_total d (1/24 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (1/24 : ℝ) := hs
        rcases le_total x (25/32 : ℝ) with hs | hs
        ·
          have hx1 : x ≤ (25/32 : ℝ) := hs
          have hb := leaf69 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hx0 : (25/32 : ℝ) ≤ x := hs
          have hb := leaf70 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
      ·
        have hd0 : (1/24 : ℝ) ≤ d := hs
        have hb := leaf71 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hu0 : (9/32 : ℝ) ≤ u := hs
      have hb := leaf72 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hu0 : (5/16 : ℝ) ≤ u := hs
    have hb := leaf73 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region58 {x d u : ℝ}
    (hx0 : (55/64 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (1/72 : ℝ) ≤ d)
    (hd1 : d ≤ (1/36 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (9/32 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total d (1/48 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/48 : ℝ) := hs
    rcases le_total d (5/288 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (5/288 : ℝ) := hs
      have hb := leaf60 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hd0 : (5/288 : ℝ) ≤ d := hs
      have hb := leaf61 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hd0 : (1/48 : ℝ) ≤ d := hs
    have hb := leaf62 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region53 {x d u : ℝ}
    (hx0 : (25/32 : ℝ) ≤ x)
    (hx1 : x ≤ (55/64 : ℝ))
    (hd0 : (1/72 : ℝ) ≤ d)
    (hd1 : d ≤ (1/36 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (9/32 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total d (1/48 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/48 : ℝ) := hs
    rcases le_total d (5/288 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (5/288 : ℝ) := hs
      have hb := leaf55 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hd0 : (5/288 : ℝ) ≤ d := hs
      have hb := leaf56 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hd0 : (1/48 : ℝ) ≤ d := hs
    have hb := leaf57 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region49 {x d u : ℝ}
    (hx0 : (25/32 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (1/144 : ℝ) ≤ d)
    (hd1 : d ≤ (1/72 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (9/32 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total x (55/64 : ℝ) with hs | hs
  ·
    have hx1 : x ≤ (55/64 : ℝ) := hs
    have hb := leaf50 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hx0 : (55/64 : ℝ) ≤ x := hs
    have hb := leaf51 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region42 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/36 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (3/8 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total u (5/16 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (5/16 : ℝ) := hs
    rcases le_total x (25/32 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (25/32 : ℝ) := hs
      have hb := leaf44 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hx0 : (25/32 : ℝ) ≤ x := hs
      rcases le_total u (9/32 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (9/32 : ℝ) := hs
        rcases le_total d (1/72 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (1/72 : ℝ) := hs
          rcases le_total d (1/144 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (1/144 : ℝ) := hs
            have hb := leaf48 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hd0 : (1/144 : ℝ) ≤ d := hs
            exact region49 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hd0 : (1/72 : ℝ) ≤ d := hs
          rcases le_total x (55/64 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (55/64 : ℝ) := hs
            exact region53 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hx0 : (55/64 : ℝ) ≤ x := hs
            exact region58 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
      ·
        have hu0 : (9/32 : ℝ) ≤ u := hs
        have hb := leaf63 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
  ·
    have hu0 : (5/16 : ℝ) ≤ u := hs
    have hb := leaf64 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region23 {x d u : ℝ}
    (hx0 : (25/32 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (1/144 : ℝ) ≤ d)
    (hd1 : d ≤ (1/72 : ℝ))
    (hu0 : (7/32 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total u (15/64 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (15/64 : ℝ) := hs
    have hb := leaf24 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (15/64 : ℝ) ≤ u := hs
    rcases le_total x (55/64 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (55/64 : ℝ) := hs
      rcases le_total d (1/96 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (1/96 : ℝ) := hs
        have hb := leaf27 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hd0 : (1/96 : ℝ) ≤ d := hs
        have hb := leaf28 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hx0 : (55/64 : ℝ) ≤ x := hs
      rcases le_total d (1/96 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (1/96 : ℝ) := hs
        have hb := leaf30 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hd0 : (1/96 : ℝ) ≤ d := hs
        have hb := leaf31 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]

private theorem region18 {x d u : ℝ}
    (hx0 : (25/32 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/144 : ℝ))
    (hu0 : (7/32 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total u (15/64 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (15/64 : ℝ) := hs
    rcases le_total x (55/64 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (55/64 : ℝ) := hs
      have hb := leaf20 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hx0 : (55/64 : ℝ) ≤ x := hs
      have hb := leaf21 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hu0 : (15/64 : ℝ) ≤ u := hs
    have hb := leaf22 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region7 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/18 : ℝ))
    (hu0 : (3/16 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total d (1/36 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/36 : ℝ) := hs
    rcases le_total x (25/32 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (25/32 : ℝ) := hs
      rcases le_total d (1/72 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (1/72 : ℝ) := hs
        have hb := leaf10 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hd0 : (1/72 : ℝ) ≤ d := hs
        rcases le_total u (7/32 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (7/32 : ℝ) := hs
          have hb := leaf12 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (7/32 : ℝ) ≤ u := hs
          have hb := leaf13 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
    ·
      have hx0 : (25/32 : ℝ) ≤ x := hs
      rcases le_total u (7/32 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (7/32 : ℝ) := hs
        have hb := leaf15 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (7/32 : ℝ) ≤ u := hs
        rcases le_total d (1/72 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (1/72 : ℝ) := hs
          rcases le_total d (1/144 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (1/144 : ℝ) := hs
            exact region18 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hd0 : (1/144 : ℝ) ≤ d := hs
            exact region23 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hd0 : (1/72 : ℝ) ≤ d := hs
          rcases le_total x (55/64 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (55/64 : ℝ) := hs
            have hb := leaf33 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hx0 : (55/64 : ℝ) ≤ x := hs
            have hb := leaf34 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
  ·
    have hd0 : (1/36 : ℝ) ≤ d := hs
    rcases le_total d (1/24 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (1/24 : ℝ) := hs
      have hb := leaf36 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hd0 : (1/24 : ℝ) ≤ d := hs
      have hb := leaf37 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region0 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/9 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ cSlackTarget x d u := by
  rcases le_total u (1/2 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (1/2 : ℝ) := hs
    rcases le_total u (1/4 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/4 : ℝ) := hs
      rcases le_total d (1/18 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (1/18 : ℝ) := hs
        rcases le_total u (1/8 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (1/8 : ℝ) := hs
          have hb := leaf4 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (1/8 : ℝ) ≤ u := hs
          rcases le_total u (3/16 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (3/16 : ℝ) := hs
            have hb := leaf6 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hu0 : (3/16 : ℝ) ≤ u := hs
            exact region7 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
      ·
        have hd0 : (1/18 : ℝ) ≤ d := hs
        have hb := leaf38 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hu0 : (1/4 : ℝ) ≤ u := hs
      rcases le_total d (1/18 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (1/18 : ℝ) := hs
        rcases le_total u (3/8 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (3/8 : ℝ) := hs
          rcases le_total d (1/36 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (1/36 : ℝ) := hs
            exact region42 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hd0 : (1/36 : ℝ) ≤ d := hs
            exact region65 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hu0 : (3/8 : ℝ) ≤ u := hs
          have hb := leaf74 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
      ·
        have hd0 : (1/18 : ℝ) ≤ d := hs
        have hb := leaf75 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
  ·
    have hu0 : (1/2 : ℝ) ≤ u := hs
    have hb := leaf76 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

theorem junctionFaceCS {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/9 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ cSlackTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1


end Taeyoung.Methods.Atlas126
