import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part000
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part001
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part002
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part003
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part004
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part005
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part006
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part007
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part008
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part009
import Taeyoung.Methods.Atlas126.Cert.LowARootSlackChunks.Part010
import Taeyoung.Methods.Atlas126.ARootSlack
import Taeyoung.Methods.Atlas126.LocalARootSlack

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126

open LowARootSlackData

private theorem region125 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/32 : ℝ))
    (hd0 : (5/16 : ℝ) ≤ d)
    (hd1 : d ≤ (3/8 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (5/16 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total u (9/32 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (9/32 : ℝ) := hs
    have hb := leaf126 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (9/32 : ℝ) ≤ u := hs
    have hb := leaf127 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region110 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/128 : ℝ))
    (hd0 : (17/64 : ℝ) ≤ d)
    (hd1 : d ≤ (9/32 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (9/32 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total u (17/64 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (17/64 : ℝ) := hs
    rcases le_total u (33/128 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (33/128 : ℝ) := hs
      have hb := leaf112 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hu0 : (33/128 : ℝ) ≤ u := hs
      have hb := leaf113 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hu0 : (17/64 : ℝ) ≤ u := hs
    have hb := leaf114 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region97 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/128 : ℝ))
    (hd0 : (1/4 : ℝ) ≤ d)
    (hd1 : d ≤ (17/64 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (9/32 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total u (17/64 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (17/64 : ℝ) := hs
    rcases le_total x (5/256 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (5/256 : ℝ) := hs
      rcases le_total d (33/128 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (33/128 : ℝ) := hs
        rcases le_total u (33/128 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (33/128 : ℝ) := hs
          exact aRootSlackLocal (by linarith only [hx0]) (by linarith only [hx1]) (by linarith only [hd0]) (by linarith only [hd1]) (by linarith only [hu0]) (by linarith only [hu1]) 
        ·
          have hu0 : (33/128 : ℝ) ≤ u := hs
          have hb := leaf102 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
      ·
        have hd0 : (33/128 : ℝ) ≤ d := hs
        rcases le_total u (33/128 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (33/128 : ℝ) := hs
          rcases le_total u (65/256 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (65/256 : ℝ) := hs
            have hb := leaf105 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hu0 : (65/256 : ℝ) ≤ u := hs
            have hb := leaf106 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
        ·
          have hu0 : (33/128 : ℝ) ≤ u := hs
          have hb := leaf107 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
    ·
      have hx0 : (5/256 : ℝ) ≤ x := hs
      have hb := leaf108 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hu0 : (17/64 : ℝ) ≤ u := hs
    have hb := leaf109 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region92 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/32 : ℝ))
    (hd0 : (1/4 : ℝ) ≤ d)
    (hd1 : d ≤ (5/16 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (5/16 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total x (5/64 : ℝ) with hs | hs
  ·
    have hx1 : x ≤ (5/64 : ℝ) := hs
    rcases le_total d (9/32 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (9/32 : ℝ) := hs
      rcases le_total u (9/32 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (9/32 : ℝ) := hs
        rcases le_total x (5/128 : ℝ) with hs | hs
        ·
          have hx1 : x ≤ (5/128 : ℝ) := hs
          rcases le_total d (17/64 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (17/64 : ℝ) := hs
            exact region97 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hd0 : (17/64 : ℝ) ≤ d := hs
            exact region110 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hx0 : (5/128 : ℝ) ≤ x := hs
          have hb := leaf115 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
      ·
        have hu0 : (9/32 : ℝ) ≤ u := hs
        have hb := leaf116 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hd0 : (9/32 : ℝ) ≤ d := hs
      rcases le_total u (9/32 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (9/32 : ℝ) := hs
        rcases le_total u (17/64 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (17/64 : ℝ) := hs
          have hb := leaf119 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (17/64 : ℝ) ≤ u := hs
          have hb := leaf120 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
      ·
        have hu0 : (9/32 : ℝ) ≤ u := hs
        have hb := leaf121 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
  ·
    have hx0 : (5/64 : ℝ) ≤ x := hs
    have hb := leaf122 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region87 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/16 : ℝ))
    (hd0 : (1/4 : ℝ) ≤ d)
    (hd1 : d ≤ (1/2 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total d (3/8 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (3/8 : ℝ) := hs
    rcases le_total u (3/8 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (3/8 : ℝ) := hs
      rcases le_total x (5/32 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (5/32 : ℝ) := hs
        rcases le_total d (5/16 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (5/16 : ℝ) := hs
          rcases le_total u (5/16 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (5/16 : ℝ) := hs
            exact region92 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hu0 : (5/16 : ℝ) ≤ u := hs
            have hb := leaf123 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
        ·
          have hd0 : (5/16 : ℝ) ≤ d := hs
          rcases le_total u (5/16 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (5/16 : ℝ) := hs
            exact region125 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hu0 : (5/16 : ℝ) ≤ u := hs
            have hb := leaf128 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
      ·
        have hx0 : (5/32 : ℝ) ≤ x := hs
        have hb := leaf129 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hu0 : (3/8 : ℝ) ≤ u := hs
      have hb := leaf130 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hd0 : (3/8 : ℝ) ≤ d := hs
    rcases le_total u (3/8 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (3/8 : ℝ) := hs
      rcases le_total u (5/16 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (5/16 : ℝ) := hs
        have hb := leaf133 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (5/16 : ℝ) ≤ u := hs
        have hb := leaf134 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hu0 : (3/8 : ℝ) ≤ u := hs
      have hb := leaf135 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region81 {x d u : ℝ}
    (hx0 : (5/16 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total d (1/8 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/8 : ℝ) := hs
    have hb := leaf82 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hd0 : (1/8 : ℝ) ≤ d := hs
    have hb := leaf83 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region70 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total d (1/8 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/8 : ℝ) := hs
    have hb := leaf71 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hd0 : (1/8 : ℝ) ≤ d := hs
    rcases le_total u (3/8 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (3/8 : ℝ) := hs
      rcases le_total x (5/32 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (5/32 : ℝ) := hs
        rcases le_total d (3/16 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (3/16 : ℝ) := hs
          have hb := leaf75 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hd0 : (3/16 : ℝ) ≤ d := hs
          rcases le_total u (5/16 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (5/16 : ℝ) := hs
            have hb := leaf77 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hu0 : (5/16 : ℝ) ≤ u := hs
            have hb := leaf78 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
      ·
        have hx0 : (5/32 : ℝ) ≤ x := hs
        have hb := leaf79 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
    ·
      have hu0 : (3/8 : ℝ) ≤ u := hs
      have hb := leaf80 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region60 {x d u : ℝ}
    (hx0 : (5/16 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total u (1/8 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (1/8 : ℝ) := hs
    have hb := leaf61 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (1/8 : ℝ) ≤ u := hs
    rcases le_total d (1/8 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (1/8 : ℝ) := hs
      rcases le_total u (3/16 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (3/16 : ℝ) := hs
        have hb := leaf64 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (3/16 : ℝ) ≤ u := hs
        rcases le_total d (1/16 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (1/16 : ℝ) := hs
          have hb := leaf66 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hd0 : (1/16 : ℝ) ≤ d := hs
          have hb := leaf67 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
    ·
      have hd0 : (1/8 : ℝ) ≤ d := hs
      have hb := leaf68 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region44 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/128 : ℝ))
    (hd0 : (15/64 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (7/32 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total u (15/64 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (15/64 : ℝ) := hs
    have hb := leaf45 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (15/64 : ℝ) ≤ u := hs
    rcases le_total x (5/256 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (5/256 : ℝ) := hs
      rcases le_total d (31/128 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (31/128 : ℝ) := hs
        rcases le_total u (31/128 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (31/128 : ℝ) := hs
          have hb := leaf49 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (31/128 : ℝ) ≤ u := hs
          rcases le_total u (63/256 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (63/256 : ℝ) := hs
            have hb := leaf51 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hu0 : (63/256 : ℝ) ≤ u := hs
            have hb := leaf52 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
      ·
        have hd0 : (31/128 : ℝ) ≤ d := hs
        rcases le_total u (31/128 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (31/128 : ℝ) := hs
          have hb := leaf54 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (31/128 : ℝ) ≤ u := hs
          exact aRootSlackLocal (by linarith only [hx0]) (by linarith only [hx1]) (by linarith only [hd0]) (by linarith only [hd1]) (by linarith only [hu0]) (by linarith only [hu1]) 
    ·
      have hx0 : (5/256 : ℝ) ≤ x := hs
      have hb := leaf56 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region39 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/128 : ℝ))
    (hd0 : (7/32 : ℝ) ≤ d)
    (hd1 : d ≤ (15/64 : ℝ))
    (hu0 : (7/32 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total u (15/64 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (15/64 : ℝ) := hs
    have hb := leaf40 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (15/64 : ℝ) ≤ u := hs
    rcases le_total u (31/128 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (31/128 : ℝ) := hs
      have hb := leaf42 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hu0 : (31/128 : ℝ) ≤ u := hs
      have hb := leaf43 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region28 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/32 : ℝ))
    (hd0 : (3/16 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (3/16 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total x (5/64 : ℝ) with hs | hs
  ·
    have hx1 : x ≤ (5/64 : ℝ) := hs
    rcases le_total d (7/32 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (7/32 : ℝ) := hs
      rcases le_total u (7/32 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (7/32 : ℝ) := hs
        have hb := leaf31 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (7/32 : ℝ) ≤ u := hs
        rcases le_total u (15/64 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (15/64 : ℝ) := hs
          have hb := leaf33 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (15/64 : ℝ) ≤ u := hs
          have hb := leaf34 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
    ·
      have hd0 : (7/32 : ℝ) ≤ d := hs
      rcases le_total u (7/32 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (7/32 : ℝ) := hs
        have hb := leaf36 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (7/32 : ℝ) ≤ u := hs
        rcases le_total x (5/128 : ℝ) with hs | hs
        ·
          have hx1 : x ≤ (5/128 : ℝ) := hs
          rcases le_total d (15/64 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (15/64 : ℝ) := hs
            exact region39 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hd0 : (15/64 : ℝ) ≤ d := hs
            exact region44 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hx0 : (5/128 : ℝ) ≤ x := hs
          have hb := leaf57 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
  ·
    have hx0 : (5/64 : ℝ) ≤ x := hs
    have hb := leaf58 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]

private theorem region21 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/32 : ℝ))
    (hd0 : (1/8 : ℝ) ≤ d)
    (hd1 : d ≤ (3/16 : ℝ))
    (hu0 : (3/16 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total u (7/32 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (7/32 : ℝ) := hs
    have hb := leaf22 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb]
  ·
    have hu0 : (7/32 : ℝ) ≤ u := hs
    rcases le_total d (5/32 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (5/32 : ℝ) := hs
      have hb := leaf24 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hd0 : (5/32 : ℝ) ≤ d := hs
      have hb := leaf25 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

private theorem region5 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/4 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total d (1/8 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/8 : ℝ) := hs
    rcases le_total u (1/8 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/8 : ℝ) := hs
      have hb := leaf7 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hu0 : (1/8 : ℝ) ≤ u := hs
      rcases le_total u (3/16 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (3/16 : ℝ) := hs
        have hb := leaf9 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (3/16 : ℝ) ≤ u := hs
        rcases le_total d (1/16 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (1/16 : ℝ) := hs
          have hb := leaf11 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hd0 : (1/16 : ℝ) ≤ d := hs
          rcases le_total u (7/32 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (7/32 : ℝ) := hs
            have hb := leaf13 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hu0 : (7/32 : ℝ) ≤ u := hs
            have hb := leaf14 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
  ·
    have hd0 : (1/8 : ℝ) ≤ d := hs
    rcases le_total u (1/8 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/8 : ℝ) := hs
      have hb := leaf16 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
    ·
      have hu0 : (1/8 : ℝ) ≤ u := hs
      rcases le_total x (5/32 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (5/32 : ℝ) := hs
        rcases le_total d (3/16 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (3/16 : ℝ) := hs
          rcases le_total u (3/16 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (3/16 : ℝ) := hs
            have hb := leaf20 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hu0 : (3/16 : ℝ) ≤ u := hs
            exact region21 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hd0 : (3/16 : ℝ) ≤ d := hs
          rcases le_total u (3/16 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (3/16 : ℝ) := hs
            have hb := leaf27 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
          ·
            have hu0 : (3/16 : ℝ) ≤ u := hs
            exact region28 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
      ·
        have hx0 : (5/32 : ℝ) ≤ x := hs
        have hb := leaf59 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]

private theorem region0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ aRootSlackTarget x d u := by
  rcases le_total d (1/2 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (1/2 : ℝ) := hs
    rcases le_total u (1/2 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/2 : ℝ) := hs
      rcases le_total d (1/4 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (1/4 : ℝ) := hs
        rcases le_total u (1/4 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (1/4 : ℝ) := hs
          rcases le_total x (5/16 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (5/16 : ℝ) := hs
            exact region5 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hx0 : (5/16 : ℝ) ≤ x := hs
            exact region60 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
        ·
          have hu0 : (1/4 : ℝ) ≤ u := hs
          rcases le_total x (5/16 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (5/16 : ℝ) := hs
            exact region70 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hx0 : (5/16 : ℝ) ≤ x := hs
            exact region81 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
      ·
        have hd0 : (1/4 : ℝ) ≤ d := hs
        rcases le_total u (1/4 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (1/4 : ℝ) := hs
          have hb := leaf85 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (1/4 : ℝ) ≤ u := hs
          rcases le_total x (5/16 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (5/16 : ℝ) := hs
            exact region87 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 
          ·
            have hx0 : (5/16 : ℝ) ≤ x := hs
            have hb := leaf136 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb]
    ·
      have hu0 : (1/2 : ℝ) ≤ u := hs
      have hb := leaf137 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]
  ·
    have hd0 : (1/2 : ℝ) ≤ d := hs
    rcases le_total u (1/2 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/2 : ℝ) := hs
      rcases le_total u (1/4 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (1/4 : ℝ) := hs
        have hb := leaf140 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb]
      ·
        have hu0 : (1/4 : ℝ) ≤ u := hs
        rcases le_total u (3/8 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (3/8 : ℝ) := hs
          have hb := leaf142 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
        ·
          have hu0 : (3/8 : ℝ) ≤ u := hs
          have hb := leaf143 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb]
    ·
      have hu0 : (1/2 : ℝ) ≤ u := hs
      have hb := leaf144 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb]

theorem junctionFaceARS {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ aRootSlackTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1


end Taeyoung.Methods.Atlas126
