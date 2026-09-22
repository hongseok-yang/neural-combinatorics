import Taeyoung.Methods.Atlas126.Cert.LowA1Chunks.Part000
import Taeyoung.Methods.Atlas126.Cert.LowA1Chunks.Part001
import Taeyoung.Methods.Atlas126.Cert.LowA1Chunks.Part002
import Taeyoung.Methods.Atlas126.Cert.LowA1Chunks.Part003
import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.LowCandidates
import Taeyoung.Methods.Atlas126.LocalAUpper
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate A1.
Regenerate with `codes/generate_atlas126_junction_lean.py`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein


open LowA1Data

private theorem region56 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (75/128 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (3/4 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total u (5/8 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (5/8 : ℝ) := hs
    rcases le_total d (165/256 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (165/256 : ℝ) := hs
      have hb := leaf58 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1, hc2]
    ·
      have hd0 : (165/256 : ℝ) ≤ d := hs
      have hb := leaf59 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1, hc2]
  ·
    have hu0 : (5/8 : ℝ) ≤ u := hs
    have hb := leaf60 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region53 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (15/32 : ℝ) ≤ d)
    (hd1 : d ≤ (75/128 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (3/4 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total x (5/16 : ℝ) with hs | hs
  ·
    have hx1 : x ≤ (5/16 : ℝ) := hs
    have hb := leaf54 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]
  ·
    have hx0 : (5/16 : ℝ) ≤ x := hs
    have hb := leaf55 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region46 {x d u : ℝ}
    (hx0 : (5/16 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (75/128 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total d (165/256 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (165/256 : ℝ) := hs
    have hb := leaf47 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]
  ·
    have hd0 : (165/256 : ℝ) ≤ d := hs
    have hb := leaf48 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region35 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/16 : ℝ))
    (hd0 : (15/32 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total d (75/128 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (75/128 : ℝ) := hs
    rcases le_total u (3/8 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (3/8 : ℝ) := hs
      have hb := leaf37 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1, hc2]
    ·
      have hu0 : (3/8 : ℝ) ≤ u := hs
      rcases le_total x (5/32 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (5/32 : ℝ) := hs
        have hb := leaf39 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]
      ·
        have hx0 : (5/32 : ℝ) ≤ x := hs
        have hb := leaf40 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]
  ·
    have hd0 : (75/128 : ℝ) ≤ d := hs
    have hb := leaf41 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region25 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/64 : ℝ))
    (hd0 : (15/32 : ℝ) ≤ d)
    (hd1 : d ≤ (135/256 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/8 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total u (1/16 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (1/16 : ℝ) := hs
    rcases le_total x (5/128 : ℝ) with hs | hs
    ·
      have hx1 : x ≤ (5/128 : ℝ) := hs
      exact upperTargetA_nonneg (by linarith only [hx0]) (by linarith only [hx1]) (by linarith only [hd0]) (by linarith only [hd1]) (by linarith only [hu0]) (by linarith only [hu1]) 
    ·
      have hx0 : (5/128 : ℝ) ≤ x := hs
      have hb := leaf28 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1, hc2]
  ·
    have hu0 : (1/16 : ℝ) ≤ u := hs
    have hb := leaf29 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region20 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/16 : ℝ))
    (hd0 : (15/32 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/4 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total x (5/32 : ℝ) with hs | hs
  ·
    have hx1 : x ≤ (5/32 : ℝ) := hs
    rcases le_total d (75/128 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (75/128 : ℝ) := hs
      rcases le_total u (1/8 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (1/8 : ℝ) := hs
        rcases le_total x (5/64 : ℝ) with hs | hs
        ·
          have hx1 : x ≤ (5/64 : ℝ) := hs
          rcases le_total d (135/256 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (135/256 : ℝ) := hs
            exact region25 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
          ·
            have hd0 : (135/256 : ℝ) ≤ d := hs
            have hb := leaf30 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
        ·
          have hx0 : (5/64 : ℝ) ≤ x := hs
          have hb := leaf31 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
      ·
        have hu0 : (1/8 : ℝ) ≤ u := hs
        have hb := leaf32 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]
    ·
      have hd0 : (75/128 : ℝ) ≤ d := hs
      have hb := leaf33 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1, hc2]
  ·
    have hx0 : (5/32 : ℝ) ≤ x := hs
    have hb := leaf34 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region7 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/16 : ℝ))
    (hd0 : (15/64 : ℝ) ≤ d)
    (hd1 : d ≤ (15/32 : ℝ))
    (hu0 : (1/4 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total d (45/128 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (45/128 : ℝ) := hs
    have hb := leaf8 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]
  ·
    have hd0 : (45/128 : ℝ) ≤ d := hs
    have hb := leaf9 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  rcases le_total d (15/32 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (15/32 : ℝ) := hs
    rcases le_total d (15/64 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (15/64 : ℝ) := hs
      have hb := leaf2 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      have hc := hc0
      linarith only [hb, hc]
    ·
      have hd0 : (15/64 : ℝ) ≤ d := hs
      rcases le_total u (1/2 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (1/2 : ℝ) := hs
        rcases le_total u (1/4 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (1/4 : ℝ) := hs
          have hb := leaf5 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
        ·
          have hu0 : (1/4 : ℝ) ≤ u := hs
          rcases le_total x (5/16 : ℝ) with hs | hs
          ·
            have hx1 : x ≤ (5/16 : ℝ) := hs
            exact region7 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
          ·
            have hx0 : (5/16 : ℝ) ≤ x := hs
            have hb := leaf10 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
      ·
        have hu0 : (1/2 : ℝ) ≤ u := hs
        rcases le_total x (5/16 : ℝ) with hs | hs
        ·
          have hx1 : x ≤ (5/16 : ℝ) := hs
          rcases le_total d (45/128 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (45/128 : ℝ) := hs
            have hb := leaf13 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
          ·
            have hd0 : (45/128 : ℝ) ≤ d := hs
            have hb := leaf14 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
        ·
          have hx0 : (5/16 : ℝ) ≤ x := hs
          have hb := leaf15 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
  ·
    have hd0 : (15/32 : ℝ) ≤ d := hs
    rcases le_total u (1/2 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/2 : ℝ) := hs
      rcases le_total x (5/16 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (5/16 : ℝ) := hs
        rcases le_total d (45/64 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (45/64 : ℝ) := hs
          rcases le_total u (1/4 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (1/4 : ℝ) := hs
            exact region20 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
          ·
            have hu0 : (1/4 : ℝ) ≤ u := hs
            exact region35 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
        ·
          have hd0 : (45/64 : ℝ) ≤ d := hs
          have hb := leaf42 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
      ·
        have hx0 : (5/16 : ℝ) ≤ x := hs
        rcases le_total d (45/64 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (45/64 : ℝ) := hs
          rcases le_total d (75/128 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (75/128 : ℝ) := hs
            have hb := leaf45 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
          ·
            have hd0 : (75/128 : ℝ) ≤ d := hs
            exact region46 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
        ·
          have hd0 : (45/64 : ℝ) ≤ d := hs
          have hb := leaf49 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
    ·
      have hu0 : (1/2 : ℝ) ≤ u := hs
      rcases le_total d (45/64 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (45/64 : ℝ) := hs
        rcases le_total u (3/4 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (3/4 : ℝ) := hs
          rcases le_total d (75/128 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (75/128 : ℝ) := hs
            exact region53 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
          ·
            have hd0 : (75/128 : ℝ) ≤ d := hs
            exact region56 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
        ·
          have hu0 : (3/4 : ℝ) ≤ u := hs
          have hb := leaf61 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
      ·
        have hd0 : (45/64 : ℝ) ≤ d := hs
        have hb := leaf62 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]

theorem junctionFaceA1 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ aFace1Constraint0 x d u)
    (hc1 : 0 ≤ aFace1Constraint1 x d u)
    (hc2 : 0 ≤ aFace1Constraint2 x d u) :
    0 ≤ aFace1Target x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2

end Taeyoung.Methods.Atlas126
