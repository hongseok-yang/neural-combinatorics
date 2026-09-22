import Taeyoung.Methods.Atlas126.Cert.LowC1Chunks.Part000
import Taeyoung.Methods.Atlas126.Cert.LowC1Chunks.Part001
import Taeyoung.Methods.Atlas126.Cert.LowC1Chunks.Part002
import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.LowCandidates
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate C1.
Regenerate with `codes/generate_atlas126_junction_lean.py`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein


open LowC1Data

private theorem region28 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (165/256 : ℝ) ≤ d)
    (hd1 : d ≤ (345/512 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (17/32 : ℝ))
    (hc0 : 0 ≤ cFace1Constraint0 x d u)
    (hc1 : 0 ≤ cFace1Constraint1 x d u)
    (hc2 : 0 ≤ cFace1Constraint2 x d u) :
    0 ≤ cFace1Target x d u := by
  rcases le_total d (675/1024 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (675/1024 : ℝ) := hs
    have hb := leaf29 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]
  ·
    have hd0 : (675/1024 : ℝ) ≤ d := hs
    have hb := leaf30 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region20 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (75/128 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (3/4 : ℝ))
    (hc0 : 0 ≤ cFace1Constraint0 x d u)
    (hc1 : 0 ≤ cFace1Constraint1 x d u)
    (hc2 : 0 ≤ cFace1Constraint2 x d u) :
    0 ≤ cFace1Target x d u := by
  rcases le_total u (5/8 : ℝ) with hs | hs
  ·
    have hu1 : u ≤ (5/8 : ℝ) := hs
    rcases le_total d (165/256 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (165/256 : ℝ) := hs
      rcases le_total x (25/32 : ℝ) with hs | hs
      ·
        have hx1 : x ≤ (25/32 : ℝ) := hs
        have hb := leaf23 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]
      ·
        have hx0 : (25/32 : ℝ) ≤ x := hs
        have hb := leaf24 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]
    ·
      have hd0 : (165/256 : ℝ) ≤ d := hs
      rcases le_total u (9/16 : ℝ) with hs | hs
      ·
        have hu1 : u ≤ (9/16 : ℝ) := hs
        rcases le_total d (345/512 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (345/512 : ℝ) := hs
          rcases le_total u (17/32 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (17/32 : ℝ) := hs
            exact region28 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
          ·
            have hu0 : (17/32 : ℝ) ≤ u := hs
            have hb := leaf31 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
        ·
          have hd0 : (345/512 : ℝ) ≤ d := hs
          have hb := leaf32 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
      ·
        have hu0 : (9/16 : ℝ) ≤ u := hs
        have hb := leaf33 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]
  ·
    have hu0 : (5/8 : ℝ) ≤ u := hs
    have hb := leaf34 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]

private theorem region8 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (165/256 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
    (hc0 : 0 ≤ cFace1Constraint0 x d u)
    (hc1 : 0 ≤ cFace1Constraint1 x d u)
    (hc2 : 0 ≤ cFace1Constraint2 x d u) :
    0 ≤ cFace1Target x d u := by
  rcases le_total d (345/512 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (345/512 : ℝ) := hs
    have hb := leaf9 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]
  ·
    have hd0 : (345/512 : ℝ) ≤ d := hs
    rcases le_total u (1/4 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/4 : ℝ) := hs
      have hb := leaf11 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1, hc2]
    ·
      have hu0 : (1/4 : ℝ) ≤ u := hs
      have hb := leaf12 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1, hc2]

private theorem region0 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ cFace1Constraint0 x d u)
    (hc1 : 0 ≤ cFace1Constraint1 x d u)
    (hc2 : 0 ≤ cFace1Constraint2 x d u) :
    0 ≤ cFace1Target x d u := by
  rcases le_total d (15/32 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (15/32 : ℝ) := hs
    have hb := leaf1 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    linarith only [hb, hc0, hc1, hc2]
  ·
    have hd0 : (15/32 : ℝ) ≤ d := hs
    rcases le_total u (1/2 : ℝ) with hs | hs
    ·
      have hu1 : u ≤ (1/2 : ℝ) := hs
      rcases le_total d (45/64 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (45/64 : ℝ) := hs
        rcases le_total d (75/128 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (75/128 : ℝ) := hs
          have hb := leaf5 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
        ·
          have hd0 : (75/128 : ℝ) ≤ d := hs
          rcases le_total d (165/256 : ℝ) with hs | hs
          ·
            have hd1 : d ≤ (165/256 : ℝ) := hs
            have hb := leaf7 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
          ·
            have hd0 : (165/256 : ℝ) ≤ d := hs
            exact region8 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
      ·
        have hd0 : (45/64 : ℝ) ≤ d := hs
        rcases le_total u (1/4 : ℝ) with hs | hs
        ·
          have hu1 : u ≤ (1/4 : ℝ) := hs
          have hb := leaf14 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
        ·
          have hu0 : (1/4 : ℝ) ≤ u := hs
          have hb := leaf15 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
    ·
      have hu0 : (1/2 : ℝ) ≤ u := hs
      rcases le_total d (45/64 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (45/64 : ℝ) := hs
        rcases le_total d (75/128 : ℝ) with hs | hs
        ·
          have hd1 : d ≤ (75/128 : ℝ) := hs
          have hb := leaf18 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
          push_cast at hb
          linarith only [hb, hc0, hc1, hc2]
        ·
          have hd0 : (75/128 : ℝ) ≤ d := hs
          rcases le_total u (3/4 : ℝ) with hs | hs
          ·
            have hu1 : u ≤ (3/4 : ℝ) := hs
            exact region20 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2
          ·
            have hu0 : (3/4 : ℝ) ≤ u := hs
            have hb := leaf35 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
            push_cast at hb
            linarith only [hb, hc0, hc1, hc2]
      ·
        have hd0 : (45/64 : ℝ) ≤ d := hs
        have hb := leaf36 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1, hc2]

theorem junctionFaceC1 {x d u : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x)
    (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ cFace1Constraint0 x d u)
    (hc1 : 0 ≤ cFace1Constraint1 x d u)
    (hc2 : 0 ≤ cFace1Constraint2 x d u) :
    0 ≤ cFace1Target x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1 hc2

end Taeyoung.Methods.Atlas126
