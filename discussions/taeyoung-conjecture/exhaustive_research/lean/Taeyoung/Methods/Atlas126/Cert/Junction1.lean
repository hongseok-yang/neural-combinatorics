import Taeyoung.Methods.Atlas126.Cert.Junction1Chunks.Part000
import Taeyoung.Methods.Atlas126.Cert.Junction1Chunks.Part001
import Taeyoung.Methods.Atlas126.Cert.Junction1Chunks.Part002
import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.LocalJunction
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate 1.
Regenerate with `codes/generate_atlas126_junction_lean.py`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein


open Junction1Data

private theorem region33 {x d u : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (15/32 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (5/8 : ℝ))
    (hc0 : 0 ≤ junctionFace1Constraint0 x d u)
    (hc1 : 0 ≤ junctionFace1Constraint1 x d u) :
    0 ≤ junctionFace1Target x d u := by
  rcases le_total d (75/128 : ℝ) with hs | hs
  ·
    have hb := leaf34 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at hb
    linarith only [hb, hc0, hc1]
  ·
    rcases le_total u (9/16 : ℝ) with hs | hs
    ·
      rcases le_total d (165/256 : ℝ) with hs | hs
      ·
        have hb := leaf37 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb, hc0, hc1]
      ·
        exact junctionFace1Middle (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    ·
      rcases le_total d (165/256 : ℝ) with hs | hs
      ·
        have hb := leaf40 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb, hc0, hc1]
      ·
        have hb := leaf41 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb, hc0, hc1]

private theorem region18 {x d u : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (15/32 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (3/8 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ))
    (hc0 : 0 ≤ junctionFace1Constraint0 x d u)
    (hc1 : 0 ≤ junctionFace1Constraint1 x d u) :
    0 ≤ junctionFace1Target x d u := by
  rcases le_total d (75/128 : ℝ) with hs | hs
  ·
    have hb := leaf19 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at hb
    linarith only [hb, hc0, hc1]
  ·
    rcases le_total u (7/16 : ℝ) with hs | hs
    ·
      rcases le_total d (165/256 : ℝ) with hs | hs
      ·
        have hb := leaf22 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb, hc0, hc1]
      ·
        have hb := leaf23 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb, hc0, hc1]
    ·
      rcases le_total d (165/256 : ℝ) with hs | hs
      ·
        have hb := leaf25 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb, hc0, hc1]
      ·
        exact junctionFace1Middle (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

private theorem region6 {x d u : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (15/32 : ℝ) ≤ d)
    (hd1 : d ≤ (45/64 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/8 : ℝ))
    (hc0 : 0 ≤ junctionFace1Constraint0 x d u)
    (hc1 : 0 ≤ junctionFace1Constraint1 x d u) :
    0 ≤ junctionFace1Target x d u := by
  rcases le_total d (75/128 : ℝ) with hs | hs
  ·
    have hb := leaf7 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at hb
    linarith only [hb, hc0, hc1]
  ·
    rcases le_total u (1/16 : ℝ) with hs | hs
    ·
      rcases le_total d (165/256 : ℝ) with hs | hs
      ·
        have hb := leaf10 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb, hc0, hc1]
      ·
        exact junctionFace1Low (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hc1
    ·
      have hb := leaf12 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      push_cast at hb
      linarith only [hb, hc0, hc1]

private theorem region0 {x d u : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ junctionFace1Constraint0 x d u)
    (hc1 : 0 ≤ junctionFace1Constraint1 x d u) :
    0 ≤ junctionFace1Target x d u := by
  rcases le_total u (1/2 : ℝ) with hs | hs
  ·
    rcases le_total d (15/32 : ℝ) with hs | hs
    ·
      have hb := leaf2 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      push_cast at hb
      linarith only [hb, hc0, hc1]
    ·
      rcases le_total u (1/4 : ℝ) with hs | hs
      ·
        rcases le_total d (45/64 : ℝ) with hs | hs
        ·
          rcases le_total u (1/8 : ℝ) with hs | hs
          ·
            exact region6 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hc0 hc1
          ·
            have hb := leaf13 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
            push_cast at hb
            linarith only [hb, hc0, hc1]
        ·
          have hb := leaf14 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hb
          linarith only [hb, hc0, hc1]
      ·
        rcases le_total d (45/64 : ℝ) with hs | hs
        ·
          rcases le_total u (3/8 : ℝ) with hs | hs
          ·
            have hb := leaf17 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
            push_cast at hb
            linarith only [hb, hc0, hc1]
          ·
            exact region18 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hc0 hc1
        ·
          have hb := leaf27 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hb
          linarith only [hb, hc0, hc1]
  ·
    rcases le_total d (15/32 : ℝ) with hs | hs
    ·
      have hb := leaf29 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      push_cast at hb
      linarith only [hb, hc0, hc1]
    ·
      rcases le_total u (3/4 : ℝ) with hs | hs
      ·
        rcases le_total d (45/64 : ℝ) with hs | hs
        ·
          rcases le_total u (5/8 : ℝ) with hs | hs
          ·
            exact region33 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hc0 hc1
          ·
            have hb := leaf42 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
            push_cast at hb
            linarith only [hb, hc0, hc1]
        ·
          have hb := leaf43 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hb
          linarith only [hb, hc0, hc1]
      ·
        rcases le_total d (45/64 : ℝ) with hs | hs
        ·
          have hb := leaf45 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hb
          linarith only [hb, hc0, hc1]
        ·
          have hb := leaf46 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hb
          linarith only [hb, hc0, hc1]

theorem junctionFace1 {x d u : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ junctionFace1Constraint0 x d u)
    (hc1 : 0 ≤ junctionFace1Constraint1 x d u) :
    0 ≤ junctionFace1Target x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1

end Taeyoung.Methods.Atlas126
