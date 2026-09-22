import Taeyoung.Methods.Atlas126.Cert.LowA2Chunks.Part000
import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.LowCandidates
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate A2.
Regenerate with `codes/generate_atlas126_junction_lean.py`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein


open LowA2Data

private theorem region0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ aFace2Constraint0 x d u)
    (hc1 : 0 ≤ aFace2Constraint1 x d u) :
    0 ≤ aFace2Target x d u := by
  rcases le_total d (15/32 : ℝ) with hs | hs
  ·
    have hd1 : d ≤ (15/32 : ℝ) := hs
    rcases le_total d (15/64 : ℝ) with hs | hs
    ·
      have hd1 : d ≤ (15/64 : ℝ) := hs
      have hb := leaf2 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
      push_cast at hb
      linarith only [hb, hc0, hc1]
    ·
      have hd0 : (15/64 : ℝ) ≤ d := hs
      rcases le_total d (45/128 : ℝ) with hs | hs
      ·
        have hd1 : d ≤ (45/128 : ℝ) := hs
        have hb := leaf4 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1]
      ·
        have hd0 : (45/128 : ℝ) ≤ d := hs
        have hb := leaf5 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
        push_cast at hb
        linarith only [hb, hc0, hc1]
  ·
    have hd0 : (15/32 : ℝ) ≤ d := hs
    have hb := leaf6 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
    push_cast at hb
    have hc := hc0
    linarith only [hb, hc]

theorem junctionFaceA2 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
    (hc0 : 0 ≤ aFace2Constraint0 x d u)
    (hc1 : 0 ≤ aFace2Constraint1 x d u) :
    0 ≤ aFace2Target x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 hc0 hc1

end Taeyoung.Methods.Atlas126
