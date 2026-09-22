import Taeyoung.Methods.Atlas126.Cert.JunctionSlackChunks.Part000
import Taeyoung.Methods.Atlas126.Cert.JunctionSlackChunks.Part001
import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.JunctionSlack
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate S.
Regenerate with `codes/generate_atlas126_junction_lean.py`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein


open JunctionSlackData

private theorem region0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/9 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ junctionSlackTarget x d u := by
  rcases le_total u (1/2 : ℝ) with hs | hs
  ·
    rcases le_total u (1/4 : ℝ) with hs | hs
    ·
      rcases le_total u (1/8 : ℝ) with hs | hs
      ·
        have hb := leaf3 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb]
      ·
        have hb := leaf4 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb]
    ·
      rcases le_total d (1/18 : ℝ) with hs | hs
      ·
        rcases le_total d (1/36 : ℝ) with hs | hs
        ·
          have hb := leaf7 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hb
          linarith only [hb]
        ·
          have hb := leaf8 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          push_cast at hb
          linarith only [hb]
      ·
        have hb := leaf9 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        push_cast at hb
        linarith only [hb]
  ·
    have hb := leaf10 (x := x) (d := d) (u := u) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at hb
    linarith only [hb]

theorem junctionSlack_nonneg {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1/16 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/9 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ junctionSlackTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 

end Taeyoung.Methods.Atlas126
