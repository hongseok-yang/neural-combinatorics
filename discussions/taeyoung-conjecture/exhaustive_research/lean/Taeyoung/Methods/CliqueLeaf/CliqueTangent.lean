import Taeyoung.Methods.PureChordal.CliquePolynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# A tangent line under the clique polynomial

The clique common-leaf argument needs an affine minorant of
`A_m(z) = ∏_{j<m} (1 - j(1-z))` through a chosen point `c`, valid on the whole
interval `[a_m, 1]` where the factors are nonnegative.  The note obtains it from
convexity of `A_m` and takes the tangent at `c`.

Here the same bound is proved directly, with no derivative and no `ConvexOn`.
`cliquePolyDeriv` is what the derivative *would* be, but it is defined by the
product rule as a recursion, and `cliquePoly_tangent` is proved by induction on
`m`: writing `t = w - c`, the inductive step is

  `A_{m+1}(w) = A_m(w)·ℓ_m(w) ≥ (A_m(c) + A_m'(c)t)(ℓ_m(c) + m t)`
             `= A_{m+1}(c) + A_{m+1}'(c) t + A_m'(c)·m·t²`,

and the leftover square is nonnegative.  The step needs the inner bound to be
nonnegative before it may be multiplied; when it is not, `t < 0` forces the whole
affine expression below `0 ≤ A_{m+1}(w)`, which is the second case.

Throughout, the clique size is written `s + 2` so that the threshold
`a_m = 1 - 1/(m-1)` is `1 - 1/(s+1)` with no truncated subtraction.
-/

namespace Taeyoung.Methods.CliqueLeaf

open Taeyoung.Methods.PureChordal

/-! ### The formal derivative -/

/-- `A_s'(p)`, defined by the product rule rather than by differentiating. -/
def cliquePolyDeriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | (s + 1), p =>
      cliquePolyDeriv s p * (1 - (s : ℝ) * (1 - p)) + (s : ℝ) * cliquePoly s p

@[simp] lemma cliquePolyDeriv_zero (p : ℝ) : cliquePolyDeriv 0 p = 0 := rfl

lemma cliquePolyDeriv_succ (s : ℕ) (p : ℝ) :
    cliquePolyDeriv (s + 1) p =
      cliquePolyDeriv s p * (1 - (s : ℝ) * (1 - p)) + (s : ℝ) * cliquePoly s p :=
  rfl

lemma cliquePolyDeriv_nonneg {s : ℕ} {p : ℝ}
    (hfactor : ∀ a < s, 0 ≤ 1 - (a : ℝ) * (1 - p)) :
    0 ≤ cliquePolyDeriv s p := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [cliquePolyDeriv_succ]
      have h1 : 0 ≤ cliquePolyDeriv s p := ih fun a ha ↦ hfactor a (by omega)
      have h2 : 0 ≤ 1 - (s : ℝ) * (1 - p) := hfactor s (by omega)
      have h3 : 0 ≤ cliquePoly s p := cliquePoly_nonneg fun a ha ↦ hfactor a (by omega)
      exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg (Nat.cast_nonneg s) h3)

/-! ### The tangent bound -/

/-- **An affine minorant of `A_s` through `c`.**  Wherever the factors are
nonnegative at both `c` and `w`, the "tangent line" at `c` lies under `A_s`. -/
theorem cliquePoly_tangent {s : ℕ} {c w : ℝ}
    (hc : ∀ a < s, 0 ≤ 1 - (a : ℝ) * (1 - c))
    (hw : ∀ a < s, 0 ≤ 1 - (a : ℝ) * (1 - w)) :
    cliquePoly s c + cliquePolyDeriv s c * (w - c) ≤ cliquePoly s w := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hc' : ∀ a < s, 0 ≤ 1 - (a : ℝ) * (1 - c) := fun a ha ↦ hc a (by omega)
      have hw' : ∀ a < s, 0 ≤ 1 - (a : ℝ) * (1 - w) := fun a ha ↦ hw a (by omega)
      have hIH := ih hc' hw'
      have hP : 0 ≤ cliquePoly s c := cliquePoly_nonneg hc'
      have hPw : 0 ≤ cliquePoly s w := cliquePoly_nonneg hw'
      have hD : 0 ≤ cliquePolyDeriv s c := cliquePolyDeriv_nonneg hc'
      have hL : 0 ≤ 1 - (s : ℝ) * (1 - c) := hc s (by omega)
      have hLw : 0 ≤ 1 - (s : ℝ) * (1 - w) := hw s (by omega)
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
      rw [cliquePoly_succ, cliquePoly_succ, cliquePolyDeriv_succ]
      set P := cliquePoly s c with hPdef
      set Pw := cliquePoly s w with hPwdef
      set D := cliquePolyDeriv s c with hDdef
      set t := w - c with htdef
      have hfac : 1 - (s : ℝ) * (1 - w) = (1 - (s : ℝ) * (1 - c)) + (s : ℝ) * t := by
        rw [htdef]; ring
      rcases le_or_gt 0 (P + D * t) with hcase | hcase
      · have hmul : (P + D * t) * (1 - (s : ℝ) * (1 - w)) ≤
            Pw * (1 - (s : ℝ) * (1 - w)) :=
          mul_le_mul_of_nonneg_right hIH hLw
        rw [hfac] at hmul ⊢
        nlinarith [mul_nonneg (mul_nonneg hD hs0) (sq_nonneg t)]
      · have htneg : t < 0 := by
          by_contra hcon
          simp only [not_lt] at hcon
          nlinarith [mul_nonneg hD hcon]
        have h1 : (1 - (s : ℝ) * (1 - c)) * (P + D * t) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hL hcase.le
        have h2 : (s : ℝ) * P * t ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs0 hP) htneg.le
        have h3 : 0 ≤ Pw * (1 - (s : ℝ) * (1 - w)) := mul_nonneg hPw hLw
        nlinarith

/-! ### The threshold `a_m` -/

/-- The clique threshold `a_m = 1 - 1/(m-1)`, for `m = s + 2`. -/
noncomputable def cliqueThreshold (s : ℕ) : ℝ := 1 - 1 / ((s : ℝ) + 1)

lemma cliqueThreshold_le_one (s : ℕ) : cliqueThreshold s ≤ 1 := by
  have : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  simp only [cliqueThreshold]
  have : 0 < 1 / ((s : ℝ) + 1) := by positivity
  linarith

/-- Above the threshold, every factor of `A_{s+2}` is nonnegative. -/
lemma factor_nonneg (s : ℕ) {x : ℝ} (hx : cliqueThreshold s ≤ x) :
    ∀ a < s + 2, 0 ≤ 1 - (a : ℝ) * (1 - x) := by
  intro a ha
  have hs0 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hacast : (a : ℝ) ≤ (s : ℝ) + 1 := by
    have h : a ≤ s + 1 := by omega
    exact_mod_cast h
  have hxx : 1 - 1 / ((s : ℝ) + 1) ≤ x := hx
  rcases le_or_gt (1 - x) 0 with h | h
  · nlinarith [Nat.cast_nonneg (α := ℝ) a]
  · have hle : 1 - x ≤ 1 / ((s : ℝ) + 1) := by linarith
    have hmul : (a : ℝ) * (1 - x) ≤ ((s : ℝ) + 1) * (1 / ((s : ℝ) + 1)) :=
      mul_le_mul hacast hle h.le (by linarith)
    rw [mul_one_div, div_self (ne_of_gt hs0)] at hmul
    linarith

/-- The clique polynomial vanishes at its threshold. -/
lemma cliquePoly_threshold (s : ℕ) : cliquePoly (s + 2) (cliqueThreshold s) = 0 := by
  have hs0 : ((s : ℝ) + 1) ≠ 0 := by positivity
  have hlast : (1 : ℝ) - ((s + 1 : ℕ) : ℝ) * (1 - cliqueThreshold s) = 0 := by
    simp only [cliqueThreshold]
    push_cast
    field_simp
    ring
  rw [show s + 2 = (s + 1) + 1 from rfl, cliquePoly_succ, hlast, mul_zero]

end Taeyoung.Methods.CliqueLeaf
