import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# A checked exact-rational multivariate Bernstein format

The external emitters only serialize rational coefficients.  Lean checks that
every coefficient is nonnegative and every multi-index is in range.  A target
polynomial is connected to the resulting Bernstein form by an ordinary Lean
algebra proof; `sound_for` packages that checked identity with positivity of
the Bernstein basis on the unit cube.  Thus no Python acceptance result is a
premise of a mathematical theorem.
-/

namespace OddCycleBound.RegionII.Certificate

open scoped BigOperators

structure BernsteinTerm (n : Nat) where
  index : Fin n → Nat
  coefficient : ℚ
deriving DecidableEq

structure BernsteinCertificate (n : Nat) where
  degree : Fin n → Nat
  terms : List (BernsteinTerm n)

def BernsteinCertificate.check {n : Nat}
    (certificate : BernsteinCertificate n) : Bool :=
  certificate.terms.all fun term =>
    decide (0 ≤ term.coefficient) &&
      (List.ofFn fun i : Fin n => decide (term.index i ≤ certificate.degree i)).all id

lemma BernsteinCertificate.valid_of_check {n : Nat}
    {certificate : BernsteinCertificate n}
    (hcheck : certificate.check = true) :
    ∀ term ∈ certificate.terms,
      0 ≤ term.coefficient ∧ ∀ i, term.index i ≤ certificate.degree i := by
  intro term hterm
  have htermCheck := List.all_eq_true.mp hcheck term hterm
  have hparts := Bool.and_eq_true_iff.mp htermCheck
  refine ⟨of_decide_eq_true hparts.1, fun i => ?_⟩
  have hi := List.all_eq_true.mp hparts.2
    (decide (term.index i ≤ certificate.degree i)) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact of_decide_eq_true hi

def bernsteinBasis (degree index : Nat) (x : ℝ) : ℝ :=
  Nat.choose degree index * x ^ index * (1 - x) ^ (degree - index)

noncomputable def bernsteinRatio (degree power index : Nat) : ℝ :=
  Nat.choose index power / Nat.choose degree power

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma monomial_eq_bernstein_sum_eight (power : Fin 9) (x : ℝ) :
    x ^ (power : Nat) =
      ∑ index : Fin 9,
        bernsteinRatio 8 power index * bernsteinBasis 8 index x := by
  fin_cases power <;>
    norm_num [bernsteinRatio, bernsteinBasis, Fin.sum_univ_succ, Nat.choose] <;>
    ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma monomial_eq_bernstein_sum_ten (power : Fin 11) (x : ℝ) :
    x ^ (power : Nat) =
      ∑ index : Fin 11,
        bernsteinRatio 10 power index * bernsteinBasis 10 index x := by
  fin_cases power <;>
    norm_num [bernsteinRatio, bernsteinBasis, Fin.sum_univ_succ, Nat.choose] <;>
    ring

def BernsteinTerm.eval {n : Nat} (degree : Fin n → Nat)
    (term : BernsteinTerm n) (point : Fin n → ℝ) : ℝ :=
  term.coefficient * ∏ i : Fin n, bernsteinBasis (degree i) (term.index i) (point i)

def BernsteinCertificate.eval {n : Nat} (certificate : BernsteinCertificate n)
    (point : Fin n → ℝ) : ℝ :=
  (certificate.terms.map (fun term => term.eval certificate.degree point)).sum

lemma bernsteinBasis_nonneg {degree index : Nat} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinBasis degree index x := by
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

lemma BernsteinTerm.eval_nonneg {n : Nat} {degree : Fin n → Nat}
    {term : BernsteinTerm n} {point : Fin n → ℝ}
    (hcoeff : 0 ≤ term.coefficient)
    (hpoint : ∀ i, 0 ≤ point i ∧ point i ≤ 1) :
    0 ≤ term.eval degree point := by
  exact mul_nonneg (by exact_mod_cast hcoeff) <| Finset.prod_nonneg fun i _ =>
    bernsteinBasis_nonneg (hpoint i).1 (hpoint i).2

theorem BernsteinCertificate.sound {n : Nat}
    {certificate : BernsteinCertificate n}
    (hcheck : certificate.check = true)
    {point : Fin n → ℝ} (hpoint : ∀ i, 0 ≤ point i ∧ point i ≤ 1) :
    0 ≤ certificate.eval point := by
  have hvalid := certificate.valid_of_check hcheck
  exact List.sum_nonneg fun value hvalue => by
    simp only [List.mem_map] at hvalue
    obtain ⟨term, hterm, rfl⟩ := hvalue
    exact BernsteinTerm.eval_nonneg (hvalid term hterm).1 hpoint

theorem BernsteinCertificate.sound_for {n : Nat}
    {certificate : BernsteinCertificate n}
    (hcheck : certificate.check = true)
    {target : (Fin n → ℝ) → ℝ}
    (hidentity : ∀ point, target point = certificate.eval point)
    {point : Fin n → ℝ} (hpoint : ∀ i, 0 ≤ point i ∧ point i ≤ 1) :
    0 ≤ target point := by
  rw [hidentity]
  exact certificate.sound hcheck hpoint

end OddCycleBound.RegionII.Certificate
