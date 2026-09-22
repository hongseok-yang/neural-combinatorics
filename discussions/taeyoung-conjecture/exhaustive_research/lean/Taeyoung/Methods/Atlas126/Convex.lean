import Taeyoung.Methods.Atlas126.Coefficients
import Mathlib.Tactic.FieldSimp

/-!
# Atlas 126: convex reduction in the rooted path variable

For fixed `(p,d,t)`, the cleared scalar residual is a convex quadratic in `a`.
This file records the exact vertex and the two monotonicity statements used to
reduce an arbitrary feasible point to the three boundary faces or the interior
critical point.  It deliberately contains no generated certificate data.
-/

namespace Taeyoung.Methods.Atlas126

/-- The scalar proposition independently of the graphon and coloring-count
development in `Rows`. It is definitionally equal to `Rows`' `ScalarPlane`;
arithmetic certificate files need only this small import closure. -/
def PolynomialPlane (p C beta gamma lam g : ℝ) : Prop :=
  ∀ d a t : ℝ, 0 ≤ d → d ≤ 1 → 0 ≤ a → d + p - 1 ≤ a → a ≤ d →
    0 ≤ t → 2*a-p ≤ t → t ≤ a → t ≤ d^2 →
    d*(1-d)*(C + beta*(d-p) + gamma*(a-d^2) + lam*(t-g)) ≤
      (1-d)*t^3 + d*t*(a-t)^2

/-- The right side minus the left side of the polynomial plane. -/
noncomputable def scalarResidual
    (p C beta gamma lam g d a t : ℝ) : ℝ :=
  (1 - d) * t ^ 3 + d * t * (a - t) ^ 2 -
    d * (1 - d) *
      (C + beta * (d - p) + gamma * (a - d ^ 2) + lam * (t - g))

lemma scalarPlane_iff_residual
    (p C beta gamma lam g : ℝ) :
    PolynomialPlane p C beta gamma lam g ↔
      ∀ d a t : ℝ,
        0 ≤ d → d ≤ 1 →
        0 ≤ a → d + p - 1 ≤ a → a ≤ d →
        0 ≤ t → 2 * a - p ≤ t → t ≤ a → t ≤ d ^ 2 →
        0 ≤ scalarResidual p C beta gamma lam g d a t := by
  simp only [PolynomialPlane, scalarResidual]
  constructor <;> intro h d a t hd0 hd1 ha0 haL haD ht0 htL htA htD
  · have := h d a t hd0 hd1 ha0 haL haD ht0 htL htA htD
    linarith
  · have := h d a t hd0 hd1 ha0 haL haD ht0 htL htA htD
    linarith

/-- The unconstrained minimizer of the residual as a function of `a`. -/
noncomputable def scalarVertex (gamma d t : ℝ) : ℝ :=
  t + gamma * (1 - d) / (2 * t)

/-- Completing the square in `a`. -/
theorem scalarResidual_vertex_identity
    (p C beta gamma lam g d a t : ℝ) (ht : t ≠ 0) :
    scalarResidual p C beta gamma lam g d a t =
      scalarResidual p C beta gamma lam g d (scalarVertex gamma d t) t +
        d * t * (a - scalarVertex gamma d t) ^ 2 := by
  simp only [scalarResidual, scalarVertex]
  field_simp
  ring

/-- To the right of the vertex, the residual is monotone. -/
theorem scalarResidual_mono_right
    (p C beta gamma lam g d t a b : ℝ)
    (hd : 0 ≤ d) (ht : 0 < t)
    (hvertex : scalarVertex gamma d t ≤ b) (hba : b ≤ a) :
    scalarResidual p C beta gamma lam g d b t ≤
      scalarResidual p C beta gamma lam g d a t := by
  have hsq : (b - scalarVertex gamma d t) ^ 2 ≤
      (a - scalarVertex gamma d t) ^ 2 := by nlinarith
  have hdt : 0 ≤ d * t := mul_nonneg hd ht.le
  have hmul := mul_le_mul_of_nonneg_left hsq hdt
  rw [scalarResidual_vertex_identity p C beta gamma lam g d a t ht.ne',
    scalarResidual_vertex_identity p C beta gamma lam g d b t ht.ne']
  linarith

/-- To the left of the vertex, moving farther left increases the residual. -/
theorem scalarResidual_mono_left
    (p C beta gamma lam g d t a b : ℝ)
    (hd : 0 ≤ d) (ht : 0 < t)
    (hab : a ≤ b) (hvertex : b ≤ scalarVertex gamma d t) :
    scalarResidual p C beta gamma lam g d b t ≤
      scalarResidual p C beta gamma lam g d a t := by
  have hsq : (b - scalarVertex gamma d t) ^ 2 ≤
      (a - scalarVertex gamma d t) ^ 2 := by nlinarith
  have hdt : 0 ≤ d * t := mul_nonneg hd ht.le
  have hmul := mul_le_mul_of_nonneg_left hsq hdt
  rw [scalarResidual_vertex_identity p C beta gamma lam g d a t ht.ne',
    scalarResidual_vertex_identity p C beta gamma lam g d b t ht.ne']
  linarith

/-- With `γ ≥ 0`, the vertex never lies below the elementary face `a=t`. -/
theorem le_scalarVertex {gamma d t : ℝ}
    (hgamma : 0 ≤ gamma) (hd : d ≤ 1) (ht : 0 < t) :
    t ≤ scalarVertex gamma d t := by
  have hnum : 0 ≤ gamma * (1 - d) := mul_nonneg hgamma (by linarith)
  have hden : 0 < 2 * t := by positivity
  simp only [scalarVertex]
  have := div_nonneg hnum hden.le
  linarith

/-- The abstract four-candidate reduction.  The three boundary hypotheses are
only requested when the vertex lies beyond that boundary; the interior
hypothesis is requested exactly when the vertex is feasible. -/
theorem scalarResidual_nonneg_of_candidates
    (p C beta gamma lam g d a t : ℝ)
    (hd0 : 0 ≤ d) (ht : 0 < t)
    (haLower : d + p - 1 ≤ a) (haD : a ≤ d)
    (haUpper : 2 * a - p ≤ t)
    (hLower : scalarVertex gamma d t < d + p - 1 →
      0 ≤ scalarResidual p C beta gamma lam g d (d + p - 1) t)
    (hD : d < scalarVertex gamma d t →
      0 ≤ scalarResidual p C beta gamma lam g d d t)
    (hUpper : (t + p) / 2 < scalarVertex gamma d t →
      0 ≤ scalarResidual p C beta gamma lam g d ((t + p) / 2) t)
    (hInterior : d + p - 1 ≤ scalarVertex gamma d t →
      scalarVertex gamma d t ≤ d →
      scalarVertex gamma d t ≤ (t + p) / 2 →
      0 ≤ scalarResidual p C beta gamma lam g d
        (scalarVertex gamma d t) t) :
    0 ≤ scalarResidual p C beta gamma lam g d a t := by
  have haT : a ≤ (t + p) / 2 := by linarith
  by_cases hvLower : d + p - 1 ≤ scalarVertex gamma d t
  · by_cases hvD : scalarVertex gamma d t ≤ d
    · by_cases hvUpper : scalarVertex gamma d t ≤ (t + p) / 2
      · have hmin := hInterior hvLower hvD hvUpper
        rw [scalarResidual_vertex_identity p C beta gamma lam g d a t ht.ne']
        have hterm : 0 ≤ d * t * (a - scalarVertex gamma d t) ^ 2 := by
          positivity
        linarith
      · have hstrict : (t + p) / 2 < scalarVertex gamma d t :=
          lt_of_not_ge hvUpper
        have hface := hUpper hstrict
        exact le_trans hface (scalarResidual_mono_left
          p C beta gamma lam g d t a ((t + p) / 2)
          hd0 ht haT hstrict.le)
    · have hstrict : d < scalarVertex gamma d t := lt_of_not_ge hvD
      have hface := hD hstrict
      exact le_trans hface (scalarResidual_mono_left
        p C beta gamma lam g d t a d hd0 ht haD hstrict.le)
  · have hstrict : scalarVertex gamma d t < d + p - 1 :=
      lt_of_not_ge hvLower
    have hface := hLower hstrict
    exact le_trans hface (scalarResidual_mono_right
      p C beta gamma lam g d t a (d + p - 1)
      hd0 ht hstrict.le haLower)

/-- The same minimization with feasibility retained on every boundary. This
interface matches the generated conditional Bernstein certificates: the chosen
upper face is the smaller of `d` and `(t+p)/2`, and the lower face is only used
when it lies above `t`. -/
theorem scalarResidual_nonneg_of_feasible_candidates
    (p C beta gamma lam g d a t : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht : 0 < t) (hgamma : 0 ≤ gamma)
    (haLower : d + p - 1 ≤ a) (haD : a ≤ d)
    (haUpper : 2 * a - p ≤ t) (htA : t ≤ a)
    (hLower : t ≤ d + p - 1 → d + p - 1 ≤ d →
      d + p - 1 ≤ (t + p) / 2 →
      scalarVertex gamma d t ≤ d + p - 1 →
      0 ≤ scalarResidual p C beta gamma lam g d (d + p - 1) t)
    (hD : d ≤ (t + p) / 2 → d ≤ scalarVertex gamma d t →
      0 ≤ scalarResidual p C beta gamma lam g d d t)
    (hUpper : (t + p) / 2 ≤ d → d + p - 1 ≤ (t + p) / 2 →
      (t + p) / 2 ≤ scalarVertex gamma d t →
      0 ≤ scalarResidual p C beta gamma lam g d ((t + p) / 2) t)
    (hInterior : d + p - 1 ≤ scalarVertex gamma d t →
      scalarVertex gamma d t ≤ d →
      scalarVertex gamma d t ≤ (t + p) / 2 →
      0 ≤ scalarResidual p C beta gamma lam g d (scalarVertex gamma d t) t) :
    0 ≤ scalarResidual p C beta gamma lam g d a t := by
  have haT : a ≤ (t + p) / 2 := by linarith
  have htv := le_scalarVertex hgamma hd1 ht
  by_cases hvL : d + p - 1 ≤ scalarVertex gamma d t
  · rcases le_total d ((t + p) / 2) with hdT | hTd
    · by_cases hvD : scalarVertex gamma d t ≤ d
      · have hmin := hInterior hvL hvD (hvD.trans hdT)
        rw [scalarResidual_vertex_identity p C beta gamma lam g d a t ht.ne']
        exact add_nonneg hmin (by positivity)
      · exact (hD hdT (le_of_not_ge hvD)).trans (scalarResidual_mono_left
          p C beta gamma lam g d t a d hd0 ht haD (le_of_not_ge hvD))
    · by_cases hvT : scalarVertex gamma d t ≤ (t + p) / 2
      · have hmin := hInterior hvL (hvT.trans hTd) hvT
        rw [scalarResidual_vertex_identity p C beta gamma lam g d a t ht.ne']
        exact add_nonneg hmin (by positivity)
      · exact (hUpper hTd (haLower.trans haT) (le_of_not_ge hvT)).trans
          (scalarResidual_mono_left p C beta gamma lam g d t a ((t + p) / 2)
            hd0 ht haT (le_of_not_ge hvT))
  · have hv : scalarVertex gamma d t ≤ d + p - 1 := le_of_not_ge hvL
    exact (hLower (htv.trans hv) (haLower.trans haD) (haLower.trans haT) hv).trans
      (scalarResidual_mono_right p C beta gamma lam g d t a (d + p - 1)
        hd0 ht hv haLower)

/-- A coarser estimate that is sufficient near degree one for the three
low-density planes. Its certificate has only the density and degree variables.
Feasibility gives `a,t ≤ p` and `p-2+2*d ≤ t`; the second rooted square can
then be discarded. -/
theorem scalarResidual_nonneg_of_high_degree
    (p C beta gamma lam g d a t : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hgamma : 0 ≤ gamma) (hlam : 0 ≤ lam)
    (haLower : d + p - 1 ≤ a) (htLower : 2 * a - p ≤ t) (htA : t ≤ a)
    (hlower : 0 ≤ p - 2 + 2*d)
    (hcert : d * (C + beta * (d-p) + gamma * (p-d^2) + lam * (p-g)) ≤
      (p - 2 + 2*d)^3) :
    0 ≤ scalarResidual p C beta gamma lam g d a t := by
  have hap : a ≤ p := by linarith
  have htp : t ≤ p := htA.trans hap
  have hlowt : p - 2 + 2*d ≤ t := by linarith
  have ht0 : 0 ≤ t := hlower.trans hlowt
  have hcube : (p - 2 + 2*d)^3 ≤ t^3 := pow_le_pow_left₀ hlower hlowt 3
  have hu : C + beta * (d-p) + gamma * (a-d^2) + lam * (t-g) ≤
      C + beta * (d-p) + gamma * (p-d^2) + lam * (p-g) := by
    nlinarith [mul_nonneg hgamma (sub_nonneg.mpr hap),
      mul_nonneg hlam (sub_nonneg.mpr htp)]
  have he : 0 ≤ 1-d := by linarith
  have hbound : d*(1-d)*(C + beta*(d-p) + gamma*(a-d^2) + lam*(t-g)) ≤
      (1-d)*t^3 + d*t*(a-t)^2 := calc
    _ ≤ d*(1-d)*(C + beta*(d-p) + gamma*(p-d^2) + lam*(p-g)) :=
      mul_le_mul_of_nonneg_left hu (mul_nonneg hd0 he)
    _ = (1-d)*(d*(C + beta*(d-p) + gamma*(p-d^2) + lam*(p-g))) := by ring
    _ ≤ (1-d)*(p-2+2*d)^3 := mul_le_mul_of_nonneg_left hcert he
    _ ≤ (1-d)*t^3 := mul_le_mul_of_nonneg_left hcube he
    _ ≤ (1-d)*t^3 + d*t*(a-t)^2 := le_add_of_nonneg_right (by positivity)
  exact sub_nonneg.mpr hbound

end Taeyoung.Methods.Atlas126
