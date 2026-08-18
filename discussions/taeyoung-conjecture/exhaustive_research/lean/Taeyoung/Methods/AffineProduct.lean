import Taeyoung.Foundation.ChromaticTarget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Targets that are products of affine factors

Every catalogue target met so far has the shape

```
Φ_F(z) = ∏_{i} (1 - k_i (1 - z)),
```

with `k_i` running over the roots of `χ_F` with multiplicity.  That is not a
coincidence: if `χ_F(x) = ∏_{i=1}^{v(F)} (x - k_i)` then, writing `q = 1 - z`,

```
Φ_F(z) = q^{v(F)} ∏_i (1/q - k_i) = ∏_i (1 - k_i q),
```

one factor of `q` per root.  This file develops that presentation once.

Three facts are needed downstream, and each is an induction over the root list.

* `affineProd_tangent` — the affine minorant through any point `c` where all
  factors are nonnegative.  This is `cliquePoly_tangent` with the arithmetic
  progression `0,1,…,s-1` replaced by an arbitrary list, proved the same way:
  by the product rule and one completed square per factor, with no derivative
  and no `ConvexOn`.
* `pow_mul_affineProd_shift` — the cone identity.  It is a *per factor*
  identity, `p·(1 - k(1 - (2 - 1/p))) = 1 - (k+1)(1-p)`, so coning shifts every
  root by one and absorbs exactly one power of `p` per root.  Together with
  `χ_{K₁∨F}(x) = x·χ_F(x-1)` this is why the cone bound `p^{v(F)}·Φ_F(2 - 1/p)`
  *is* the cone's catalogue target rather than merely bounding it.
* `chromaticTarget_affineProd` — the identification of the target itself.
-/

open Polynomial

namespace Taeyoung.Methods

/-! ### The product and its formal derivative -/

/-- `∏_{k ∈ ks} (1 - k(1 - z))`. -/
def affineProd : List ℝ → ℝ → ℝ
  | [], _ => 1
  | k :: ks, z => affineProd ks z * (1 - k * (1 - z))

/-- The product-rule derivative of `affineProd`, defined as a recursion. -/
def affineProdDeriv : List ℝ → ℝ → ℝ
  | [], _ => 0
  | k :: ks, z => affineProdDeriv ks z * (1 - k * (1 - z)) + k * affineProd ks z

@[simp] lemma affineProd_nil (z : ℝ) : affineProd [] z = 1 := rfl

lemma affineProd_cons (k : ℝ) (ks : List ℝ) (z : ℝ) :
    affineProd (k :: ks) z = affineProd ks z * (1 - k * (1 - z)) := rfl

@[simp] lemma affineProdDeriv_nil (z : ℝ) : affineProdDeriv [] z = 0 := rfl

lemma affineProdDeriv_cons (k : ℝ) (ks : List ℝ) (z : ℝ) :
    affineProdDeriv (k :: ks) z =
      affineProdDeriv ks z * (1 - k * (1 - z)) + k * affineProd ks z := rfl

@[simp] lemma affineProd_at_one (ks : List ℝ) : affineProd ks 1 = 1 := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [affineProd_cons, ih]

lemma affineProd_append (l₁ l₂ : List ℝ) (z : ℝ) :
    affineProd (l₁ ++ l₂) z = affineProd l₁ z * affineProd l₂ z := by
  induction l₁ with
  | nil => simp
  | cons k l ih =>
      rw [List.cons_append, affineProd_cons, affineProd_cons, ih]
      ring

@[simp] lemma affineProd_replicate_zero (c : ℕ) (z : ℝ) :
    affineProd (List.replicate c 0) z = 1 := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, affineProd_cons, ih]; ring

@[simp] lemma affineProd_replicate_one (e : ℕ) (z : ℝ) :
    affineProd (List.replicate e 1) z = z ^ e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [List.replicate_succ, affineProd_cons, ih, pow_succ]; ring

/-- The root list of a forest with `c` components and `e` edges: `χ_F(x) =
x^c(x-1)^e`, so the affine product is `z^e`, its Sidorenko bound. -/
lemma affineProd_forestRoots (c e : ℕ) (z : ℝ) :
    affineProd (List.replicate c (0 : ℝ) ++ List.replicate e 1) z = z ^ e := by
  rw [affineProd_append, affineProd_replicate_zero, affineProd_replicate_one,
    one_mul]

/-! ### Nonnegativity -/

lemma affineProd_nonneg {ks : List ℝ} {z : ℝ}
    (h : ∀ k ∈ ks, 0 ≤ 1 - k * (1 - z)) : 0 ≤ affineProd ks z := by
  induction ks with
  | nil => norm_num
  | cons k ks ih =>
      exact mul_nonneg (ih fun a ha ↦ h a (List.mem_cons_of_mem _ ha))
        (h k (List.mem_cons_self ..))

lemma affineProdDeriv_nonneg {ks : List ℝ} {z : ℝ} (hk : ∀ k ∈ ks, 0 ≤ k)
    (h : ∀ k ∈ ks, 0 ≤ 1 - k * (1 - z)) : 0 ≤ affineProdDeriv ks z := by
  induction ks with
  | nil => norm_num
  | cons k ks ih =>
      have hk' : ∀ a ∈ ks, 0 ≤ a := fun a ha ↦ hk a (List.mem_cons_of_mem _ ha)
      have h' : ∀ a ∈ ks, 0 ≤ 1 - a * (1 - z) := fun a ha ↦
        h a (List.mem_cons_of_mem _ ha)
      rw [affineProdDeriv_cons]
      exact add_nonneg (mul_nonneg (ih hk' h') (h k (List.mem_cons_self ..)))
        (mul_nonneg (hk k (List.mem_cons_self ..)) (affineProd_nonneg h'))

/-! ### The affine minorant -/

/-- **A tangent line under `affineProd`.**  Wherever every factor is
nonnegative at both `c` and `w`, the line through `(c, φ(c))` of slope
`φ'(c)` lies under `φ`. -/
theorem affineProd_tangent {ks : List ℝ} {c w : ℝ} (hk : ∀ k ∈ ks, 0 ≤ k)
    (hc : ∀ k ∈ ks, 0 ≤ 1 - k * (1 - c))
    (hw : ∀ k ∈ ks, 0 ≤ 1 - k * (1 - w)) :
    affineProd ks c + affineProdDeriv ks c * (w - c) ≤ affineProd ks w := by
  induction ks with
  | nil => norm_num
  | cons k ks ih =>
      have hk' : ∀ a ∈ ks, 0 ≤ a := fun a ha ↦ hk a (List.mem_cons_of_mem _ ha)
      have hc' : ∀ a ∈ ks, 0 ≤ 1 - a * (1 - c) := fun a ha ↦
        hc a (List.mem_cons_of_mem _ ha)
      have hw' : ∀ a ∈ ks, 0 ≤ 1 - a * (1 - w) := fun a ha ↦
        hw a (List.mem_cons_of_mem _ ha)
      have hIH := ih hk' hc' hw'
      have hP : 0 ≤ affineProd ks c := affineProd_nonneg hc'
      have hPw : 0 ≤ affineProd ks w := affineProd_nonneg hw'
      have hD : 0 ≤ affineProdDeriv ks c := affineProdDeriv_nonneg hk' hc'
      have hL : 0 ≤ 1 - k * (1 - c) := hc k (List.mem_cons_self ..)
      have hLw : 0 ≤ 1 - k * (1 - w) := hw k (List.mem_cons_self ..)
      have hk0 : 0 ≤ k := hk k (List.mem_cons_self ..)
      rw [affineProd_cons, affineProd_cons, affineProdDeriv_cons]
      set P := affineProd ks c
      set Pw := affineProd ks w
      set D := affineProdDeriv ks c
      set t := w - c with htdef
      have hfac : 1 - k * (1 - w) = (1 - k * (1 - c)) + k * t := by
        rw [htdef]; ring
      rcases le_or_gt 0 (P + D * t) with hcase | hcase
      · have hmul : (P + D * t) * (1 - k * (1 - w)) ≤ Pw * (1 - k * (1 - w)) :=
          mul_le_mul_of_nonneg_right hIH hLw
        rw [hfac] at hmul ⊢
        nlinarith [mul_nonneg (mul_nonneg hD hk0) (sq_nonneg t)]
      · have htneg : t < 0 := by
          by_contra hcon
          simp only [not_lt] at hcon
          nlinarith [mul_nonneg hD hcon]
        have h1 : (1 - k * (1 - c)) * (P + D * t) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hL hcase.le
        have h2 : k * P * t ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk0 hP) htneg.le
        have h3 : 0 ≤ Pw * (1 - k * (1 - w)) := mul_nonneg hPw hLw
        nlinarith

/-! ### The threshold -/

/-- Above `1 - 1/kmax`, every factor with slope at most `kmax` is nonnegative. -/
lemma affineProd_factor_nonneg {ks : List ℝ} {kmax z : ℝ} (hkmax : 0 < kmax)
    (hk : ∀ k ∈ ks, 0 ≤ k) (hle : ∀ k ∈ ks, k ≤ kmax) (hz : 1 - 1 / kmax ≤ z) :
    ∀ k ∈ ks, 0 ≤ 1 - k * (1 - z) := by
  intro k hkm
  rcases le_or_gt (1 - z) 0 with h | h
  · nlinarith [hk k hkm]
  · have hle' : 1 - z ≤ 1 / kmax := by linarith
    have hmul : k * (1 - z) ≤ kmax * (1 / kmax) :=
      mul_le_mul (hle k hkm) hle' h.le hkmax.le
    rw [mul_one_div, div_self (ne_of_gt hkmax)] at hmul
    linarith

/-- The product vanishes at the threshold of its largest slope. -/
lemma affineProd_threshold {ks : List ℝ} {kmax : ℝ} (hkmax : 0 < kmax)
    (hmem : kmax ∈ ks) : affineProd ks (1 - 1 / kmax) = 0 := by
  have hne : kmax ≠ 0 := ne_of_gt hkmax
  induction ks with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons k ks ih =>
      rw [affineProd_cons]
      rcases List.mem_cons.mp hmem with heq | hks
      · have hz : 1 - kmax * (1 - (1 - 1 / kmax)) = 0 := by field_simp; ring
        rw [← heq, hz, mul_zero]
      · rw [ih hks, zero_mul]

/-! ### Coning shifts every root by one -/

/-- **The cone identity.**  `p^{|ks|}·φ(2 - 1/p)` is the product with every
slope increased by one, evaluated at `p`. -/
lemma pow_mul_affineProd_shift (ks : List ℝ) {p : ℝ} (hp : p ≠ 0) :
    p ^ ks.length * affineProd ks (2 - 1 / p) =
      affineProd (ks.map (· + 1)) p := by
  induction ks with
  | nil => norm_num
  | cons k ks ih =>
      have hfac : p * (1 - k * (1 - (2 - 1 / p))) = 1 - (k + 1) * (1 - p) := by
        field_simp
        ring
      rw [List.length_cons, List.map_cons, affineProd_cons, affineProd_cons,
        pow_succ]
      calc p ^ ks.length * p * (affineProd ks (2 - 1 / p) * (1 - k * (1 - (2 - 1 / p))))
          = (p ^ ks.length * affineProd ks (2 - 1 / p)) *
              (p * (1 - k * (1 - (2 - 1 / p)))) := by ring
        _ = affineProd (ks.map (· + 1)) p * (1 - (k + 1) * (1 - p)) := by
              rw [ih, hfac]

/-! ### The target of a split chromatic polynomial -/

lemma eval_affine_roots (ks : List ℝ) {p : ℝ} (hp : p ≠ 1) :
    (1 - p) ^ ks.length *
        Polynomial.eval (1 / (1 - p)) ((ks.map fun k ↦ (X : ℝ[X]) - C k).prod) =
      affineProd ks p := by
  have hq : (1 : ℝ) - p ≠ 0 := fun h ↦ hp (by linarith)
  induction ks with
  | nil => norm_num
  | cons k ks ih =>
      have hfac : (1 - p) * (1 / (1 - p) - k) = 1 - k * (1 - p) := by
        field_simp
      rw [List.length_cons, List.map_cons, List.prod_cons, eval_mul, eval_sub,
        eval_X, eval_C, affineProd_cons, pow_succ]
      calc (1 - p) ^ ks.length * (1 - p) *
            ((1 / (1 - p) - k) *
              Polynomial.eval (1 / (1 - p)) ((ks.map fun k ↦ (X : ℝ[X]) - C k).prod))
          = ((1 - p) ^ ks.length *
              Polynomial.eval (1 / (1 - p))
                ((ks.map fun k ↦ (X : ℝ[X]) - C k).prod)) *
              ((1 - p) * (1 / (1 - p) - k)) := by ring
        _ = affineProd ks p * (1 - k * (1 - p)) := by rw [ih, hfac]

/-- **The catalogue target of a chromatic polynomial split into linear
factors** is the affine product over its roots. -/
lemma chromaticTarget_affineProd {n : ℕ} (ks : List ℝ) (hlen : ks.length = n)
    {p : ℝ} (hp : p ≠ 1) :
    Taeyoung.chromaticTarget (V := Fin n)
        ((ks.map fun k ↦ (X : ℝ[X]) - C k).prod) p = affineProd ks p := by
  rw [Taeyoung.chromaticTarget_of_ne_one _ hp, Fintype.card_fin, ← hlen]
  exact eval_affine_roots ks hp

end Taeyoung.Methods
