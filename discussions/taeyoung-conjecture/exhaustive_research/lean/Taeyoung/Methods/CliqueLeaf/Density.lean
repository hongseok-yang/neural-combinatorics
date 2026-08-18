import Taeyoung.Methods.Link.Cone
import Taeyoung.Methods.CliqueLeaf.CliqueTangent
import Taeyoung.Methods.PureChordal.CliquePolynomialBound
import Taeyoung.Methods.RootedTriangleTree.Paw

/-!
# Cliques with common pendant leaves: the density bound

`H_{r,k}` is a `K_r` with `k` leaves attached to one fixed clique vertex.
Writing `r = s + 3`, it is the cone over `K_{s+2}` together with `k` isolated
vertices, so `Methods/Link/Cone.lean` factors its density as an average of rooted
densities and `Foundation/GraphMap.lean` discards the isolated vertices.

The bound proved here is the note's main theorem,

  `t(H_{r,k}, W) ≥ p^k · A_r(p)` whenever `p ≥ 1 - 1/(r-1)`,

assembled from four inputs, all already available:

* the clique input `A_m(z) ≤ t(K_m,V)` of the pure-chordal development;
* `cliquePoly_tangent`, the affine minorant of `A_m` through `c = 2 - 1/p`;
* `tangent_of_convex`, which extends that minorant past the threshold;
* `weighted_rootedTriangle`, which makes the correction term nonnegative.
-/

open MeasureTheory

namespace Taeyoung.Methods.CliqueLeaf

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The rooted triangle is dominated by the degree -/

/-- `τ(x) ≤ d(x)`: drop two of the three factors.  This is what makes the
degenerate set `d(x) = 0` harmless when the exponent `d^h` has `h = 0`. -/
lemma rootedTriangle_le_degree (W : Graphon Ω μ) (x : Ω) :
    rootedTriangle W x ≤ degree W x := by
  have hrowx : Measurable fun b ↦ W x b := measurable_row W.measurable x
  have huncurry : Measurable (Function.uncurry fun y z : Ω ↦ W x y * W x z * W y z) :=
    ((hrowx.comp measurable_fst).mul (hrowx.comp measurable_snd)).mul W.measurable
  have hbdd : ∀ y z : Ω, |W x y * W x z * W y z| ≤ 1 := by
    intro y z
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (W.nonneg x y) (W.nonneg x z))
      (W.nonneg y z))]
    exact mul_le_one₀
      (mul_le_one₀ (W.le_one x y) (W.nonneg x z) (W.le_one x z))
      (W.nonneg y z) (W.le_one y z)
  have hinner : ∀ y, (∫ z, W x y * W x z * W y z ∂μ) ≤ W x y := by
    intro y
    have hint : Integrable (fun z ↦ W x y * W x z * W y z) μ :=
      integrable_of_bdd ((measurable_const.mul hrowx).mul (measurable_row W.measurable y))
        (hbdd y)
    calc ∫ z, W x y * W x z * W y z ∂μ ≤ ∫ _z : Ω, W x y ∂μ := by
          refine integral_mono hint (integrable_const _) fun z ↦ ?_
          calc W x y * W x z * W y z = W x y * (W x z * W y z) := by ring
            _ ≤ W x y * 1 :=
                mul_le_mul_of_nonneg_left
                  (mul_le_one₀ (W.le_one x z) (W.nonneg y z) (W.le_one y z))
                  (W.nonneg x y)
            _ = W x y := mul_one _
      _ = W x y := by simp
  have hint2 : Integrable (fun y ↦ ∫ z, W x y * W x z * W y z ∂μ) μ :=
    integrable_integral_right huncurry hbdd
  have hdeg : Integrable (fun y ↦ W x y) μ :=
    integrable_of_bdd hrowx fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  exact integral_mono hint2 hdeg hinner

/-! ### The family, and the rooted triangle as a cone density -/

/-- `K_{s+2}` on the first `s+2` of `s+2+k` vertices, the remaining `k`
isolated. -/
def leafBase (s k : ℕ) : SimpleGraph (Fin (s + 2 + k)) :=
  (⊤ : SimpleGraph (Fin (s + 2))).map (Fin.castAdd k)

instance leafBase_decidableAdj (s k : ℕ) : DecidableRel (leafBase s k).Adj := by
  unfold leafBase
  infer_instance

/-- **The family `H_{r,k}` with `r = s + 3`.**  A `K_{s+3}` with `k` leaves
attached to the vertex `0`. -/
def cliqueLeafGraph (s k : ℕ) : SimpleGraph (Fin (s + 2 + k + 1)) :=
  coneGraph (leafBase s k)

instance cliqueLeafGraph_decidableAdj (s k : ℕ) :
    DecidableRel (cliqueLeafGraph s k).Adj :=
  coneGraph_decidableAdj (leafBase s k)

lemma homDensity_leafBase {ν : Measure Ω} [IsProbabilityMeasure ν]
    (s k : ℕ) (V : Graphon Ω ν) :
    homDensity (leafBase s k) V = cliqueDensity (s + 2) V :=
  homDensity_map_castAdd (⊤ : SimpleGraph (Fin (s + 2))) k V

lemma rooted_integrand_top_two (W : Graphon Ω μ) (a : Ω) (y : Fin 2 → Ω) :
    (∏ i, W a (y i)) * graphWeight (⊤ : SimpleGraph (Fin 2)) W y =
      W a (y 0) * W a (y 1) * W (y 0) (y 1) := by
  rw [graphWeight_top_fin_two, Fin.prod_univ_two]

/-- The rooted triangle density is the rooted density of `K₂`. -/
lemma rootedDensity_top_two (W : Graphon Ω μ) (a : Ω) :
    rootedDensity (⊤ : SimpleGraph (Fin 2)) W a = rootedTriangle W a := by
  have hm := measurable_rooted_integrand (⊤ : SimpleGraph (Fin 2)) W a
  have hb := abs_rooted_integrand_le_one (⊤ : SimpleGraph (Fin 2)) W a
  rw [rootedDensity, integral_assignmentMeasure_succ _ hm hb, rootedTriangle]
  refine integral_congr_ae (ae_of_all _ fun y₀ ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ (∏ i, W a ((Fin.cons y₀ y : Fin 2 → Ω) i)) *
      graphWeight (⊤ : SimpleGraph (Fin 2)) W (Fin.cons y₀ y))
    (hm.comp (measurable_fin_cons y₀)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun y₁ ↦ ?_)
  simp only []
  have hval : ∀ z : Fin 0 → Ω,
      (∏ i, W a ((Fin.cons y₀ (Fin.cons y₁ z) : Fin 2 → Ω) i)) *
          graphWeight (⊤ : SimpleGraph (Fin 2)) W (Fin.cons y₀ (Fin.cons y₁ z)) =
        W a y₀ * W a y₁ * W y₀ y₁ := fun z ↦
    rooted_integrand_top_two W a (Fin.cons y₀ (Fin.cons y₁ z))
  rw [integral_congr_ae (ae_of_all _ hval)]
  simp

/-! ### The clique input in the form the family needs -/

/-- The clique-density input for every clique size `m = s + 2 ≥ 2`.  For `m = 2`
it is the identity `t(K₂,V) = z`; above that it is the pure-chordal bound. -/
theorem cliqueDensity_ge_cliquePoly' {ν : Measure Ω} [IsProbabilityMeasure ν]
    (V : Graphon Ω ν) (s : ℕ) (hz : cliqueThreshold s ≤ cliqueDensity 2 V) :
    cliquePoly (s + 2) (cliqueDensity 2 V) ≤ cliqueDensity (s + 2) V := by
  cases s with
  | zero =>
      rw [show (0 : ℕ) + 2 = 1 + 1 from rfl, cliquePoly_succ, cliquePoly_one]
      norm_num
  | succ s =>
      have hr : 3 ≤ s + 1 + 2 := by omega
      have hcast : ((s + 1 + 2 - 1 : ℕ) : ℝ) = (s : ℝ) + 2 := by
        push_cast [show s + 1 + 2 - 1 = s + 2 from rfl]
        ring
      have hp : 1 - 1 / (((s + 1 + 2 - 1 : ℕ) : ℝ)) ≤ cliqueDensity 2 V := by
        rw [hcast]
        have : cliqueThreshold (s + 1) = 1 - 1 / ((s : ℝ) + 2) := by
          simp only [cliqueThreshold]
          push_cast
          ring_nf
        rw [← this]
        exact hz
      exact cliqueDensity_ge_cliquePoly V hr hp le_rfl

/-! ### The pointwise bound at a root -/

/-- **The tangent bound in the link.**  For any tangent point `c` above the
clique threshold, the affine minorant of `A_{s+2}` holds at every root. -/
theorem link_tangent (W : Graphon Ω μ) (s : ℕ) {c : ℝ}
    (hcth : cliqueThreshold s ≤ c) {a : Ω} (ha : 0 < degree W a) :
    cliquePoly (s + 2) c +
        cliquePolyDeriv (s + 2) c * (cliqueDensity 2 (linkGraphon W a) - c) ≤
      cliqueDensity (s + 2) (linkGraphon W a) := by
  haveI := isProbabilityMeasure_linkMeasure W ha
  refine tangent_of_convex (φ := cliquePoly (s + 2)) (a := cliqueThreshold s)
    (c := c) (s := cliquePolyDeriv (s + 2) c)
    (z := cliqueDensity 2 (linkGraphon W a))
    (t := cliqueDensity (s + 2) (linkGraphon W a))
    (cliquePoly_threshold s)
    (cliquePolyDeriv_nonneg (factor_nonneg s hcth))
    (fun w hw hw1 ↦ cliquePoly_tangent (factor_nonneg s hcth) (factor_nonneg s hw))
    (cliqueThreshold_le_one s)
    (cliqueDensity_le_one 2 (linkGraphon W a))
    (cliqueDensity_nonneg _ (linkGraphon W a))
    fun hle ↦ cliqueDensity_ge_cliquePoly' (linkGraphon W a) s hle

/-- **The pointwise lower bound on the rooted density.**  Valid at every root,
including where the degree vanishes. -/
theorem rootedDensity_lower (W : Graphon Ω μ) (s k : ℕ) {c : ℝ}
    (hcth : cliqueThreshold s ≤ c) (a : Ω) :
    degree W a ^ (s + 2 + k) * cliquePoly (s + 2) c +
        cliquePolyDeriv (s + 2) c *
          (degree W a ^ (s + k) * rootedTriangle W a -
            c * degree W a ^ (s + 2 + k)) ≤
      rootedDensity (leafBase s k) W a := by
  have hfac := factor_nonneg s hcth
  have hφ : 0 ≤ cliquePoly (s + 2) c := cliquePoly_nonneg hfac
  have hlam : 0 ≤ cliquePolyDeriv (s + 2) c := cliquePolyDeriv_nonneg hfac
  rcases eq_or_lt_of_le (degree_nonneg W a) with hd0 | hdpos
  · have hz : degree W a = 0 := hd0.symm
    have hτ : rootedTriangle W a = 0 :=
      le_antisymm (by rw [← hz]; exact rootedTriangle_le_degree W a)
        (rootedTriangle_nonneg W a)
    rw [hz, hτ, zero_pow (by omega : s + 2 + k ≠ 0)]
    simpa using rootedDensity_nonneg (leafBase s k) W a
  · haveI := isProbabilityMeasure_linkMeasure W hdpos
    have hsplit : degree W a ^ (s + 2 + k) = degree W a ^ (s + k) * degree W a ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have hτeq : degree W a ^ 2 * cliqueDensity 2 (linkGraphon W a) =
        rootedTriangle W a := by
      rw [← rootedDensity_top_two W a, cliqueDensity,
        rootedDensity_eq (⊤ : SimpleGraph (Fin 2)) W hdpos]
    have hcone : rootedDensity (leafBase s k) W a =
        degree W a ^ (s + 2 + k) * cliqueDensity (s + 2) (linkGraphon W a) := by
      rw [rootedDensity_eq (leafBase s k) W hdpos, homDensity_leafBase]
    have htan := link_tangent W s hcth hdpos
    have hpow : (0 : ℝ) ≤ degree W a ^ (s + 2 + k) :=
      pow_nonneg (degree_nonneg W a) _
    have hmul := mul_le_mul_of_nonneg_left htan hpow
    rw [hcone]
    have hz : degree W a ^ (s + 2 + k) * cliqueDensity 2 (linkGraphon W a) =
        degree W a ^ (s + k) * rootedTriangle W a := by
      rw [hsplit, mul_assoc, hτeq]
    nlinarith [hmul, hz]

/-! ### The tangent point and the target -/

/-- `p^{m}·A_m(2 - 1/p) = A_{m+1}(p)`: the identification that turns the bound at
the tangent point into the catalogue target. -/
lemma cliquePoly_shift (s : ℕ) {p : ℝ} (hp : 0 < p) :
    p ^ (s + 2) * cliquePoly (s + 2) (2 - 1 / p) = cliquePoly (s + 3) p := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have hrhs : cliquePoly (s + 3) p =
      ∏ a ∈ Finset.range (s + 2), (1 - ((a : ℝ) + 1) * (1 - p)) := by
    rw [show s + 3 = (s + 2) + 1 from rfl, cliquePoly,
      Finset.prod_range_succ' (fun i ↦ 1 - (i : ℝ) * (1 - p)) (s + 2)]
    push_cast
    simp
  rw [hrhs, cliquePoly, show p ^ (s + 2) = ∏ _a ∈ Finset.range (s + 2), p from by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  field_simp
  ring

/-! ### The integrated bound -/

/-- The density bound at an arbitrary tangent point `c`, given that the
correction term is nonnegative. -/
theorem cliqueLeaf_density_at (W : Graphon Ω μ) (s k : ℕ) {c : ℝ}
    (hcth : cliqueThreshold s ≤ c)
    (hcorr : c * moment W (s + 2 + k) ≤
      ∫ a, degree W a ^ (s + k) * rootedTriangle W a ∂μ) :
    moment W (s + 2 + k) * cliquePoly (s + 2) c ≤
      homDensity (cliqueLeafGraph s k) W := by
  have hfac := factor_nonneg s hcth
  have hphi : 0 ≤ cliquePoly (s + 2) c := cliquePoly_nonneg hfac
  have hlam : 0 ≤ cliquePolyDeriv (s + 2) c := cliquePolyDeriv_nonneg hfac
  have hdint : Integrable (fun a ↦ degree W a ^ (s + 2 + k)) μ :=
    integrable_of_bdd ((measurable_degree W).pow_const _) fun a ↦ by
      rw [abs_of_nonneg (pow_nonneg (degree_nonneg W a) _)]
      exact pow_le_one₀ (degree_nonneg W a) (degree_le_one W a)
  have htint : Integrable (fun a ↦ degree W a ^ (s + k) * rootedTriangle W a) μ :=
    integrable_of_bdd (((measurable_degree W).pow_const _).mul
      (measurable_rootedTriangle W)) fun a ↦ by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (degree_nonneg W a) _)
          (rootedTriangle_nonneg W a))]
        exact mul_le_one₀ (pow_le_one₀ (degree_nonneg W a) (degree_le_one W a))
          (rootedTriangle_nonneg W a) (rootedTriangle_le_one W a)
  have hg : Integrable (fun a ↦
      (cliquePoly (s + 2) c - cliquePolyDeriv (s + 2) c * c) * degree W a ^ (s + 2 + k) +
        cliquePolyDeriv (s + 2) c * (degree W a ^ (s + k) * rootedTriangle W a)) μ :=
    (hdint.const_mul _).add (htint.const_mul _)
  have hmono : ∫ a, ((cliquePoly (s + 2) c - cliquePolyDeriv (s + 2) c * c) *
        degree W a ^ (s + 2 + k) +
        cliquePolyDeriv (s + 2) c *
          (degree W a ^ (s + k) * rootedTriangle W a)) ∂μ ≤
      ∫ a, rootedDensity (leafBase s k) W a ∂μ := by
    refine integral_mono hg (integrable_rootedDensity _ W) fun a ↦ ?_
    have hb := rootedDensity_lower W s k hcth a
    have heq : (cliquePoly (s + 2) c - cliquePolyDeriv (s + 2) c * c) *
          degree W a ^ (s + 2 + k) +
          cliquePolyDeriv (s + 2) c *
            (degree W a ^ (s + k) * rootedTriangle W a) =
        degree W a ^ (s + 2 + k) * cliquePoly (s + 2) c +
          cliquePolyDeriv (s + 2) c *
            (degree W a ^ (s + k) * rootedTriangle W a -
              c * degree W a ^ (s + 2 + k)) := by ring
    rw [heq]
    exact hb
  have hcone : homDensity (cliqueLeafGraph s k) W =
      ∫ a, rootedDensity (leafBase s k) W a ∂μ :=
    homDensity_coneGraph (leafBase s k) W
  rw [hcone]
  refine le_trans ?_ hmono
  rw [integral_add (hdint.const_mul _) (htint.const_mul _), integral_const_mul,
    integral_const_mul, ← moment]
  have hstep := mul_le_mul_of_nonneg_left hcorr hlam
  linarith

/-! ### The main theorem -/

/-- **Cliques with common pendant leaves.**  With `r = s + 3`, every graphon of
edge density `p ≥ 1 - 1/(r-1)` satisfies `t(H_{r,k},W) ≥ p^k·A_r(p)`. -/
theorem cliqueLeaf_density (W : Graphon Ω μ) (s k : ℕ)
    (hp : 1 - 1 / ((s : ℝ) + 2) ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ k * cliquePoly (s + 3) (cliqueDensity 2 W) ≤
      homDensity (cliqueLeafGraph s k) W := by
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
  have hscast : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hhalf : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have hle : 1 / ((s : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · norm_num
      · linarith
    linarith
  have hppos : (0 : ℝ) < cliqueDensity 2 W := by linarith
  have hp1 : cliqueDensity 2 W ≤ 1 := cliqueDensity_le_one 2 W
  have hinv : 1 / cliqueDensity 2 W ≤ 1 + 1 / ((s : ℝ) + 1) := by
    have hX : (0 : ℝ) < 1 + 1 / ((s : ℝ) + 1) := by positivity
    have hprod : (1 + 1 / ((s : ℝ) + 1)) * (1 - 1 / ((s : ℝ) + 2)) = 1 := by
      field_simp
      ring
    have h1 : (1 : ℝ) ≤ (1 + 1 / ((s : ℝ) + 1)) * cliqueDensity 2 W :=
      calc (1 : ℝ) = (1 + 1 / ((s : ℝ) + 1)) * (1 - 1 / ((s : ℝ) + 2)) := hprod.symm
        _ ≤ (1 + 1 / ((s : ℝ) + 1)) * cliqueDensity 2 W :=
            mul_le_mul_of_nonneg_left hp hX.le
    rw [div_le_iff₀ hppos]
    linarith
  have hcth : cliqueThreshold s ≤ 2 - 1 / cliqueDensity 2 W := by
    simp only [cliqueThreshold]
    linarith
  have hcorr : (2 - 1 / cliqueDensity 2 W) * moment W (s + 2 + k) ≤
      ∫ a, degree W a ^ (s + k) * rootedTriangle W a ∂μ := by
    have hwrt := weighted_rootedTriangle (W := W) (s + k)
    rw [show s + k + 2 = s + 2 + k by omega] at hwrt
    rw [show (2 : ℝ) - 1 / cliqueDensity 2 W =
      (2 * cliqueDensity 2 W - 1) / cliqueDensity 2 W by field_simp,
      div_mul_eq_mul_div, div_le_iff₀ hppos]
    nlinarith [hwrt]
  have hmain := cliqueLeaf_density_at W s k hcth hcorr
  have hmom : cliqueDensity 2 W ^ (s + 2 + k) ≤ moment W (s + 2 + k) :=
    RootedTriangleTree.pow_le_moment W _
  have hphi : 0 ≤ cliquePoly (s + 2) (2 - 1 / cliqueDensity 2 W) :=
    cliquePoly_nonneg (factor_nonneg s hcth)
  refine le_trans ?_ hmain
  have hjensen : cliqueDensity 2 W ^ (s + 2 + k) *
      cliquePoly (s + 2) (2 - 1 / cliqueDensity 2 W) ≤
      moment W (s + 2 + k) * cliquePoly (s + 2) (2 - 1 / cliqueDensity 2 W) :=
    mul_le_mul_of_nonneg_right hmom hphi
  refine le_trans (le_of_eq ?_) hjensen
  rw [show s + 2 + k = k + (s + 2) by omega, pow_add, mul_assoc,
    cliquePoly_shift s hppos]

end Taeyoung.Methods.CliqueLeaf
