import Taeyoung.Methods.Link.PageOp
import Taeyoung.Methods.RootedTriangleTree.Paw
import Taeyoung.Methods.Peeling
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 115: the two-fold edge self-amalgam of the paw

`notes/self_amalgam.tex` at `N = 2`, `F` the paw, and the distinguished edge the
triangle edge opposite the leaf-bearing vertex.  Gluing two paws along that edge
gives Atlas 115.

The note's Lemma 2.2 conditions on the images `x,y` of the two glued roots and
writes the rooted factor

```
g(x,y) = ∫ W(x,z)W(y,z)d(z) dμ(z),
```

the paw density with its distinguished edge deleted.  **That object is already
in the project**: it is `Link.pageOp W 1`, built for the page-rooted book-leaf
family, and the two identities the note needs are its existing lemmas.  So the
whole row is

```
t(paw,W)   = ∫∫ W(x,y)·g(x,y)          (Link.integral_edge_pageOp at s = 1)
t(A₁₁₅,W)  = ∫∫ W(x,y)·g(x,y)²         (one six-coordinate peeling)
t(paw,W)²  ≤ p·t(A₁₁₅,W)               (Cauchy–Schwarz in the measure W dμ²)
t(paw,W)   ≥ p²(2p-1)                  (RootedTriangleTree.rootedTree_bound)
```

and `(p²(2p-1))²/p = p³(2p-1)² = Φ`.

**The route differs from the note in two ways.**  The note proves a general
`N`-fold amalgamation inequality by Jensen against the probability measure
`dρ = W dμ²/p`, and a general chromatic-polynomial identity
`χ_{B_N}(x) = χ_F(x)^N/(x(x-1))^{N-1}`; neither is formalized.  At `N = 2`
Jensen against `ρ` *is* Cauchy–Schwarz, so the project's own
`PureChordal.integral_mul_sq_le_integral_mul_integral_mul_sq` applies directly
to the unnormalised weight `W`, and no probability measure `ρ` is constructed —
which also removes the note's hypothesis `p > 0` from the analytic step.  The
chromatic polynomial is obtained the way every other row obtains it, from an
`attachVertex` tower, not from the amalgamation identity.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.SelfAmalgam

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.RootedTriangleTree
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.PawCone

-- `paw_factorization` is stated for `Ω : Type`, and `SatisfiesLowerBound`
-- quantifies over `Ω : Type` too, so there is nothing to gain from `Type*`.
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The glued edge, and the two integrals over it -/

section Edge

variable (W : Graphon Ω μ)

lemma measurable_edgeProd : Measurable fun q : Ω × Ω ↦ W q.1 q.2 := W.measurable

lemma integrable_edgeProd : Integrable (fun q : Ω × Ω ↦ W q.1 q.2) (μ.prod μ) := by
  refine integrable_prod_of_bdd W.measurable (C := 1) fun q ↦ ?_
  rw [abs_of_nonneg (W.nonneg q.1 q.2)]
  exact W.le_one q.1 q.2

/-- The edge density, as an integral over the product. -/
lemma integral_edgeProd :
    (∫ q, W q.1 q.2 ∂(μ.prod μ)) = cliqueDensity 2 W := by
  rw [← integral_integral (f := fun a b ↦ W a b) (integrable_edgeProd W),
    ← integral_degree W]
  rfl

private lemma meas_page : Measurable fun q : Ω × Ω ↦ pageOp W 1 q.1 q.2 :=
  measurable_pageOp W (by norm_num)

private lemma bdd_page (q : Ω × Ω) : |pageOp W 1 q.1 q.2| ≤ 1 := by
  rw [abs_of_nonneg (pageOp_nonneg W (by norm_num) q.1 q.2)]
  exact pageOp_le_one W (by norm_num) q.1 q.2

lemma integrable_edge_page : Integrable
    (fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W 1 q.1 q.2) (μ.prod μ) := by
  refine integrable_prod_of_bdd (W.measurable.mul (meas_page W)) (C := 1) fun q ↦ ?_
  rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _)
    (pageOp_nonneg W (by norm_num) _ _))]
  exact mul_le_one₀ (W.le_one _ _) (pageOp_nonneg W (by norm_num) _ _)
    (pageOp_le_one W (by norm_num) _ _)

lemma integrable_edge_page_sq : Integrable
    (fun q : Ω × Ω ↦ W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2) (μ.prod μ) := by
  refine integrable_prod_of_bdd (W.measurable.mul ((meas_page W).pow_const 2))
    (C := 1) fun q ↦ ?_
  have h0 : 0 ≤ pageOp W 1 q.1 q.2 ^ 2 :=
    pow_nonneg (pageOp_nonneg W (by norm_num) _ _) 2
  rw [abs_of_nonneg (mul_nonneg (W.nonneg _ _) h0)]
  exact mul_le_one₀ (W.le_one _ _) h0
    (pow_le_one₀ (pageOp_nonneg W (by norm_num) _ _)
      (pageOp_le_one W (by norm_num) _ _))

/-- **Cauchy–Schwarz in the weight `W dμ²`.**  This is the note's Jensen step at
`N = 2`, applied to the unnormalised weight, so no probability measure `ρ` and
no hypothesis `p > 0` are needed. -/
theorem sq_edge_page_le :
    (∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ)) ^ 2 ≤
      cliqueDensity 2 W * ∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2 ∂(μ.prod μ) := by
  have h := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ.prod μ) (A := fun q : Ω × Ω ↦ W q.1 q.2)
    (η := fun q : Ω × Ω ↦ pageOp W 1 q.1 q.2)
    (integrable_edgeProd W) (integrable_edge_page W) (integrable_edge_page_sq W)
    (fun q ↦ W.nonneg q.1 q.2)
  rwa [integral_edgeProd W] at h

/-- **The paw density, in the glued-edge form.** -/
theorem integral_edge_page_eq :
    (∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ)) =
      ∫ x, degree W x ^ 1 * rootedTriangle W x ∂μ := by
  rw [integral_edge_pageOp W (by norm_num : (0:ℝ) ≤ 1)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only []
  rw [Real.rpow_one, pow_one]

/-- **The paw bound**, transported to the glued-edge form. -/
theorem paw_le (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1) ≤
      ∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ) := by
  rw [integral_edge_page_eq W]
  have h := rootedTree_bound (H := Taeyoung.Methods.Chromatic.pawGraph) W 1
    (paw_factorization W) hp
  rw [paw_factorization W] at h
  calc cliqueDensity 2 W ^ 2 * (2 * cliqueDensity 2 W - 1)
      = cliqueDensity 2 W ^ (1 + 1) * (2 * cliqueDensity 2 W - 1) := by norm_num
    _ ≤ _ := h

end Edge

/-! ### The graph and its peeling -/

/-- Two paws glued along the edge `{0,1}`: triangles `{0,1,2}` and `{0,1,4}`,
with a private leaf on each of the two apexes. -/
def amalgam : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (2, 3), (0, 4), (1, 4), (4, 5)]

instance : DecidableRel amalgam.Adj := graphFromEdges_decidableAdj _ _

lemma graphWeight_amalgam (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight amalgam W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 2) (x 3) *
        W (x 0) (x 4) * W (x 1) (x 4) * W (x 4) (x 5) := by
  have hedge : amalgam.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(2, 3), s(0, 4), s(1, 4), s(4, 5)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      revert u v
      decide
  rw [graphWeight, hedge]
  simp
  ring

section Peel

variable (W : Graphon Ω μ)

private lemma meas_amalgam : Measurable fun y : Fin 6 → Ω ↦
    W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 2) (y 3) *
      W (y 0) (y 4) * W (y 1) (y 4) * W (y 4) (y 5) :=
  ((((((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)).mul (measurable_coord_pair W 2 3)).mul
    (measurable_coord_pair W 0 4)).mul (measurable_coord_pair W 1 4)).mul
    (measurable_coord_pair W 4 5)

omit [IsProbabilityMeasure μ] in
private lemma bdd_amalgam (x : Fin 6 → Ω) :
    |W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 2) (x 3) *
      W (x 0) (x 4) * W (x 1) (x 4) * W (x 4) (x 5)| ≤ 1 := by
  have h0 : 0 ≤ W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 2) (x 3) *
      W (x 0) (x 4) * W (x 1) (x 4) * W (x 4) (x 5) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_) ?_ <;> exact W.nonneg _ _
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)

/-- **The density of Atlas 115 is the glued edge against the square of the
rooted page.** -/
theorem homDensity_amalgam :
    homDensity amalgam W =
      ∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2 ∂(μ.prod μ) := by
  rw [← integral_integral (f := fun a b ↦ W a b * pageOp W 1 a b ^ 2)
    (integrable_edge_page_sq W)]
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_amalgam W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3 *
        W a0 a4 * W a1 a4 * W a4 a5)
      (meas_amalgam W) (bdd_amalgam W)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  -- the second copy integrates to a page
  have h5 : ∀ a2 a3 a4 : Ω,
      (∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3 * W a0 a4 * W a1 a4 *
          W a4 a5 ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3) *
          (W a0 a4 * W a1 a4 * degree W a4) := by
    intro a2 a3 a4
    have hre : ∀ a5 : Ω,
        W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3 * W a0 a4 * W a1 a4 * W a4 a5 =
          ((W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3) * (W a0 a4 * W a1 a4)) *
            W a4 a5 := fun a5 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    show ((W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3) * (W a0 a4 * W a1 a4)) *
        degree W a4 = _
    ring
  have h4 : ∀ a2 a3 : Ω,
      (∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3 * W a0 a4 * W a1 a4 *
          W a4 a5 ∂μ ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3) * pageOp W 1 a0 a1 := by
    intro a2 a3
    rw [integral_congr_ae (ae_of_all _ (h5 a2 a3)), integral_const_mul]
    congr 1
    rw [pageOp]
    refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
    simp only []
    rw [Real.rpow_one]
  have h3 : ∀ a2 : Ω,
      (∫ a3, ∫ a4, ∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3 * W a0 a4 *
          W a1 a4 * W a4 a5 ∂μ ∂μ ∂μ) =
        (W a0 a1 * pageOp W 1 a0 a1) *
          (W a0 a2 * W a1 a2 * degree W a2) := by
    intro a2
    rw [integral_congr_ae (ae_of_all _ (h4 a2))]
    have hre : ∀ a3 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2 * W a2 a3) * pageOp W 1 a0 a1 =
          ((W a0 a1 * pageOp W 1 a0 a1) * (W a0 a2 * W a1 a2)) * W a2 a3 :=
      fun a3 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    show ((W a0 a1 * pageOp W 1 a0 a1) * (W a0 a2 * W a1 a2)) * degree W a2 = _
    ring
  rw [integral_congr_ae (ae_of_all _ h3), integral_const_mul]
  have hpage : (∫ a2, W a0 a2 * W a1 a2 * degree W a2 ∂μ) = pageOp W 1 a0 a1 := by
    rw [pageOp]
    refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
    simp only []
    rw [Real.rpow_one]
  rw [hpage]
  ring

end Peel

/-! ### The bound -/

/-- **Atlas 115 dominates its target.** -/
theorem amalgam_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity amalgam W := by
  set p := cliqueDensity 2 W with hpdef
  have hp0 : (0 : ℝ) < p := by linarith
  have hpaw := paw_le W hp
  have hpaw0 : 0 ≤ p ^ 2 * (2 * p - 1) := by nlinarith
  have hcs := sq_edge_page_le W
  have hsq : (p ^ 2 * (2 * p - 1)) ^ 2 ≤
      (∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ∂(μ.prod μ)) ^ 2 :=
    pow_le_pow_left₀ hpaw0 hpaw 2
  rw [homDensity_amalgam W]
  have hchain : (p ^ 2 * (2 * p - 1)) ^ 2 ≤
      p * ∫ q, W q.1 q.2 * pageOp W 1 q.1 q.2 ^ 2 ∂(μ.prod μ) :=
    le_trans hsq hcs
  have hval : (p ^ 2 * (2 * p - 1)) ^ 2 = p * (p ^ 3 * (2 * p - 1) ^ 2) := by ring
  rw [hval] at hchain
  exact le_of_mul_le_mul_left hchain hp0

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_115 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 2] z = z ^ 3 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃` on `{0,1,2}`, then the leaf `3` on `2`, then the apex `4` on the glued
edge `{0,1}`, then the leaf `5` on `4`. -/
def iso115 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {2}) {some 0, some 1})
      {none} ≃g amalgam where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom115 : IsChromaticPolynomial amalgam
    ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := amalgam) iso115
    (isClique_singleton _ none)
    (isChromaticPolynomial_attachVertex (isClique_attach_pair {2} (by decide))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({2} : Finset (Fin 3)).card) = 1 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count115 (k : ℕ) :
    properAssignmentCount amalgam k =
      (k - 1) * ((k - 2) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := amalgam) iso115
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isClique_attach_pair {2} (by decide)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({2} : Finset (Fin 3)).card) = 1 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton]

theorem num115 : IsChromaticNumber amalgam 3 where
  positive := by rw [count115]; decide
  zero_below k hk := by
    rw [count115]
    interval_cases k <;> decide

/-- **Atlas 115 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_115 : Taeyoung.SatisfiesLowerBound amalgam := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := amalgam) hP chrom115
  have hreq : r = 3 := IsChromaticNumber.unique (H := amalgam) hr num115
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := amalgam_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_115]
    exact hkey

end Taeyoung.Methods.SelfAmalgam
