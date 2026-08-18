import Taeyoung.Methods.BaseCone.Rows
import Taeyoung.Methods.PathSidorenko

/-!
# Cones over forests, and the last verified-base cone

`notes/forest_cone_graphon_bound.tex` proves its corollary through forest
Sidorenko, `t(F,V) ≥ z^{e(F)}`.  The classifier attributes five Atlas rows to
that methodology, and deleting the universal vertex from each shows that four
of the five need nothing of the kind:

| Atlas | base `F` | `t(F,V) ≥ z^{e(F)}` because |
|---:|---|---|
| 40 | `K_{1,2} ⊔ K₁` | `t(K_{1,n},V) = M_n ≥ zⁿ`, Jensen |
| 111 | `K_{1,2} ⊔ 2K₁` | the same |
| 117 | `K₂ ⊔ K₂ ⊔ K₁` | multiplicativity, with equality |
| 135 | `K_{1,3} ⊔ K₁` | Jensen again |
| 136 | `P₄ ⊔ K₁` | **not** a star: this one needs `t(P₄,V) ≥ z³` |

So only Atlas 136 depends on a genuinely new inequality, and that inequality is
`Methods/PathSidorenko.lean`; everything else in the list is
`homDensity_starTree`, `pow_le_moment`, and `homDensity_disjointUnion`, fed
through `coneGraph_affineProd_bound`.

Closing Atlas 40 also closes Atlas 192, the sixth cone of
`notes/six_verified_base_cones.tex`, which is the cone over it.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.ForestCone

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PawCone Taeyoung.Methods.BaseCone
  Taeyoung.Methods.Components Taeyoung.Methods.RootedTriangleTree
  Taeyoung.Methods.PathSidorenko

/-! ### The root lists -/

lemma affineProd_0011 (z : ℝ) : affineProd [0, 0, 1, 1] z = z ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_nil]
  ring

lemma affineProd_00011 (z : ℝ) : affineProd [0, 0, 0, 1, 1] z = z ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

lemma affineProd_00111 (z : ℝ) : affineProd [0, 0, 1, 1, 1] z = z ^ 3 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

lemma affineProd_1122 (z : ℝ) :
    affineProd [1, 1, 2, 2] z = z ^ 2 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_nil]
  ring

lemma affineProd_01122 (z : ℝ) :
    affineProd [0, 1, 1, 2, 2] z = z ^ 2 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

/-! ### The four star / product bases -/

/-- `K_{1,2} ⊔ K₁`. -/
abbrev starIsolate1 : SimpleGraph (Fin (3 + 1)) := (starTree 2).map (Fin.castAdd 1)

/-- `K_{1,2} ⊔ 2K₁`. -/
abbrev starIsolate2 : SimpleGraph (Fin (3 + 2)) := (starTree 2).map (Fin.castAdd 2)

/-- `K_{1,3} ⊔ K₁`. -/
abbrev star3Isolate : SimpleGraph (Fin (4 + 1)) := (starTree 3).map (Fin.castAdd 1)

/-- `K₂ ⊔ K₂ ⊔ K₁`. -/
abbrev twoEdgesIsolate : SimpleGraph (Fin (2 + 2 + 1)) :=
  (disjointUnion (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2))).map
    (Fin.castAdd 1)

theorem base_starIsolate1 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (_hz : 1 - 1 / (1 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 0, 1, 1] (cliqueDensity 2 V) ≤ homDensity starIsolate1 V := by
  rw [homDensity_map_castAdd (starTree 2) 1 V, affineProd_0011,
    homDensity_starTree]
  exact RootedTriangleTree.pow_le_moment V 2

theorem base_starIsolate2 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (_hz : 1 - 1 / (1 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 0, 0, 1, 1] (cliqueDensity 2 V) ≤
      homDensity starIsolate2 V := by
  rw [homDensity_map_castAdd (starTree 2) 2 V, affineProd_00011,
    homDensity_starTree]
  exact RootedTriangleTree.pow_le_moment V 2

theorem base_star3Isolate {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (_hz : 1 - 1 / (1 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 0, 1, 1, 1] (cliqueDensity 2 V) ≤
      homDensity star3Isolate V := by
  rw [homDensity_map_castAdd (starTree 3) 1 V, affineProd_00111,
    homDensity_starTree]
  exact RootedTriangleTree.pow_le_moment V 3

theorem base_twoEdgesIsolate {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (_hz : 1 - 1 / (1 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 0, 0, 1, 1] (cliqueDensity 2 V) ≤
      homDensity twoEdgesIsolate V := by
  rw [homDensity_map_castAdd
      (disjointUnion (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2))) 1 V,
    affineProd_00011, homDensity_disjointUnion]
  exact le_of_eq (by rw [sq]; rfl)

/-! ### Atlas 40 — a triangle with a leaf on an edge and a leaf on a vertex -/

/-- `K₃` with `3` attached to the edge `{0,1}` and `4` attached to `{0}`. -/
def equiv40 : Option (Option (Fin 3)) ≃ Fin 5 where
  toFun a := match a with
    | none => 4
    | some none => 3
    | some (some i) => ![0, 1, 2] i
  invFun j := ![some (some 0), some (some 1), some (some 2), some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso40 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0} ≃g
      coneGraph starIsolate1 where
  toEquiv := equiv40
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom40 : IsChromaticPolynomial (coneGraph starIsolate1)
    ((((0 : ℝ) :: ([0, 0, 1, 1] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph starIsolate1)
    iso40 (isClique_singleton _ (some 0))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 3))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton] at h
  rw [show ((0 : ℝ) :: ([0, 0, 1, 1] : List ℝ).map (· + 1)) =
    [0, 1, 1, 2, 2] from by norm_num]
  have hpoly : ((([0, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count40 (k : ℕ) :
    properAssignmentCount (coneGraph starIsolate1) k =
      (k - 1) * ((k - 2) * k.descFactorial 3) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph starIsolate1) iso40
      (isClique_singleton _ (some 0)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide, Finset.card_singleton]

theorem num40 : IsChromaticNumber (coneGraph starIsolate1) 3 where
  positive := by rw [count40]; decide
  zero_below k hk := by
    rw [count40, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

theorem satisfiesLowerBound_40 :
    Taeyoung.SatisfiesLowerBound (coneGraph starIsolate1) :=
  satisfiesLowerBound_of_baseCone (h := 2) starIsolate1 [0, 0, 1, 1]
    (kmax := 1) (r := 3) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom40 num40 (by norm_num) base_starIsolate1

/-! ### Atlas 111, 117 and 135 — three-attachment towers -/

/-- `some (some (some i)) ↦ i`, then the three attached vertices in order. -/
def equivTriple : Option (Option (Option (Fin 3))) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some none) => 3
    | some (some (some i)) => ![0, 1, 2] i
  invFun j := ![some (some (some 0)), some (some (some 1)), some (some (some 2)),
    some (some none), some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso111 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0})
      {some (some 0)} ≃g coneGraph starIsolate2 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

def iso117 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {none, some 0})
      {some (some 0)} ≃g coneGraph twoEdgesIsolate where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

def iso135 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0, some 1})
      {some (some 0)} ≃g coneGraph star3Isolate where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom111 : IsChromaticPolynomial (coneGraph starIsolate2)
    ((((0 : ℝ) :: ([0, 0, 0, 1, 1] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph starIsolate2)
    iso111 (isClique_singleton _ (some (some 0)))
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 0))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  rw [show ((0 : ℝ) :: ([0, 0, 0, 1, 1] : List ℝ).map (· + 1)) =
    [0, 1, 1, 1, 2, 2] from by norm_num]
  have hpoly : ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count111 (k : ℕ) :
    properAssignmentCount (coneGraph starIsolate2) k =
      (k - 1) * ((k - 1) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph starIsolate2) iso111
      (isClique_singleton _ (some (some 0))) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 0)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num111 : IsChromaticNumber (coneGraph starIsolate2) 3 where
  positive := by rw [count111]; decide
  zero_below k hk := by
    rw [count111, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

theorem satisfiesLowerBound_111 :
    Taeyoung.SatisfiesLowerBound (coneGraph starIsolate2) :=
  satisfiesLowerBound_of_baseCone (h := 3) starIsolate2 [0, 0, 0, 1, 1]
    (kmax := 1) (r := 3) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom111 num111 (by norm_num) base_starIsolate2

theorem chrom117 : IsChromaticPolynomial (coneGraph twoEdgesIsolate)
    ((((0 : ℝ) :: ([0, 0, 0, 1, 1] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph twoEdgesIsolate)
    iso117 (isClique_singleton _ (some (some 0)))
    (isChromaticPolynomial_attachVertex (isClique_attach_new {0} (by decide))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [Finset.card_singleton,
    show (({none, some 0} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton] at h
  rw [show ((0 : ℝ) :: ([0, 0, 0, 1, 1] : List ℝ).map (· + 1)) =
    [0, 1, 1, 1, 2, 2] from by norm_num]
  have hpoly : ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count117 (k : ℕ) :
    properAssignmentCount (coneGraph twoEdgesIsolate) k =
      (k - 1) * ((k - 2) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph twoEdgesIsolate) iso117
      (isClique_singleton _ (some (some 0))) k,
    properAssignmentCount_attachVertex (isClique_attach_new {0} (by decide)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    Finset.card_singleton,
    show (({none, some 0} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton]

theorem num117 : IsChromaticNumber (coneGraph twoEdgesIsolate) 3 where
  positive := by rw [count117]; decide
  zero_below k hk := by
    rw [count117, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

theorem satisfiesLowerBound_117 :
    Taeyoung.SatisfiesLowerBound (coneGraph twoEdgesIsolate) :=
  satisfiesLowerBound_of_baseCone (h := 3) twoEdgesIsolate [0, 0, 0, 1, 1]
    (kmax := 1) (r := 3) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom117 num117 (by norm_num) base_twoEdgesIsolate

theorem chrom135 : IsChromaticPolynomial (coneGraph star3Isolate)
    ((((0 : ℝ) :: ([0, 0, 1, 1, 1] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph star3Isolate)
    iso135 (isClique_singleton _ (some (some 0)))
    (isChromaticPolynomial_attachVertex (isClique_attach_pair {0, 1} (by decide))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton] at h
  rw [show ((0 : ℝ) :: ([0, 0, 1, 1, 1] : List ℝ).map (· + 1)) =
    [0, 1, 1, 2, 2, 2] from by norm_num]
  have hpoly : ((([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count135 (k : ℕ) :
    properAssignmentCount (coneGraph star3Isolate) k =
      (k - 1) * ((k - 2) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph star3Isolate) iso135
      (isClique_singleton _ (some (some 0))) k,
    properAssignmentCount_attachVertex (isClique_attach_pair {0, 1} (by decide)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton]

theorem num135 : IsChromaticNumber (coneGraph star3Isolate) 3 where
  positive := by rw [count135]; decide
  zero_below k hk := by
    rw [count135, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

theorem satisfiesLowerBound_135 :
    Taeyoung.SatisfiesLowerBound (coneGraph star3Isolate) :=
  satisfiesLowerBound_of_baseCone (h := 3) star3Isolate [0, 0, 1, 1, 1]
    (kmax := 1) (r := 3) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom135 num135 (by norm_num) base_star3Isolate

/-! ### Atlas 192 — the sixth verified-base cone -/

theorem base_40 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (hz : 1 - 1 / (2 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 1, 1, 2, 2] (cliqueDensity 2 V) ≤
      homDensity (coneGraph starIsolate1) V := by
  have h := coneGraph_affineProd_bound (h := 2) starIsolate1 [0, 0, 1, 1]
    (kmax := 1) rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    base_starIsolate1 V (by norm_num; linarith)
  rw [show ([0, 0, 1, 1] : List ℝ).map (· + 1) = [1, 1, 2, 2] from by norm_num] at h
  rw [affineProd_01122, ← affineProd_1122]
  exact h

def iso192 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 1, 2})
      {some 0, some 1} ≃g coneGraph (coneGraph starIsolate1) where
  toEquiv := equiv156
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom192 : IsChromaticPolynomial (coneGraph (coneGraph starIsolate1))
    ((((0 : ℝ) :: ([0, 1, 1, 2, 2] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso
    (H' := coneGraph (coneGraph starIsolate1)) iso192
    (isClique_attach_pair {0, 1, 2} (by decide))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 4))
  rw [show (({0, 1, 2} : Finset (Fin 4)).card) = 3 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 4))).card) = 2 from by decide] at h
  rw [show ((0 : ℝ) :: ([0, 1, 1, 2, 2] : List ℝ).map (· + 1)) =
    [0, 1, 2, 2, 3, 3] from by norm_num]
  have hpoly : ((([0, 1, 2, 2, 3, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((3 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count192 (k : ℕ) :
    properAssignmentCount (coneGraph (coneGraph starIsolate1)) k =
      (k - 2) * ((k - 3) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso
      (H' := coneGraph (coneGraph starIsolate1)) iso192
      (isClique_attach_pair {0, 1, 2} (by decide)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1, 2} : Finset (Fin 4)).card) = 3 from by decide,
    show (({some 0, some 1} : Finset (Option (Fin 4))).card) = 2 from by decide]

theorem num192 : IsChromaticNumber (coneGraph (coneGraph starIsolate1)) 4 where
  positive := by rw [count192]; decide
  zero_below k hk := by
    rw [count192, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

theorem satisfiesLowerBound_192 :
    Taeyoung.SatisfiesLowerBound (coneGraph (coneGraph starIsolate1)) :=
  satisfiesLowerBound_of_baseCone (h := 3) (coneGraph starIsolate1)
    [0, 1, 1, 2, 2] (kmax := 2) (r := 4) rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) chrom192 num192 (by norm_num) base_40

/-! ### Atlas 136 — the one row that needs path Sidorenko

The one row of this methodology whose forest is not a union of stars and single
edges.  Its base is `P₄ ⊔ K₁`, so the Sidorenko input it needs is exactly
`t(P₄,V) ≥ z³`, which is `pow_three_le_pathIntegral` of
`Methods/PathSidorenko.lean`. -/

/-- `P₄ ⊔ K₁`, over the path of `Methods/PathSidorenko.lean`. -/
abbrev p4Isolated : SimpleGraph (Fin (4 + 1)) := p4Graph.map (Fin.castAdd 1)

def iso136 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 2}) {none, some 0})
      {some (some 0)} ≃g coneGraph p4Isolated where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom136 : IsChromaticPolynomial (coneGraph p4Isolated)
    ((((0 : ℝ) :: (List.replicate 2 (0 : ℝ) ++ List.replicate 3 1).map (· + 1)).map
      fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph p4Isolated)
    iso136 (isClique_singleton _ (some (some 0)))
    (isChromaticPolynomial_attachVertex (isClique_attach_new {0, 2} (by decide))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 2} : Finset (Fin 3)).card) = 2 from by decide,
    show (({none, some 0} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton] at h
  rw [show (List.replicate 2 (0 : ℝ) ++ List.replicate 3 1) = [0, 0, 1, 1, 1] from rfl,
    show ((0 : ℝ) :: ([0, 0, 1, 1, 1] : List ℝ).map (· + 1)) =
      [0, 1, 1, 2, 2, 2] from by norm_num]
  have hpoly : ((([0, 1, 1, 2, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count136 (k : ℕ) :
    properAssignmentCount (coneGraph p4Isolated) k =
      (k - 1) * ((k - 2) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph p4Isolated) iso136
      (isClique_singleton _ (some (some 0))) k,
    properAssignmentCount_attachVertex (isClique_attach_new {0, 2} (by decide)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 2} : Finset (Fin 3)).card) = 2 from by decide,
    show (({none, some 0} : Finset (Option (Fin 3))).card) = 2 from by decide,
    Finset.card_singleton]

theorem num136 : IsChromaticNumber (coneGraph p4Isolated) 3 where
  positive := by rw [count136]; decide
  zero_below k hk := by
    rw [count136, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 136.**  The forest is `P₄ ⊔ K₁`, the only one in this methodology
that is not a union of stars and single edges.  Its Sidorenko input is path
Sidorenko, `t(P₄,V) ≥ z³`, proved in `Methods/PathSidorenko.lean`. -/
theorem satisfiesLowerBound_136 :
    Taeyoung.SatisfiesLowerBound (coneGraph p4Isolated) :=
  satisfiesLowerBound_coneGraph_of_sidorenko (h := 3) p4Isolated (c := 2) (e := 3)
    rfl (by norm_num) chrom136 num136
    (fun V ↦ by
      rw [homDensity_map_castAdd p4Graph 1 V, homDensity_p4Graph]
      exact pow_three_le_pathIntegral V)

end Taeyoung.Methods.ForestCone
