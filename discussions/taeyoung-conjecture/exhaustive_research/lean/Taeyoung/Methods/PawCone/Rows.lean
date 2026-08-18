import Taeyoung.Methods.PawCone.Base
import Taeyoung.Methods.RootedTriangleTree.Paw
import Taeyoung.Foundation.DisjointUnion

/-!
# The three catalogue members of the paw / triangle–edge cone family

The base bounds are the two the note quotes, and nothing else is needed:

* `t(P,V) ≥ z²(2z-1)` is `rootedTree_bound` at `r = 1`, the paw's own row;
* `t(K₃ ⊔ K₂,V) = t(K₃,V)·z ≥ z(2z-1)·z` is multiplicativity together with the
  Goodman triangle bound `A₃`;
* isolated vertices drop out by `homDensity_map_castAdd`.

| Atlas | base `B` | `m` | vertices |
|---:|---|---:|---:|
| 49 | `P` | 1 | 5 |
| 156 | `P ⊔ K₁` | 2 | 6 |
| 165 | `K₃ ⊔ K₂` | 2 | 6 |

Each cone is a `K₄` with two further clique-attachments, which is where its
chromatic polynomial `x(x-1)^m(x-2)²(x-3)` comes from.  Vertex `0` of the `K₄`
is the cone apex throughout, so the attachment sets always contain `0`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.PawCone

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.CliqueLeaf
  Taeyoung.Methods.PureChordal Taeyoung.Methods.RootedTriangleTree

/-! ### Two clique facts used by every tower -/

/-- Every subset of a complete graph is a clique. -/
lemma isClique_top {n : ℕ} (S : Finset (Fin n)) :
    (⊤ : SimpleGraph (Fin n)).IsClique (S : Set (Fin n)) := by
  intro u _ v _ huv
  simpa using huv

/-- A singleton is a clique in any graph. -/
lemma isClique_singleton {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V) :
    G.IsClique (({v} : Finset V) : Set V) := by
  intro u hu w hw huw
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hw
  exact absurd (hu.trans hw.symm) huw

/-! ### The three bases -/

/-- The paw with one isolated vertex. -/
abbrev pawIsolated : SimpleGraph (Fin (4 + 1)) := pawRooted.map (Fin.castAdd 1)

/-- The triangle–edge product `K₃ ⊔ K₂`. -/
abbrev triangleEdge : SimpleGraph (Fin (3 + 2)) :=
  disjointUnion (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 2))

/-- The paw is the `r = 1` member of the rooted triangle–tree family. -/
theorem base_paw {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν) (hz : 1 / 2 ≤ cliqueDensity 2 V) :
    baseTarget (cliqueDensity 2 V) ≤ homDensity pawRooted V := by
  have hfac : homDensity pawRooted V =
      ∫ x, degree V x ^ 1 * rootedTriangle V x ∂ν := by
    rw [homDensity_pawRooted]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp)
  have hb := rootedTree_bound V 1 hfac hz
  rw [baseTarget]
  calc cliqueDensity 2 V ^ 2 * (2 * cliqueDensity 2 V - 1)
      = cliqueDensity 2 V ^ (1 + 1) * (2 * cliqueDensity 2 V - 1) := by norm_num
    _ ≤ homDensity pawRooted V := hb

theorem base_pawIsolated {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν) (hz : 1 / 2 ≤ cliqueDensity 2 V) :
    baseTarget (cliqueDensity 2 V) ≤ homDensity pawIsolated V := by
  rw [homDensity_map_castAdd pawRooted 1 V]
  exact base_paw V hz

lemma cliquePoly_three (z : ℝ) : cliquePoly 3 z = z * (2 * z - 1) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cliquePoly_succ, show (2 : ℕ) = 1 + 1 from rfl,
    cliquePoly_succ, cliquePoly_one]
  push_cast
  ring

theorem base_triangleEdge {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν) (hz : 1 / 2 ≤ cliqueDensity 2 V) :
    baseTarget (cliqueDensity 2 V) ≤ homDensity triangleEdge V := by
  have hthr : cliqueThreshold 1 ≤ cliqueDensity 2 V := by
    simp only [cliqueThreshold]
    norm_num
    linarith
  have h3 : cliqueDensity 2 V * (2 * cliqueDensity 2 V - 1) ≤ cliqueDensity 3 V := by
    have := cliqueDensity_ge_cliquePoly' V 1 hthr
    rwa [show (1 : ℕ) + 2 = 3 from rfl, cliquePoly_three] at this
  have hz0 : (0 : ℝ) ≤ cliqueDensity 2 V := cliqueDensity_nonneg 2 V
  have hmul := mul_le_mul_of_nonneg_right h3 hz0
  rw [homDensity_disjointUnion, baseTarget]
  show cliqueDensity 2 V ^ 2 * (2 * cliqueDensity 2 V - 1) ≤
    cliqueDensity 3 V * cliqueDensity 2 V
  nlinarith [hmul]

/-! ### Atlas 49 — the cone over the paw -/

def equiv49 : Option (Fin 4) ≃ Fin 5 where
  toFun a := match a with
    | none => 4
    | some i => ![0, 1, 2, 3] i
  invFun j := ![some 0, some 1, some 2, some 3, none] j
  left_inv := by decide
  right_inv := by decide

def iso49 : attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 1} ≃g coneGraph pawRooted where
  toEquiv := equiv49
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom49 : IsChromaticPolynomial (coneGraph pawRooted)
    ((X : ℝ[X]) * (X - C 1) ^ 1 * (X - C 2) ^ 2 * (X - C 3)) := by
  have h := isChromaticPolynomial_of_attachIso iso49 (isClique_top _)
    (isChromaticPolynomial_top 4)
  rw [show (({0, 1} : Finset (Fin 4)).card) = 2 from by decide] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ 1 * (X - C 2) ^ 2 * (X - C 3) =
      (X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat, map_zero, sub_zero, one_mul, pow_one]
    ring
  rw [hpoly]
  exact h

theorem count49 (k : ℕ) :
    properAssignmentCount (coneGraph pawRooted) k = (k - 2) * k.descFactorial 4 := by
  rw [properAssignmentCount_of_attachIso iso49 (isClique_top _) k,
    properAssignmentCount_top, show (({0, 1} : Finset (Fin 4)).card) = 2 from by decide]

theorem num49 : IsChromaticNumber (coneGraph pawRooted) 4 where
  positive := by rw [count49]; decide
  zero_below k hk := by
    rw [count49, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero]

theorem satisfiesLowerBound_49 :
    Taeyoung.SatisfiesLowerBound (coneGraph pawRooted) :=
  satisfiesLowerBound_of_pawCone (m := 1) pawRooted chrom49 num49
    fun V hz ↦ base_paw V hz

/-! ### Atlas 156 — the cone over the paw with an isolated vertex -/

def equiv156 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some i) => ![0, 1, 2, 3] i
  invFun j := ![some (some 0), some (some 1), some (some 2), some (some 3),
    some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso156 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 1}) {some 0} ≃g
      coneGraph pawIsolated where
  toEquiv := equiv156
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom156 : IsChromaticPolynomial (coneGraph pawIsolated)
    ((X : ℝ[X]) * (X - C 1) ^ 2 * (X - C 2) ^ 2 * (X - C 3)) := by
  have h := isChromaticPolynomial_of_attachIso iso156
    (isClique_singleton _ (some 0))
    (isChromaticPolynomial_attachVertex (isClique_top _)
      (isChromaticPolynomial_top 4))
  rw [show (({0, 1} : Finset (Fin 4)).card) = 2 from by decide,
    Finset.card_singleton] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ 2 * (X - C 2) ^ 2 * (X - C 3) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat, map_zero, sub_zero, one_mul]
    ring
  rw [hpoly]
  exact h

theorem count156 (k : ℕ) :
    properAssignmentCount (coneGraph pawIsolated) k =
      (k - 1) * ((k - 2) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso iso156 (isClique_singleton _ (some 0)) k,
    properAssignmentCount_attachVertex (isClique_top _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 4)).card) = 2 from by decide, Finset.card_singleton]

theorem num156 : IsChromaticNumber (coneGraph pawIsolated) 4 where
  positive := by rw [count156]; decide
  zero_below k hk := by
    rw [count156, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero, Nat.mul_zero]

theorem satisfiesLowerBound_156 :
    Taeyoung.SatisfiesLowerBound (coneGraph pawIsolated) :=
  satisfiesLowerBound_of_pawCone (m := 2) pawIsolated chrom156 num156
    fun V hz ↦ base_pawIsolated V hz

/-! ### Atlas 165 — the cone over `K₃ ⊔ K₂` -/

/-- The apex of the `K₄` together with the first attached vertex is a clique:
that vertex was attached to `{0}`. -/
lemma isClique_165 :
    (attachVertex (⊤ : SimpleGraph (Fin 4)) {0}).IsClique
      ((({none, some 0} : Finset (Option (Fin 4))) : Set (Option (Fin 4)))) := by
  intro u hu v hv huv
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · simp
  · simp
  · exact absurd rfl huv

def iso165 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0}) {none, some 0} ≃g
      coneGraph triangleEdge where
  toEquiv := equiv156
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom165 : IsChromaticPolynomial (coneGraph triangleEdge)
    ((X : ℝ[X]) * (X - C 1) ^ 2 * (X - C 2) ^ 2 * (X - C 3)) := by
  have h := isChromaticPolynomial_of_attachIso iso165 isClique_165
    (isChromaticPolynomial_attachVertex (isClique_top _)
      (isChromaticPolynomial_top 4))
  rw [Finset.card_singleton,
    show (({none, some 0} : Finset (Option (Fin 4))).card) = 2 from by decide] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ 2 * (X - C 2) ^ 2 * (X - C 3) =
      (X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat, map_zero, sub_zero, one_mul]
    ring
  rw [hpoly]
  exact h

theorem count165 (k : ℕ) :
    properAssignmentCount (coneGraph triangleEdge) k =
      (k - 2) * ((k - 1) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso iso165 isClique_165 k,
    properAssignmentCount_attachVertex (isClique_top _), properAssignmentCount_top,
    Finset.card_singleton,
    show (({none, some 0} : Finset (Option (Fin 4))).card) = 2 from by decide]

theorem num165 : IsChromaticNumber (coneGraph triangleEdge) 4 where
  positive := by rw [count165]; decide
  zero_below k hk := by
    rw [count165, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero, Nat.mul_zero]

theorem satisfiesLowerBound_165 :
    Taeyoung.SatisfiesLowerBound (coneGraph triangleEdge) :=
  satisfiesLowerBound_of_pawCone (m := 2) triangleEdge chrom165 num165
    fun V hz ↦ base_triangleEdge V hz

end Taeyoung.Methods.PawCone
