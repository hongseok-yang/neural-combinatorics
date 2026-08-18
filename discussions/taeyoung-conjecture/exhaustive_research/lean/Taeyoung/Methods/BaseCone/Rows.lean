import Taeyoung.Methods.BaseCone
import Taeyoung.Methods.PawCone.Rows
import Taeyoung.Methods.CliqueLeaf.Rows
import Taeyoung.Methods.Components.Atlas84
import Taeyoung.Methods.RootedTriangleTree.L2
import Taeyoung.Methods.RootedTriangleTree.Q1

/-!
# The verified-base cones

Five of the six cones of `notes/six_verified_base_cones.tex`.  The sixth,
Atlas 192, is the cone over Atlas 40, whose base bound is the forest-cone
theorem and is not yet available.

| Atlas | base | root list `ks` of `χ_B` | `kmax` | base bound |
|---:|---|---|---:|---|
| 177 | diamond `⊔ K₁` | `[0,0,1,2,2]` | 2 | the cone over `K_{1,2}` |
| 179 | Atlas 34 (`L₂`) | `[0,1,1,1,2]` | 2 | rooted triangle–tree, `r = 2` |
| 183 | Atlas 36 (`Q₁`) | `[0,1,1,1,2]` | 2 | the two-edge-tail bound |
| 200 | Atlas 45 | `[0,1,1,2,3]` | 3 | clique common leaf |
| 205 | Atlas 49 | `[0,1,2,2,3]` | 3 | the paw cone |

The diamond needs no separate argument: it is itself the cone over the star
`K_{1,2}`, whose target `z²` is Jensen, so `coneGraph_affineProd_bound` supplies
it.  Every cone here is a `K₄` or `K₅` with two further clique-attachments,
which is where its chromatic polynomial comes from.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.BaseCone

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PawCone Taeyoung.Methods.CliqueLeaf
  Taeyoung.Methods.Components Taeyoung.Methods.RootedTriangleTree
  Taeyoung.Methods.PureChordal

/-! ### The four root lists -/

lemma affineProd_star (z : ℝ) : affineProd [0, 1, 1] z = z ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_nil]
  ring

lemma affineProd_diamond (z : ℝ) : affineProd [1, 2, 2] z = z * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_nil]
  ring

lemma affineProd_33 (z : ℝ) :
    affineProd [0, 0, 1, 2, 2] z = z * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

lemma affineProd_34 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2] z = z ^ 3 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

lemma affineProd_45 (z : ℝ) :
    affineProd [0, 1, 1, 2, 3] z = z ^ 2 * (2 * z - 1) * (3 * z - 2) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

lemma affineProd_49 (z : ℝ) :
    affineProd [0, 1, 2, 2, 3] z = z * (2 * z - 1) ^ 2 * (3 * z - 2) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_nil]
  ring

/-! ### Two clique facts -/

lemma isCliqueTop {n : ℕ} (S : Finset (Fin n)) :
    (⊤ : SimpleGraph (Fin n)).IsClique (S : Set (Fin n)) := by
  intro u _ v _ huv
  simpa using huv

/-- Two `some`s of a complete graph stay adjacent after an attachment. -/
lemma isClique_attach_pair {n : ℕ} (S : Finset (Fin n)) {u v : Fin n} (huv : u ≠ v) :
    (attachVertex (⊤ : SimpleGraph (Fin n)) S).IsClique
      ((({some u, some v} : Finset (Option (Fin n))) : Set (Option (Fin n)))) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · simpa using huv
  · simpa using huv.symm
  · exact absurd rfl hab

/-- The attached vertex and a member of the set it was attached to. -/
lemma isClique_attach_new {n : ℕ} (S : Finset (Fin n)) {u : Fin n} (hu : u ∈ S) :
    (attachVertex (⊤ : SimpleGraph (Fin n)) S).IsClique
      ((({none, some u} : Finset (Option (Fin n))) : Set (Option (Fin n)))) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · simpa using hu
  · simpa using hu
  · exact absurd rfl hab

/-! ### Atlas 177 — the cone over the diamond with an isolated vertex -/

/-- The diamond, as the cone over the star `K_{1,2}`. -/
abbrev diamond : SimpleGraph (Fin (3 + 1)) := coneGraph (starTree 2)

/-- The diamond with one isolated vertex. -/
abbrev diamondIsolated : SimpleGraph (Fin (4 + 1)) := diamond.map (Fin.castAdd 1)

theorem base_star {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (_hz : 1 - 1 / (1 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 1, 1] (cliqueDensity 2 V) ≤ homDensity (starTree 2) V := by
  rw [affineProd_star, homDensity_starTree]
  exact RootedTriangleTree.pow_le_moment V 2

theorem base_diamond {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (hz : 1 - 1 / (2 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [1, 2, 2] (cliqueDensity 2 V) ≤ homDensity diamond V := by
  have h := coneGraph_affineProd_bound (h := 1) (starTree 2) [0, 1, 1] (kmax := 1)
    rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) base_star V
    (by norm_num; linarith)
  rwa [show ([0, 1, 1] : List ℝ).map (· + 1) = [1, 2, 2] from by norm_num] at h

theorem base_33 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (hz : 1 - 1 / (2 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 0, 1, 2, 2] (cliqueDensity 2 V) ≤
      homDensity diamondIsolated V := by
  rw [homDensity_map_castAdd diamond 1 V, affineProd_33, ← affineProd_diamond]
  exact base_diamond V hz

/-- Vertex `0` of the `K₄` is the apex; `4` is attached to `{0,1,2}` and `5` to
`{0}`.  The relabelling is the one already used for Atlas 156. -/
def iso177 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 1, 2}) {some 0} ≃g
      coneGraph diamondIsolated where
  toEquiv := equiv156
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom177 : IsChromaticPolynomial (coneGraph diamondIsolated)
    ((((0 : ℝ) :: ([0, 0, 1, 2, 2] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso
    (H' := coneGraph diamondIsolated) iso177 (isClique_singleton _ (some 0))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 4))
  rw [show (({0, 1, 2} : Finset (Fin 4)).card) = 3 from by decide,
    Finset.card_singleton] at h
  have hlist : ((0 : ℝ) :: ([0, 0, 1, 2, 2] : List ℝ).map (· + 1)) =
      [0, 1, 1, 2, 3, 3] := by norm_num
  rw [hlist]
  have hpoly : ((([0, 1, 1, 2, 3, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((3 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count177 (k : ℕ) :
    properAssignmentCount (coneGraph diamondIsolated) k =
      (k - 1) * ((k - 3) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph diamondIsolated) iso177
      (isClique_singleton _ (some 0)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1, 2} : Finset (Fin 4)).card) = 3 from by decide,
    Finset.card_singleton]

theorem num177 : IsChromaticNumber (coneGraph diamondIsolated) 4 where
  positive := by rw [count177]; decide
  zero_below k hk := by
    rw [count177, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

theorem satisfiesLowerBound_177 :
    Taeyoung.SatisfiesLowerBound (coneGraph diamondIsolated) :=
  satisfiesLowerBound_of_baseCone (h := 3) diamondIsolated [0, 0, 1, 2, 2]
    (kmax := 2) (r := 4) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom177 num177 (by norm_num) base_33

/-! ### Atlas 179 — the cone over `L₂` -/

theorem base_34 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (hz : 1 - 1 / (2 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 1, 1, 1, 2] (cliqueDensity 2 V) ≤ homDensity l2Graph V := by
  have hhalf : (1 : ℝ) / 2 ≤ cliqueDensity 2 V := by norm_num at hz; linarith
  have h := rootedTree_bound V 2 (l2_factorization V) hhalf
  rw [affineProd_34]
  calc cliqueDensity 2 V ^ 3 * (2 * cliqueDensity 2 V - 1)
      = cliqueDensity 2 V ^ (2 + 1) * (2 * cliqueDensity 2 V - 1) := by norm_num
    _ ≤ homDensity l2Graph V := h

/-- `K₄` on `{0,3,4,5}`, with `1` and `2` attached to the edge `{0,5}`. -/
def equiv179 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 2
    | some none => 1
    | some (some i) => ![0, 3, 4, 5] i
  invFun j := ![some (some 0), some none, none, some (some 1), some (some 2),
    some (some 3)] j
  left_inv := by decide
  right_inv := by decide

def iso179 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 3}) {some 0, some 3} ≃g
      coneGraph l2Graph where
  toEquiv := equiv179
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom179 : IsChromaticPolynomial (coneGraph l2Graph)
    ((((0 : ℝ) :: ([0, 1, 1, 1, 2] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph l2Graph) iso179
    (isClique_attach_pair {0, 3} (by decide))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 4))
  rw [show (({0, 3} : Finset (Fin 4)).card) = 2 from by decide,
    show (({some 0, some 3} : Finset (Option (Fin 4))).card) = 2 from by decide] at h
  rw [show ((0 : ℝ) :: ([0, 1, 1, 1, 2] : List ℝ).map (· + 1)) =
    [0, 1, 2, 2, 2, 3] from by norm_num]
  have hpoly : ((([0, 1, 2, 2, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count179 (k : ℕ) :
    properAssignmentCount (coneGraph l2Graph) k =
      (k - 2) * ((k - 2) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph l2Graph) iso179
      (isClique_attach_pair {0, 3} (by decide)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 3} : Finset (Fin 4)).card) = 2 from by decide,
    show (({some 0, some 3} : Finset (Option (Fin 4))).card) = 2 from by decide]

theorem num179 : IsChromaticNumber (coneGraph l2Graph) 4 where
  positive := by rw [count179]; decide
  zero_below k hk := by
    rw [count179, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

theorem satisfiesLowerBound_179 :
    Taeyoung.SatisfiesLowerBound (coneGraph l2Graph) :=
  satisfiesLowerBound_of_baseCone (h := 3) l2Graph [0, 1, 1, 1, 2]
    (kmax := 2) (r := 4) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom179 num179 (by norm_num) base_34

/-! ### Atlas 183 — the cone over `Q₁` -/

theorem base_36 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (hz : 1 - 1 / (2 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 1, 1, 1, 2] (cliqueDensity 2 V) ≤ homDensity q1Graph V := by
  have hhalf : (1 : ℝ) / 2 ≤ cliqueDensity 2 V := by norm_num at hz; linarith
  rw [affineProd_34, ← homDensity_iso V q1RootedIso, homDensity_q1Rooted]
  exact tail_bound V hhalf

/-- `K₄` on `{0,2,3,4}`, with `5` attached to `{0,4}` and `1` to `{0,5}`. -/
def equiv183 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 1
    | some none => 5
    | some (some i) => ![0, 2, 3, 4] i
  invFun j := ![some (some 0), none, some (some 1), some (some 2),
    some (some 3), some none] j
  left_inv := by decide
  right_inv := by decide

def iso183 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0, 3}) {none, some 0} ≃g
      coneGraph q1Graph where
  toEquiv := equiv183
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom183 : IsChromaticPolynomial (coneGraph q1Graph)
    ((((0 : ℝ) :: ([0, 1, 1, 1, 2] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := coneGraph q1Graph) iso183
    (isClique_attach_new {0, 3} (by decide))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 4))
  rw [show (({0, 3} : Finset (Fin 4)).card) = 2 from by decide,
    show (({none, some 0} : Finset (Option (Fin 4))).card) = 2 from by decide] at h
  rw [show ((0 : ℝ) :: ([0, 1, 1, 1, 2] : List ℝ).map (· + 1)) =
    [0, 1, 2, 2, 2, 3] from by norm_num]
  have hpoly : ((([0, 1, 2, 2, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((2 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count183 (k : ℕ) :
    properAssignmentCount (coneGraph q1Graph) k =
      (k - 2) * ((k - 2) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso (H' := coneGraph q1Graph) iso183
      (isClique_attach_new {0, 3} (by decide)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 3} : Finset (Fin 4)).card) = 2 from by decide,
    show (({none, some 0} : Finset (Option (Fin 4))).card) = 2 from by decide]

theorem num183 : IsChromaticNumber (coneGraph q1Graph) 4 where
  positive := by rw [count183]; decide
  zero_below k hk := by
    rw [count183, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

theorem satisfiesLowerBound_183 :
    Taeyoung.SatisfiesLowerBound (coneGraph q1Graph) :=
  satisfiesLowerBound_of_baseCone (h := 3) q1Graph [0, 1, 1, 1, 2]
    (kmax := 2) (r := 4) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom183 num183 (by norm_num) base_36

/-! ### Atlas 200 and 205 — the cones over Atlas 45 and Atlas 49 -/

lemma cliquePoly_four (z : ℝ) : cliquePoly 4 z = z * (2 * z - 1) * (3 * z - 2) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, cliquePoly_succ, cliquePoly_three]
  push_cast
  ring

theorem base_45 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (hz : 1 - 1 / (3 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 1, 1, 2, 3] (cliqueDensity 2 V) ≤
      homDensity (cliqueLeafGraph 1 1) V := by
  have hthr : 1 - 1 / (((1 : ℕ) : ℝ) + 2) ≤ cliqueDensity 2 V := by
    push_cast
    norm_num at hz ⊢
    linarith
  have h := cliqueLeaf_density V 1 1 hthr
  rw [affineProd_45]
  refine le_trans (le_of_eq ?_) h
  rw [show (1 : ℕ) + 3 = 4 from rfl, cliquePoly_four]
  ring

theorem base_49 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (V : Graphon Ω ν)
    (hz : 1 - 1 / (3 : ℝ) ≤ cliqueDensity 2 V) :
    affineProd [0, 1, 2, 2, 3] (cliqueDensity 2 V) ≤
      homDensity (coneGraph pawRooted) V := by
  have hthr : (2 : ℝ) / 3 ≤ cliqueDensity 2 V := by norm_num at hz ⊢; linarith
  have h := coneGraph_baseTarget_bound (m := 1) pawRooted
    (fun U hu ↦ base_paw U hu) V hthr
  rw [affineProd_49]
  refine le_trans (le_of_eq ?_) h
  ring

/-- `K₅` on `{0,1,2,3,4}`, with the last vertex attached to a face of it. -/
def equiv200 : Option (Fin 5) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some i => ![0, 1, 2, 3, 4] i
  invFun j := ![some 0, some 1, some 2, some 3, some 4, none] j
  left_inv := by decide
  right_inv := by decide

def iso200 : attachVertex (⊤ : SimpleGraph (Fin 5)) {0, 1} ≃g
    coneGraph (cliqueLeafGraph 1 1) where
  toEquiv := equiv200
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom200 : IsChromaticPolynomial (coneGraph (cliqueLeafGraph 1 1))
    ((((0 : ℝ) :: ([0, 1, 1, 2, 3] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso
    (H' := coneGraph (cliqueLeafGraph 1 1)) iso200 (isCliqueTop _)
    (isChromaticPolynomial_top 5)
  rw [show (({0, 1} : Finset (Fin 5)).card) = 2 from by decide] at h
  rw [show ((0 : ℝ) :: ([0, 1, 1, 2, 3] : List ℝ).map (· + 1)) =
    [0, 1, 2, 2, 3, 4] from by norm_num]
  have hpoly : ((([0, 1, 2, 2, 3, 4] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 5, ((X : ℝ[X]) - C (i : ℝ)) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count200 (k : ℕ) :
    properAssignmentCount (coneGraph (cliqueLeafGraph 1 1)) k =
      (k - 2) * k.descFactorial 5 := by
  rw [properAssignmentCount_of_attachIso
      (H' := coneGraph (cliqueLeafGraph 1 1)) iso200 (isCliqueTop _) k,
    properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 5)).card) = 2 from by decide]

theorem num200 : IsChromaticNumber (coneGraph (cliqueLeafGraph 1 1)) 5 where
  positive := by rw [count200]; decide
  zero_below k hk := by
    rw [count200, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero]

theorem satisfiesLowerBound_200 :
    Taeyoung.SatisfiesLowerBound (coneGraph (cliqueLeafGraph 1 1)) :=
  satisfiesLowerBound_of_baseCone (h := 3) (cliqueLeafGraph 1 1) [0, 1, 1, 2, 3]
    (kmax := 3) (r := 5) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom200 num200 (by norm_num) base_45

def iso205 : attachVertex (⊤ : SimpleGraph (Fin 5)) {0, 1, 2} ≃g
    coneGraph (coneGraph pawRooted) where
  toEquiv := equiv200
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom205 : IsChromaticPolynomial (coneGraph (coneGraph pawRooted))
    ((((0 : ℝ) :: ([0, 1, 2, 2, 3] : List ℝ).map (· + 1)).map fun k ↦
      (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso
    (H' := coneGraph (coneGraph pawRooted)) iso205 (isCliqueTop _)
    (isChromaticPolynomial_top 5)
  rw [show (({0, 1, 2} : Finset (Fin 5)).card) = 3 from by decide] at h
  rw [show ((0 : ℝ) :: ([0, 1, 2, 2, 3] : List ℝ).map (· + 1)) =
    [0, 1, 2, 3, 3, 4] from by norm_num]
  have hpoly : ((([0, 1, 2, 3, 3, 4] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((3 : ℕ) : ℝ)) * ∏ i ∈ range 5, ((X : ℝ[X]) - C (i : ℝ)) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count205 (k : ℕ) :
    properAssignmentCount (coneGraph (coneGraph pawRooted)) k =
      (k - 3) * k.descFactorial 5 := by
  rw [properAssignmentCount_of_attachIso
      (H' := coneGraph (coneGraph pawRooted)) iso205 (isCliqueTop _) k,
    properAssignmentCount_top,
    show (({0, 1, 2} : Finset (Fin 5)).card) = 3 from by decide]

theorem num205 : IsChromaticNumber (coneGraph (coneGraph pawRooted)) 5 where
  positive := by rw [count205]; decide
  zero_below k hk := by
    rw [count205, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero]

theorem satisfiesLowerBound_205 :
    Taeyoung.SatisfiesLowerBound (coneGraph (coneGraph pawRooted)) :=
  satisfiesLowerBound_of_baseCone (h := 3) (coneGraph pawRooted) [0, 1, 2, 2, 3]
    (kmax := 3) (r := 5) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) chrom205 num205 (by norm_num) base_49

end Taeyoung.Methods.BaseCone
