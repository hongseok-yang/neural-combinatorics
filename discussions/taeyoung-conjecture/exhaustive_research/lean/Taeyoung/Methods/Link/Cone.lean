import Taeyoung.Methods.Link.Tilt
import Taeyoung.Foundation.GraphMap

/-!
# The cone `K₁ ∨ F` and its rooted density

Five methodologies bound the density of a graph of the form `K₁ ∨ F`: a
distinguished vertex joined to every vertex of a smaller graph `F`.  Each of them
conditions on the image `x` of that vertex and applies a theorem valid for
*arbitrary* graphons to the link `W_x`.

This file supplies the identity that makes the conditioning legitimate,

  `t(K₁ ∨ F, W) = ∫ d(x) ^ n · t(F, W_x) dμ(x)`,

in the two halves it is actually used in:

* `homDensity_coneGraph`, the combinatorial half — the cone density is the
  `μ`-average of the rooted density `∫ (∏ i, W x (y i)) · graphWeight F W y`.
  This is pure coordinate peeling; no tilt appears.
* `rootedDensity_eq`, the analytic half — at a point of positive degree the
  rooted density is `d(x) ^ n · t(F, W_x)`, by the tilt transfer of
  `Foundation/TiltTransfer.lean`.

Keeping them apart matters: the first holds everywhere, so the degenerate set
`d(x) = 0` never has to be divided by.  There the rooted density is bounded below
by `0`, which is all any consumer needs, since `d(x) ^ n` vanishes too.
-/

open MeasureTheory Finset

namespace Taeyoung.Methods.Link

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ}

/-! ### The cone graph -/

/-- The star centred at `0` on `Fin (n+1)`. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun u _ ↦ u = 0

instance starGraph_decidableAdj (n : ℕ) : DecidableRel (starGraph n).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

/-- **The cone `K₁ ∨ F`.**  Vertex `0` is joined to every vertex of `F`, which
occupies the remaining coordinates through `Fin.succ`. -/
def coneGraph (F : SimpleGraph (Fin n)) : SimpleGraph (Fin (n + 1)) :=
  starGraph n ⊔ F.map (Fin.succEmb n)

instance coneGraph_decidableAdj (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    DecidableRel (coneGraph F).Adj := by
  unfold coneGraph
  infer_instance

/-! ### The edge set of a cone -/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma zero_notMem_sym2_map_succ (e : Sym2 (Fin n)) :
    (0 : Fin (n + 1)) ∉ Sym2.map Fin.succ e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [Sym2.map_mk]
    simp only [Sym2.mem_iff]
    rintro (h | h) <;> exact Fin.succ_ne_zero _ h.symm

/-- The edges of the cone are the `n` star edges at `0`, together with the edges
of `F` shifted by `Fin.succ`. -/
lemma edgeFinset_coneGraph (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    (coneGraph F).edgeFinset =
      (Finset.univ.image fun i : Fin n ↦ s((0 : Fin (n + 1)), i.succ)) ∪
        F.edgeFinset.image (Sym2.map Fin.succ) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and, coneGraph, SimpleGraph.sup_adj,
      SimpleGraph.map_adj', Fin.coe_succEmb, starGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro (⟨hne, h0 | h0⟩ | ⟨-, i, j, hij, rfl, rfl⟩)
      · subst h0
        obtain rfl | ⟨j, rfl⟩ := v.eq_zero_or_eq_succ
        · exact absurd rfl hne
        · exact Or.inl ⟨j, rfl⟩
      · subst h0
        obtain rfl | ⟨j, rfl⟩ := u.eq_zero_or_eq_succ
        · exact absurd rfl hne
        · exact Or.inl ⟨j, Sym2.eq_swap⟩
      · exact Or.inr ⟨s(i, j), hij, rfl⟩
    · rintro (⟨j, hj⟩ | ⟨e', he', heq⟩)
      · rw [Sym2.eq_iff] at hj
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨(Fin.succ_ne_zero j).symm, Or.inl rfl⟩
        · exact Or.inl ⟨Fin.succ_ne_zero j, Or.inr rfl⟩
      · revert he' heq
        induction e' using Sym2.inductionOn with
        | _ i j =>
          intro he' heq
          rw [SimpleGraph.mem_edgeSet] at he'
          rw [Sym2.map_mk, Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨fun h ↦ he'.ne (Fin.succ_injective _ h), i, j, he', rfl, rfl⟩
          · exact Or.inr
              ⟨fun h ↦ he'.ne (Fin.succ_injective _ h).symm, j, i, he'.symm, rfl, rfl⟩

lemma disjoint_star_shifted (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    Disjoint (Finset.univ.image fun i : Fin n ↦ s((0 : Fin (n + 1)), i.succ))
      (F.edgeFinset.image (Sym2.map Fin.succ)) := by
  rw [Finset.disjoint_left]
  rintro e he he'
  rw [Finset.mem_image] at he he'
  obtain ⟨i, -, rfl⟩ := he
  obtain ⟨e', -, he'⟩ := he'
  exact zero_notMem_sym2_map_succ e' (he' ▸ Sym2.mem_mk_left _ _)

/-! ### The weight of a cone -/

omit [IsProbabilityMeasure μ] in
lemma edgeValue_map_succ (W : Graphon Ω μ) (a : Ω) (y : Fin n → Ω)
    (e : Sym2 (Fin n)) :
    edgeValue W (Fin.cons a y) (Sym2.map Fin.succ e) = edgeValue W y e := by
  induction e using Sym2.inductionOn with
  | _ u v => simp [edgeValue]

omit [IsProbabilityMeasure μ] in
/-- **The weight of a cone factors.**  The star at the root contributes
`∏ i, W a (y i)`, and the rest is the weight of `F`. -/
theorem graphWeight_coneGraph (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) (a : Ω) (y : Fin n → Ω) :
    graphWeight (coneGraph F) W (Fin.cons a y) =
      (∏ i, W a (y i)) * graphWeight F W y := by
  rw [graphWeight, edgeFinset_coneGraph,
    Finset.prod_union (disjoint_star_shifted F)]
  congr 1
  · rw [Finset.prod_image]
    · exact Finset.prod_congr rfl fun i _ ↦ by simp [edgeValue]
    · intro i _ j _ hij
      rw [Sym2.eq_iff] at hij
      rcases hij with ⟨-, h⟩ | ⟨h, -⟩
      · exact Fin.succ_injective _ h
      · exact absurd h.symm (Fin.succ_ne_zero j)
  · rw [Finset.prod_image fun e _ e' _ h ↦ sym2_map_injective (Fin.succ_injective n) h,
      graphWeight]
    exact Finset.prod_congr rfl fun e _ ↦ edgeValue_map_succ W a y e

/-! ### The rooted density -/

/-- The density of `F` rooted at `a`, weighted by the star at the root but *not*
normalised: `∫ (∏ i, W a (y i)) · graphWeight F W y`. -/
noncomputable def rootedDensity (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) (a : Ω) : ℝ :=
  ∫ y, (∏ i, W a (y i)) * graphWeight F W y ∂assignmentMeasure (Fin n) μ

omit [IsProbabilityMeasure μ] in
lemma star_weight_nonneg (W : Graphon Ω μ) (a : Ω) (y : Fin n → Ω) :
    0 ≤ ∏ i, W a (y i) :=
  coord_prod_nonneg (fun z ↦ W.nonneg a z) y

omit [IsProbabilityMeasure μ] in
lemma star_weight_le_one (W : Graphon Ω μ) (a : Ω) (y : Fin n → Ω) :
    (∏ i, W a (y i)) ≤ 1 := by
  simpa using coord_prod_le (fun z ↦ W.nonneg a z) (fun z ↦ W.le_one a z) y

lemma measurable_rooted_integrand (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) (a : Ω) :
    Measurable fun y : Fin n → Ω ↦ (∏ i, W a (y i)) * graphWeight F W y :=
  (measurable_coord_prod (measurable_row W.measurable a) n).mul
    (measurable_graphWeight F W)

lemma abs_rooted_integrand_le_one (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) (a : Ω) (y : Fin n → Ω) :
    |(∏ i, W a (y i)) * graphWeight F W y| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (star_weight_nonneg W a y),
    abs_of_nonneg (graphWeight_nonneg F W y)]
  exact mul_le_one₀ (star_weight_le_one W a y) (graphWeight_nonneg F W y)
    (graphWeight_le_one F W y)

lemma rootedDensity_nonneg (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) (a : Ω) : 0 ≤ rootedDensity F W a :=
  integral_nonneg fun y ↦
    mul_nonneg (star_weight_nonneg W a y) (graphWeight_nonneg F W y)

lemma rootedDensity_le_one (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) (a : Ω) : rootedDensity F W a ≤ 1 := by
  have hint : Integrable (fun y : Fin n → Ω ↦ (∏ i, W a (y i)) * graphWeight F W y)
      (assignmentMeasure (Fin n) μ) :=
    integrable_of_bounded (measurable_rooted_integrand F W a)
      (abs_rooted_integrand_le_one F W a)
  calc rootedDensity F W a
      ≤ ∫ _y : Fin n → Ω, (1 : ℝ) ∂assignmentMeasure (Fin n) μ := by
        refine integral_mono hint (integrable_const _) fun y ↦ ?_
        exact mul_le_one₀ (star_weight_le_one W a y) (graphWeight_nonneg F W y)
          (graphWeight_le_one F W y)
    _ = 1 := by simp

lemma measurable_rootedDensity (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) : Measurable (rootedDensity F W) := by
  have hg : StronglyMeasurable fun q : Ω × (Fin n → Ω) ↦
      (∏ i, W q.1 (q.2 i)) * graphWeight F W q.2 := by
    refine (?_ : Measurable _).stronglyMeasurable
    refine Measurable.mul ?_ ((measurable_graphWeight F W).comp measurable_snd)
    exact Finset.univ.measurable_fun_prod fun i _ ↦
      W.measurable.comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  exact (hg.integral_prod_right' (ν := assignmentMeasure (Fin n) μ)).measurable

lemma integrable_rootedDensity (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) : Integrable (rootedDensity F W) μ :=
  integrable_of_bdd (measurable_rootedDensity F W) fun a ↦ by
    rw [abs_of_nonneg (rootedDensity_nonneg F W a)]
    exact rootedDensity_le_one F W a

/-- **The combinatorial half of the cone identity.**  The cone density is the
`μ`-average of the rooted density.  No tilt appears, so this holds at every
point, including where the degree vanishes. -/
theorem homDensity_coneGraph (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    homDensity (coneGraph F) W = ∫ a, rootedDensity F W a ∂μ := by
  have hm : Measurable (graphWeight (coneGraph F) W) := measurable_graphWeight _ W
  have hb : ∀ z, |graphWeight (coneGraph F) W z| ≤ 1 := fun z ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W z)]
    exact graphWeight_le_one _ W z
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  simp only []
  rw [rootedDensity]
  exact integral_congr_ae (ae_of_all _ fun y ↦ graphWeight_coneGraph F W a y)

/-- **The analytic half of the cone identity.**  At a point of positive degree
the rooted density is `d(a) ^ n` times the density of `F` in the link. -/
theorem rootedDensity_eq (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) {a : Ω} (ha : 0 < degree W a) :
    rootedDensity F W a = degree W a ^ n * homDensity F (linkGraphon W a) := by
  have hlink : homDensity F (linkGraphon W a) =
      (degree W a)⁻¹ ^ n * rootedDensity F W a := by
    rw [homDensity]
    exact integral_assignmentMeasure_linkMeasure W ha (graphWeight F W)
      (measurable_graphWeight F W) zero_le_one fun y ↦ by
        rw [abs_of_nonneg (graphWeight_nonneg F W y)]
        exact graphWeight_le_one F W y
  rw [hlink, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt ha), one_pow, one_mul]

end Taeyoung.Methods.Link
