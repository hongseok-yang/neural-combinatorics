import Taeyoung.Foundation.ProductIntegral

/-!
# Weights and densities along an injective relabelling of the vertices

A graph carried into a larger vertex type by an injection has the same weight,
read at the pulled-back assignment.  Two catalogue constructions are instances:

* the cone `K₁ ∨ F`, whose non-root part is `F` shifted by `Fin.succ`;
* a graph with `k` isolated vertices appended, which is the graph itself carried
  along `Fin.castAdd k`.  For that case `homDensity_map_castAdd` says what one
  expects: isolated vertices do not change the homomorphism density.

The statements take `DecidableRel (G.map f).Adj` as an instance argument rather
than synthesising it, so that they rewrite against whatever instance the goal
already carries.
-/

open MeasureTheory Finset

namespace Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V'] in
lemma sym2_map_injective {f : V → V'} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro e₁
  induction e₁ using Sym2.inductionOn with
  | _ a b =>
    intro e₂
    induction e₂ using Sym2.inductionOn with
    | _ c d =>
      intro h
      rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at h
      rw [Sym2.eq_iff]
      exact h.imp (fun p ↦ ⟨hf p.1, hf p.2⟩) fun p ↦ ⟨hf p.1, hf p.2⟩

omit [DecidableEq V] in
/-- The edges of a graph carried along an injection are the images of its
edges. -/
lemma edgeFinset_map_eq_image (G : SimpleGraph V) [DecidableRel G.Adj]
    {f : V → V'} (hf : Function.Injective f) [DecidableRel (G.map f).Adj] :
    (G.map f).edgeFinset = G.edgeFinset.image (Sym2.map f) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image,
      SimpleGraph.map_adj']
    constructor
    · rintro ⟨-, i, j, hij, rfl, rfl⟩
      exact ⟨s(i, j), hij, rfl⟩
    · rintro ⟨e', he', heq⟩
      revert he' heq
      induction e' using Sym2.inductionOn with
      | _ i j =>
        intro he' heq
        rw [SimpleGraph.mem_edgeSet] at he'
        rw [Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨fun h ↦ he'.ne (hf h), i, j, he', rfl, rfl⟩
        · exact ⟨fun h ↦ he'.ne (hf h).symm, j, i, he'.symm, rfl, rfl⟩

omit [IsProbabilityMeasure μ] [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V'] in
lemma edgeValue_sym2_map (W : Graphon Ω μ) (y : V' → Ω) (f : V → V')
    (e : Sym2 V) :
    edgeValue W y (Sym2.map f e) = edgeValue W (fun i ↦ y (f i)) e := by
  induction e using Sym2.inductionOn with
  | _ u v => simp [edgeValue]

omit [IsProbabilityMeasure μ] [DecidableEq V] in
/-- **Weight is preserved by an injective relabelling.** -/
theorem graphWeight_map (G : SimpleGraph V) [DecidableRel G.Adj]
    {f : V → V'} (hf : Function.Injective f) [DecidableRel (G.map f).Adj]
    (W : Graphon Ω μ) (y : V' → Ω) :
    graphWeight (G.map f) W y = graphWeight G W (fun i ↦ y (f i)) := by
  rw [graphWeight, edgeFinset_map_eq_image G hf,
    Finset.prod_image fun e _ e' _ h ↦ sym2_map_injective hf h, graphWeight]
  exact Finset.prod_congr rfl fun e _ ↦ edgeValue_sym2_map W y f e

/-- **Isolated vertices do not change the homomorphism density.**  `G` planted on
the first `m` of `m + k` vertices has the density of `G`. -/
theorem homDensity_map_castAdd {m : ℕ} (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (k : ℕ) [DecidableRel (G.map (Fin.castAdd k)).Adj]
    (W : Graphon Ω μ) :
    homDensity (G.map (Fin.castAdd k)) W = homDensity G W := by
  have hbdd : ∀ z : Fin m → Ω, |graphWeight G W z| ≤ 1 := fun z ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg G W z)]
    exact graphWeight_le_one G W z
  rw [homDensity, integral_congr_ae (ae_of_all _ fun y ↦
    graphWeight_map G (Fin.castAdd_injective m k) W y)]
  exact integral_assignmentMeasure_castAdd (graphWeight G W)
    (measurable_graphWeight G W) hbdd k

end Taeyoung
