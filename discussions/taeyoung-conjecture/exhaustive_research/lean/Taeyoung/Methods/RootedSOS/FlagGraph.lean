import Taeyoung.Foundation.GraphMap
import Taeyoung.Foundation.ProductIntegral
import Taeyoung.Foundation.DisjointUnion

/-!
# Ordinary graphs obtained by gluing one-branch rooted flags

This is the graph-theoretic foundation shared by the three-root Atlas 43
certificate and the four-root `S₄` certificates.  A rooted flag consists of
a graph on `k` labels and a set of labels adjacent to one branch vertex.
Multiplying two flags identifies their labels and keeps two independent branch
vertices.  The result is an ordinary graph on `k + 2` vertices.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

open Taeyoung

/-- The first `k` vertices in the glued graph are its labels. -/
def labelInclusion (k : ℕ) : Fin k → Fin (k + 2) := Fin.castAdd 2

/-- The two final vertices in the glued graph are its independent branches. -/
def branchInclusion (k : ℕ) : Fin 2 → Fin (k + 2) := Fin.natAdd k

@[simp] theorem labelInclusion_val {k : ℕ} (i : Fin k) :
    (labelInclusion k i).1 = i.1 := rfl

@[simp] theorem branchInclusion_val {k : ℕ} (b : Fin 2) :
    (branchInclusion k b).1 = k + b.1 := rfl

/-- Label-label edges transported into the glued vertex set. -/
def liftedLabelEdges {k : ℕ} (L : SimpleGraph (Fin k)) [DecidableRel L.Adj] :
    Finset (Sym2 (Fin (k + 2))) :=
  L.edgeFinset.image (Sym2.map (labelInclusion k))

/-- Edges from a selected label set to branch `b`. -/
def branchEdges {k : ℕ} (N : Finset (Fin k)) (b : Fin 2) :
    Finset (Sym2 (Fin (k + 2))) :=
  N.image fun i ↦ s(labelInclusion k i, branchInclusion k b)

/-- The edge set of two one-branch flags glued along all their labels. -/
def gluedFlagEdges {k : ℕ} (L : SimpleGraph (Fin k)) [DecidableRel L.Adj]
    (N₀ N₁ : Finset (Fin k)) : Finset (Sym2 (Fin (k + 2))) :=
  liftedLabelEdges L ∪ branchEdges N₀ 0 ∪ branchEdges N₁ 1

/-- The ordinary simple graph represented by a product of two rooted flags. -/
def gluedFlagGraph {k : ℕ} (L : SimpleGraph (Fin k)) [DecidableRel L.Adj]
    (N₀ N₁ : Finset (Fin k)) : SimpleGraph (Fin (k + 2)) :=
  SimpleGraph.fromEdgeSet ↑(gluedFlagEdges L N₀ N₁)

instance gluedFlagGraph_decidableAdj {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) :
    DecidableRel (gluedFlagGraph L N₀ N₁).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet _).Adj)

private lemma labelInclusion_injective (k : ℕ) :
    Function.Injective (labelInclusion k) := Fin.castAdd_injective k 2

private lemma branchEdge_injective {k : ℕ} (b : Fin 2) :
    Function.Injective
      (fun i : Fin k ↦ s(labelInclusion k i, branchInclusion k b)) := by
  intro i j hij
  simp only [Sym2.eq_iff] at hij
  rcases hij with h | h
  · exact Fin.ext (by simpa [labelInclusion] using congrArg Fin.val h.1)
  · have : i.1 < k := i.2
    have := congrArg Fin.val h.1
    simp [labelInclusion, branchInclusion] at this
    omega

private lemma liftedLabelEdges_nondiag {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] {e : Sym2 (Fin (k + 2))}
    (he : e ∈ liftedLabelEdges L) : ¬e.IsDiag := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  rw [Sym2.isDiag_map (labelInclusion_injective k)]
  exact L.not_isDiag_of_mem_edgeFinset hd

private lemma branchEdges_nondiag {k : ℕ} (N : Finset (Fin k)) (b : Fin 2)
    {e : Sym2 (Fin (k + 2))} (he : e ∈ branchEdges N b) : ¬e.IsDiag := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  rw [Sym2.mk_isDiag_iff]
  intro h
  have := congrArg Fin.val h
  simp [labelInclusion, branchInclusion] at this
  omega

private lemma gluedFlagEdges_nondiag {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k))
    {e : Sym2 (Fin (k + 2))} (he : e ∈ gluedFlagEdges L N₀ N₁) :
    ¬e.IsDiag := by
  simp only [gluedFlagEdges, Finset.mem_union] at he
  rcases he with (he | he) | he
  · exact liftedLabelEdges_nondiag L he
  · exact branchEdges_nondiag N₀ 0 he
  · exact branchEdges_nondiag N₁ 1 he

theorem gluedFlagGraph_edgeFinset {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) :
    (gluedFlagGraph L N₀ N₁).edgeFinset = gluedFlagEdges L N₀ N₁ := by
  ext e
  constructor
  · intro he
    have hs := SimpleGraph.mem_edgeFinset.mp he
    rw [gluedFlagGraph, SimpleGraph.edgeSet_fromEdgeSet] at hs
    exact hs.1
  · intro he
    apply SimpleGraph.mem_edgeFinset.mpr
    rw [gluedFlagGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨he, gluedFlagEdges_nondiag L N₀ N₁ he⟩

private lemma label_branch_disjoint {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N : Finset (Fin k)) (b : Fin 2) :
    Disjoint (liftedLabelEdges L) (branchEdges N b) := by
  rw [Finset.disjoint_left]
  intro e heL heN
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp heL
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp heN
  induction d using Sym2.inductionOn with
  | _ u v =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at hi
      rcases hi with h | h
      · have := congrArg Fin.val h.2
        change k + b.1 = v.1 at this
        omega
      · have := congrArg Fin.val h.2
        change k + b.1 = u.1 at this
        omega

private lemma branch_branch_disjoint {k : ℕ}
    (N₀ N₁ : Finset (Fin k)) :
    Disjoint (branchEdges N₀ 0) (branchEdges N₁ 1) := by
  rw [Finset.disjoint_left]
  intro e he₀ he₁
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he₀
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp he₁
  simp only [Sym2.eq_iff] at hj
  rcases hj with h | h
  · have := congrArg Fin.val h.2
    simp [branchInclusion] at this
  · have := congrArg Fin.val h.1
    simp [labelInclusion, branchInclusion] at this
    omega

private lemma left_union_right_disjoint {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) :
    Disjoint (liftedLabelEdges L ∪ branchEdges N₀ 0) (branchEdges N₁ 1) :=
  Finset.disjoint_union_left.mpr
    ⟨label_branch_disjoint L N₁ 1, branch_branch_disjoint N₀ N₁⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]

/-- Product of the branch-to-label graphon factors. -/
def rootedBranchMonomial {k : ℕ} (W : Graphon Ω μ) (x : Fin k → Ω) (y : Ω)
    (N : Finset (Fin k)) : ℝ :=
  ∏ i ∈ N, W (x i) y

lemma measurable_rootedBranchMonomial {k : ℕ} (W : Graphon Ω μ)
    (N : Finset (Fin k)) :
    Measurable fun q : (Fin k → Ω) × Ω ↦ rootedBranchMonomial W q.1 q.2 N := by
  unfold rootedBranchMonomial
  apply Finset.measurable_fun_prod
  intro i _
  have hp : Measurable fun q : (Fin k → Ω) × Ω ↦ (q.1 i, q.2) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  simpa [Function.comp_def, Function.uncurry] using W.measurable.comp hp

lemma rootedBranchMonomial_nonneg {k : ℕ} (W : Graphon Ω μ)
    (x : Fin k → Ω) (y : Ω) (N : Finset (Fin k)) :
    0 ≤ rootedBranchMonomial W x y N := by
  exact Finset.prod_nonneg fun i _ ↦ W.nonneg (x i) y

lemma rootedBranchMonomial_le_one {k : ℕ} (W : Graphon Ω μ)
    (x : Fin k → Ω) (y : Ω) (N : Finset (Fin k)) :
    rootedBranchMonomial W x y N ≤ 1 := by
  exact Finset.prod_le_one (fun i _ ↦ W.nonneg (x i) y)
    (fun i _ ↦ W.le_one (x i) y)

/-- Conditional density of one branch vertex attached to a set of labels. -/
noncomputable def rootedBranchDensity {k : ℕ} (W : Graphon Ω μ)
    (x : Fin k → Ω) (N : Finset (Fin k)) : ℝ :=
  ∫ y, rootedBranchMonomial W x y N ∂μ

private lemma measurable_rootedBranchMonomial_right {k : ℕ} (W : Graphon Ω μ)
    (x : Fin k → Ω) (N : Finset (Fin k)) :
    Measurable fun y ↦ rootedBranchMonomial W x y N := by
  exact (measurable_rootedBranchMonomial W N).comp (measurable_const.prodMk measurable_id)

private lemma integral_assignmentMeasure_one (f : Ω → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) :
    (∫ x : Fin 1 → Ω, f (x 0) ∂(assignmentMeasure (Fin 1) μ)) = ∫ x, f x ∂μ := by
  have hm : Measurable fun x : Fin 1 → Ω ↦ f (x 0) :=
    hf.comp (measurable_pi_apply 0)
  simpa using
    (integral_assignmentMeasure_succ (μ := μ) (fun x : Fin 1 → Ω ↦ f (x 0)) hm
      (fun x ↦ hb (x 0)))

/-- The two branch coordinates are independent under the assignment measure. -/
theorem integral_two_rootedBranchMonomial {k : ℕ} (W : Graphon Ω μ)
    (x : Fin k → Ω) (N₀ N₁ : Finset (Fin k)) :
    (∫ y : Fin 2 → Ω,
      rootedBranchMonomial W x (y 0) N₀ * rootedBranchMonomial W x (y 1) N₁
        ∂(assignmentMeasure (Fin 2) μ)) =
      rootedBranchDensity W x N₀ * rootedBranchDensity W x N₁ := by
  have hsplit := (measurePreserving_assignmentSplit (μ := μ) 1 1).integral_comp'
    (g := fun q : (Fin 1 → Ω) × (Fin 1 → Ω) ↦
      rootedBranchMonomial W x (q.1 0) N₀ * rootedBranchMonomial W x (q.2 0) N₁)
  simp only [assignmentSplit_apply] at hsplit
  norm_num at hsplit
  have hcast : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := rfl
  rw [hcast] at hsplit
  rw [hsplit, MeasureTheory.integral_prod_mul
    (fun u : Fin 1 → Ω ↦ rootedBranchMonomial W x (u 0) N₀)
    (fun v : Fin 1 → Ω ↦ rootedBranchMonomial W x (v 0) N₁)]
  rw [integral_assignmentMeasure_one
    (fun y ↦ rootedBranchMonomial W x y N₀)
    (measurable_rootedBranchMonomial_right W x N₀)
    (fun y ↦ by
      rw [abs_of_nonneg (rootedBranchMonomial_nonneg W x y N₀)]
      exact rootedBranchMonomial_le_one W x y N₀)]
  rw [integral_assignmentMeasure_one
    (fun y ↦ rootedBranchMonomial W x y N₁)
    (measurable_rootedBranchMonomial_right W x N₁)
    (fun y ↦ by
      rw [abs_of_nonneg (rootedBranchMonomial_nonneg W x y N₁)]
      exact rootedBranchMonomial_le_one W x y N₁)]
  rfl

/-- The product integrand obtained after splitting the label coordinates from
the two branch coordinates. -/
def splitGluedFlagKernel {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ)
    (q : (Fin k → Ω) × (Fin 2 → Ω)) : ℝ :=
  graphWeight L W q.1 *
    (rootedBranchMonomial W q.1 (q.2 0) N₀ *
      rootedBranchMonomial W q.1 (q.2 1) N₁)

lemma measurable_splitGluedFlagKernel {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ) :
    Measurable (splitGluedFlagKernel L N₀ N₁ W) := by
  have h₀ : Measurable fun q : (Fin k → Ω) × (Fin 2 → Ω) ↦
      rootedBranchMonomial W q.1 (q.2 0) N₀ := by
    exact (measurable_rootedBranchMonomial W N₀).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have h₁ : Measurable fun q : (Fin k → Ω) × (Fin 2 → Ω) ↦
      rootedBranchMonomial W q.1 (q.2 1) N₁ := by
    exact (measurable_rootedBranchMonomial W N₁).comp
      (measurable_fst.prodMk ((measurable_pi_apply 1).comp measurable_snd))
  exact ((measurable_graphWeight L W).comp measurable_fst).mul (h₀.mul h₁)

lemma splitGluedFlagKernel_nonneg {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ)
    (q : (Fin k → Ω) × (Fin 2 → Ω)) :
    0 ≤ splitGluedFlagKernel L N₀ N₁ W q := by
  exact mul_nonneg (graphWeight_nonneg L W q.1)
    (mul_nonneg (rootedBranchMonomial_nonneg W q.1 (q.2 0) N₀)
      (rootedBranchMonomial_nonneg W q.1 (q.2 1) N₁))

lemma splitGluedFlagKernel_le_one {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ)
    (q : (Fin k → Ω) × (Fin 2 → Ω)) :
    splitGluedFlagKernel L N₀ N₁ W q ≤ 1 := by
  apply mul_le_one₀ (graphWeight_le_one L W q.1)
  · exact mul_nonneg (rootedBranchMonomial_nonneg W q.1 (q.2 0) N₀)
      (rootedBranchMonomial_nonneg W q.1 (q.2 1) N₁)
  · exact mul_le_one₀ (rootedBranchMonomial_le_one W q.1 (q.2 0) N₀)
      (rootedBranchMonomial_nonneg W q.1 (q.2 1) N₁)
      (rootedBranchMonomial_le_one W q.1 (q.2 1) N₁)

lemma integrable_splitGluedFlagKernel {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ) :
    MeasureTheory.Integrable (splitGluedFlagKernel L N₀ N₁ W)
      ((assignmentMeasure (Fin k) μ).prod (assignmentMeasure (Fin 2) μ)) := by
  refine (MeasureTheory.integrable_const
    (μ := (assignmentMeasure (Fin k) μ).prod (assignmentMeasure (Fin 2) μ))
    (1 : ℝ)).mono' (measurable_splitGluedFlagKernel L N₀ N₁ W).aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun q ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (splitGluedFlagKernel_nonneg L N₀ N₁ W q)]
  exact splitGluedFlagKernel_le_one L N₀ N₁ W q

/-- The conditional kernel left after integrating out the two branch
coordinates of a glued pair of rooted flags. -/
noncomputable def rootedGluedKernel {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ)
    (x : Fin k → Ω) : ℝ :=
  graphWeight L W x * (rootedBranchDensity W x N₀ * rootedBranchDensity W x N₁)

/-- Pointwise weight factorisation of an ordinary glued flag graph. -/
theorem graphWeight_gluedFlagGraph {k : ℕ} (L : SimpleGraph (Fin k))
    [DecidableRel L.Adj] (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ)
    (z : Fin (k + 2) → Ω) :
    graphWeight (gluedFlagGraph L N₀ N₁) W z =
      graphWeight L W (fun i ↦ z (labelInclusion k i)) *
        rootedBranchMonomial W (fun i ↦ z (labelInclusion k i))
          (z (branchInclusion k 0)) N₀ *
        rootedBranchMonomial W (fun i ↦ z (labelInclusion k i))
          (z (branchInclusion k 1)) N₁ := by
  rw [graphWeight, gluedFlagGraph_edgeFinset]
  unfold gluedFlagEdges
  rw [Finset.prod_union (left_union_right_disjoint L N₀ N₁)]
  rw [Finset.prod_union (label_branch_disjoint L N₀ 0)]
  unfold liftedLabelEdges branchEdges
  rw [Finset.prod_image
    (fun d _ e _ h ↦ sym2_map_injective (labelInclusion_injective k) h)]
  rw [Finset.prod_image (fun i _ j _ h ↦ branchEdge_injective (k := k) 0 h)]
  rw [Finset.prod_image (fun i _ j _ h ↦ branchEdge_injective (k := k) 1 h)]
  simp only [graphWeight, rootedBranchMonomial, edgeValue_sym2_map, edgeValue_mk]

/-- **Semantic gluing identity.** Integrating the conditional kernel of two
rooted flags gives the ordinary homomorphism density of the graph obtained by
identifying their labels. -/
theorem integral_rootedGluedKernel_eq_homDensity {k : ℕ}
    (L : SimpleGraph (Fin k)) [DecidableRel L.Adj]
    (N₀ N₁ : Finset (Fin k)) (W : Graphon Ω μ) :
    (∫ x, rootedGluedKernel L N₀ N₁ W x ∂(assignmentMeasure (Fin k) μ)) =
      homDensity (gluedFlagGraph L N₀ N₁) W := by
  have hmp := measurePreserving_assignmentSplit (μ := μ) k 2
  have hsplit := hmp.integral_comp'
    (g := splitGluedFlagKernel L N₀ N₁ W)
  simp only [assignmentSplit_apply] at hsplit
  calc
    (∫ x, rootedGluedKernel L N₀ N₁ W x ∂(assignmentMeasure (Fin k) μ)) =
        ∫ x, (∫ y, splitGluedFlagKernel L N₀ N₁ W (x, y)
          ∂(assignmentMeasure (Fin 2) μ)) ∂(assignmentMeasure (Fin k) μ) := by
      refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun x ↦ ?_)
      simp only [rootedGluedKernel, splitGluedFlagKernel]
      rw [MeasureTheory.integral_const_mul,
        integral_two_rootedBranchMonomial W x N₀ N₁]
    _ = ∫ q, splitGluedFlagKernel L N₀ N₁ W q
          ∂((assignmentMeasure (Fin k) μ).prod (assignmentMeasure (Fin 2) μ)) := by
      exact (MeasureTheory.integral_prod _
        (integrable_splitGluedFlagKernel L N₀ N₁ W)).symm
    _ = ∫ z, graphWeight (gluedFlagGraph L N₀ N₁) W z
          ∂(assignmentMeasure (Fin (k + 2)) μ) := by
      rw [← hsplit]
      refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun z ↦ ?_)
      simpa [splitGluedFlagKernel, labelInclusion, branchInclusion, mul_assoc] using
        (graphWeight_gluedFlagGraph L N₀ N₁ W z).symm
    _ = homDensity (gluedFlagGraph L N₀ N₁) W := rfl

end Taeyoung.Methods.RootedSOS
