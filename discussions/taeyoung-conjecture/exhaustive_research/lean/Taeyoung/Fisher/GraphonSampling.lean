-- Vendored from `discussions/goodman-style-bound/fisher_lean`
-- (`OddCycleBound/Fisher/GraphonSampling.lean`), Lean v4.31.0, Mathlib rev fabf563a.
-- Only the `import` lines differ from the upstream file; see
-- `Taeyoung/Fisher.lean` for why the copy exists.
import Taeyoung.Fisher.GraphonRounding
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Finite sampling interface for edge and triangle densities

This file isolates the standard graphon sampling theorem at exactly the two
homomorphism densities needed by Fisher's inequality.
-/

open MeasureTheory Filter
open scoped Topology

namespace OddCycleBound

universe u

/-- A finite simple graph bundled with the decidability needed by its finite
edge and clique enumerators. -/
structure DecidableFiniteGraph (V : Type u) [Fintype V] where
  graph : SimpleGraph V
  adjDecidable : DecidableRel graph.Adj

namespace DecidableFiniteGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def edgeDensity (G : DecidableFiniteGraph V) : ℝ := by
  letI := G.adjDecidable
  exact 2 * (G.graph.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2

noncomputable def triangleDensity (G : DecidableFiniteGraph V) : ℝ := by
  letI := G.adjDecidable
  exact 6 * (Fisher.cliqueCount G.graph 3 : ℝ) / (Fintype.card V : ℝ) ^ 3

theorem fisher_density_form
    [Nonempty V] (G : DecidableFiniteGraph V)
    (hlo : 1 / 2 ≤ G.edgeDensity)
    (hhi : G.edgeDensity ≤ 2 / 3) :
    G.edgeDensity - 4 / 9 -
        (4 / 9) * (1 - 3 * G.edgeDensity / 2) ^ ((3 : ℝ) / 2) ≤
      G.triangleDensity := by
  letI := G.adjDecidable
  have hn : 0 < Fisher.nR G.graph := by
    simp [Fisher.nR, Fisher.cliqueCount_one, Fintype.card_pos]
  apply Fisher.fisher_density_form G.graph hn G.edgeDensity G.triangleDensity
  · simp [edgeDensity, Fisher.eR, Fisher.nR, Fisher.cliqueCount_one,
      Fisher.cliqueCount_two]
  · simp [triangleDensity, Fisher.TR, Fisher.nR, Fisher.cliqueCount_one]
  · exact hlo
  · exact hhi

end DecidableFiniteGraph

/-- A finite graph with its vertex type and all required finite/decidable
instances bundled.  Allowing the vertex type to vary with the approximation
index avoids artificial padding in deterministic blow-up constructions. -/
structure FiniteGraphApprox where
  V : Type u
  fintype : Fintype V
  nonempty : Nonempty V
  decidableEq : DecidableEq V
  graph : SimpleGraph V
  adjDecidable : DecidableRel graph.Adj

namespace FiniteGraphApprox

noncomputable def edgeDensity (G : FiniteGraphApprox) : ℝ := by
  letI := G.fintype
  letI := G.decidableEq
  letI := G.adjDecidable
  exact 2 * (G.graph.edgeFinset.card : ℝ) / (Fintype.card G.V : ℝ) ^ 2

noncomputable def triangleDensity (G : FiniteGraphApprox) : ℝ := by
  letI := G.fintype
  letI := G.decidableEq
  letI := G.adjDecidable
  exact 6 * (Fisher.cliqueCount G.graph 3 : ℝ) / (Fintype.card G.V : ℝ) ^ 3

theorem fisher_density_form
    (G : FiniteGraphApprox)
    (hlo : 1 / 2 ≤ G.edgeDensity)
    (hhi : G.edgeDensity ≤ 2 / 3) :
    G.edgeDensity - 4 / 9 -
        (4 / 9) * (1 - 3 * G.edgeDensity / 2) ^ ((3 : ℝ) / 2) ≤
      G.triangleDensity := by
  letI := G.fintype
  letI := G.nonempty
  letI := G.decidableEq
  letI := G.adjDecidable
  have hn : 0 < Fisher.nR G.graph := by
    simp [Fisher.nR, Fisher.cliqueCount_one, Fintype.card_pos]
  apply Fisher.fisher_density_form G.graph hn G.edgeDensity G.triangleDensity
  · simp [edgeDensity, Fisher.eR, Fisher.nR, Fisher.cliqueCount_one,
      Fisher.cliqueCount_two]
  · simp [triangleDensity, Fisher.TR, Fisher.nR, Fisher.cliqueCount_one]
  · exact hlo
  · exact hhi

end FiniteGraphApprox

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrable real functions admit simple-function approximants in real
`L¹`.  This small wrapper puts Mathlib's sequential approximation theorem in
the existential form used by the deterministic graphon-step construction. -/
private theorem exists_simpleFunc_integral_abs_sub_lt
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (hfmeas : Measurable f) (hfint : Integrable f ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : SimpleFunc α ℝ, ∫ x, |S x - f x| ∂ν < ε := by
  have ht := tendsto_integral_norm_approxOn_sub hfmeas hfint
  have hev : ∀ᶠ n in atTop,
      (∫ x, ‖SimpleFunc.approxOn f hfmeas (Set.range f ∪ {0}) 0
        (by simp) n x - f x‖ ∂ν) < ε :=
    ht.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨SimpleFunc.approxOn f hfmeas (Set.range f ∪ {0}) 0
    (by simp) n, ?_⟩
  simpa [Real.norm_eq_abs] using hn

/-- The jointly measurable `[0,1]`-valued graphon kernel can therefore be
approximated in product-measure `L¹` by a real simple function. -/
private theorem exists_graphon_simpleFunc_L1
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : SimpleFunc (Ω × Ω) ℝ,
      ∫ p, |S p - W p.1 p.2| ∂(μ.prod μ) < ε := by
  have hint : Integrable (Function.uncurry W) (μ.prod μ) := by
    apply Integrable.of_bound hW.meas.aestronglyMeasurable 1
    exact ae_of_all _ fun p => by
      change |W p.1 p.2| ≤ 1
      rw [abs_of_nonneg (hW.nonneg p.1 p.2)]
      exact hW.le_one p.1 p.2
  exact exists_simpleFunc_integral_abs_sub_lt hW.meas hint hε

/-- On a probability space the `L¹` norm is bounded by the `L²` norm, in the
concrete integral form used below. -/
private theorem integral_abs_le_sqrt_integral_sq
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) (C : ℝ)
    (hC : ∀ᵐ x ∂ν, ‖f x‖ ≤ C) :
    (∫ x, |f x| ∂ν) ≤ (∫ x, (f x) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have hf2 : MemLp f (ENNReal.ofReal 2) ν := MemLp.of_bound hf C hC
  have h1 : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal 2) ν :=
    memLp_const 1
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (μ := ν) (f := f) (g := fun _ : α => (1 : ℝ))
    Real.HolderConjugate.two_two hf2 h1
  simpa [Real.norm_eq_abs] using hh

/-- Finitely many finite-range one-variable factors jointly take only
finitely many feature values. -/
private theorem finite_range_paired_feature
    {J : Type u} [Fintype J] (a b : J → Ω → ℝ)
    (ha : ∀ j, (Set.range (a j)).Finite)
    (hb : ∀ j, (Set.range (b j)).Finite) :
    (Set.range (fun x : Ω => fun j => (a j x, b j x))).Finite := by
  let t : J → Set (ℝ × ℝ) := fun j => Set.range (a j) ×ˢ Set.range (b j)
  refine (Set.Finite.pi (fun j => (ha j).prod (hb j))).subset ?_
  rintro f ⟨x, rfl⟩
  simp [Set.mem_pi, t]

/-- A real simple function on the product space admits an `L¹`-close finite
sum of separable measurable rectangle indicators. -/
private theorem exists_simpleFunc_rectangular_finiteRank_data_integral_abs_lt
    (S : SimpleFunc (Ω × Ω) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Ω → Ω → ℝ, ∃ Bnd : ℝ,
    ∃ a b : J → Ω → ℝ,
      GoodK K ∧
      0 ≤ Bnd ∧
      (∀ x y, |K x y| ≤ Bnd) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ j, (Set.range (a j)).Finite) ∧
      (∀ j, (Set.range (b j)).Finite) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) ∧
      (∫ p, |S p - K p.1 p.2| ∂(μ.prod μ)) < ε := by
  classical
  let C : ℝ := (SimpleFunc.range S).sum fun c => |c|
  let A : ℝ := C ^ 2 * (SimpleFunc.range S).card
  let η : ℝ := ε ^ 2 / (A + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (sq_pos_of_pos hε) (by linarith)
  rcases exists_simpleFunc_rectangular_finiteRank_data_integral_sq_bound
      (Ω := Ω) μ S hη with
    ⟨J, hJ, K, Bnd, a, b, hK, hB0, hKB, ha, hb, hfa, hfb, hsep, hsq⟩
  refine ⟨J, hJ, K, Bnd, a, b, hK, hB0, hKB, ha, hb, hfa, hfb, hsep, ?_⟩
  let f : Ω × Ω → ℝ := fun p => S p - K p.1 p.2
  have hfmeas : AEStronglyMeasurable f (μ.prod μ) := by
    exact S.aestronglyMeasurable.sub hK.meas.aestronglyMeasurable
  have hSbound (p : Ω × Ω) : |S p| ≤ C := by
    dsimp [C]
    have hmem : S p ∈ SimpleFunc.range S := S.mem_range_self p
    exact Finset.single_le_sum (fun c _ => abs_nonneg c) hmem
  have hfbound : ∀ᵐ p ∂(μ.prod μ), ‖f p‖ ≤ C + Bnd := by
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hSbound p) (hKB p.1 p.2))
  have hL1 := integral_abs_le_sqrt_integral_sq
    hfmeas (C + Bnd) hfbound
  have hfactor : C ^ 2 * ((SimpleFunc.range S).card * η) < ε ^ 2 := by
    rw [show C ^ 2 * ((SimpleFunc.range S).card * η) =
        A * (ε ^ 2 / (A + 1)) by simp [A, η]; ring]
    have hden : 0 < A + 1 := by linarith
    have heps : 0 < ε ^ 2 := sq_pos_of_pos hε
    field_simp [ne_of_gt hden]
    nlinarith
  have hIlt : (∫ p, (f p) ^ 2 ∂(μ.prod μ)) < ε ^ 2 := by
    exact hsq.trans_lt (by simpa [f, C, A, η] using hfactor)
  have hInonneg : 0 ≤ ∫ p, (f p) ^ 2 ∂(μ.prod μ) :=
    integral_nonneg fun _ => sq_nonneg _
  have hsqrt : Real.sqrt (∫ p, (f p) ^ 2 ∂(μ.prod μ)) < ε :=
    (Real.sqrt_lt' hε).mpr hIlt
  rw [← Real.sqrt_eq_rpow] at hL1
  exact hL1.trans_lt (by simpa [f] using hsqrt)

/-- Every graphon is `L¹`-close to a bounded measurable kernel which factors
through a finite-range one-variable feature map. -/
private theorem exists_graphon_finiteFeature_kernel_L1
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ K : Ω → Ω → ℝ, ∃ Bnd : ℝ,
    ∃ a b : J → Ω → ℝ,
      GoodK K ∧
      0 ≤ Bnd ∧
      (∀ x y, |K x y| ≤ Bnd) ∧
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ j, (Set.range (a j)).Finite) ∧
      (∀ j, (Set.range (b j)).Finite) ∧
      (∀ x y, K x y = (@Finset.univ J hJ).sum
        (fun j : J => a j x * b j y)) ∧
      (Set.range (fun x : Ω => fun j => (a j x, b j x))).Finite ∧
      (∫ p, |K p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)) < ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases exists_graphon_simpleFunc_L1 hW hhalf with ⟨S, hSW⟩
  rcases exists_simpleFunc_rectangular_finiteRank_data_integral_abs_lt
      (μ := μ) S hhalf with
    ⟨J, hJ, K, Bnd, a, b, hK, hB0, hKB, ha, hb, hfa, hfb, hsep, hSK⟩
  refine ⟨J, hJ, K, Bnd, a, b, hK, hB0, hKB, ha, hb, hfa, hfb,
    hsep, finite_range_paired_feature a b hfa hfb, ?_⟩
  have hWint : Integrable (Function.uncurry W) (μ.prod μ) := by
    apply Integrable.of_bound hW.meas.aestronglyMeasurable 1
    exact ae_of_all _ fun p => by
      change |W p.1 p.2| ≤ 1
      rw [abs_of_nonneg (hW.nonneg p.1 p.2)]
      exact hW.le_one p.1 p.2
  let C : ℝ := (SimpleFunc.range S).sum fun c => |c|
  have hSbound (p : Ω × Ω) : |S p| ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun c _ => abs_nonneg c) (S.mem_range_self p)
  have hSint : Integrable (fun p : Ω × Ω => S p) (μ.prod μ) := by
    apply Integrable.of_bound S.aestronglyMeasurable C
    exact ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hSbound p
  have hKint : Integrable (Function.uncurry K) (μ.prod μ) :=
    hK.integrable_prod
  have hleft : Integrable
      (fun p : Ω × Ω => |K p.1 p.2 - W p.1 p.2|) (μ.prod μ) :=
    (hKint.sub hWint).abs
  have hright : Integrable
      (fun p : Ω × Ω =>
        |S p - W p.1 p.2| + |S p - K p.1 p.2|) (μ.prod μ) :=
    (hSint.sub hWint).abs.add (hSint.sub hKint).abs
  have hpoint (p : Ω × Ω) :
      |K p.1 p.2 - W p.1 p.2| ≤
        |S p - W p.1 p.2| + |S p - K p.1 p.2| := by
    calc
      |K p.1 p.2 - W p.1 p.2| ≤
          |K p.1 p.2 - S p| + |S p - W p.1 p.2| :=
        _root_.abs_sub_le (G := ℝ) (K p.1 p.2) (S p) (W p.1 p.2)
      _ = |S p - W p.1 p.2| + |S p - K p.1 p.2| := by
        rw [abs_sub_comm (K p.1 p.2) (S p), add_comm]
  calc
    (∫ p, |K p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)) ≤
        ∫ p, (|S p - W p.1 p.2| + |S p - K p.1 p.2|) ∂(μ.prod μ) := by
          apply integral_mono (μ := μ.prod μ) hleft hright
          intro (p : Ω × Ω)
          exact hpoint p
    _ = (∫ p, |S p - W p.1 p.2| ∂(μ.prod μ)) +
        ∫ p, |S p - K p.1 p.2| ∂(μ.prod μ) := by
          simpa [Real.norm_eq_abs, Function.uncurry] using
            integral_add (hSint.sub hWint).abs (hSint.sub hKint).abs
    _ < ε / 2 + ε / 2 := add_lt_add hSW hSK
    _ = ε := by ring

private def unitClamp (z : ℝ) : ℝ := max 0 (min 1 z)

private theorem unitClamp_nonneg (z : ℝ) : 0 ≤ unitClamp z := by
  exact le_max_left _ _

private theorem unitClamp_le_one (z : ℝ) : unitClamp z ≤ 1 := by
  exact max_le zero_le_one (min_le_left _ _)

private theorem unitClamp_eq_self {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    unitClamp z = z := by
  simp [unitClamp, hz0, hz1]

/-- Projection to `[0,1]` does not increase distance from a point already in
that interval. -/
private theorem abs_unitClamp_sub_le {w z : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |unitClamp z - w| ≤ |z - w| := by
  by_cases hz0 : 0 ≤ z
  · by_cases hz1 : z ≤ 1
    · rw [unitClamp_eq_self hz0 hz1]
    · have h1z : 1 ≤ z := le_of_not_ge hz1
      have hc : unitClamp z = 1 := by simp [unitClamp, hz0, h1z]
      rw [hc, abs_of_nonneg (sub_nonneg.mpr hw1),
        abs_of_nonneg (sub_nonneg.mpr (hw1.trans h1z))]
      linarith
  · have hz : z ≤ 0 := le_of_not_ge hz0
    have hc : unitClamp z = 0 := by simp [unitClamp, hz]
    rw [hc, abs_of_nonpos (sub_nonpos.mpr hw0),
      abs_of_nonpos (sub_nonpos.mpr (hz.trans hw0))]
    linarith

/-- Symmetrize a kernel and project its values to the graphon interval. -/
private noncomputable def graphonize (K : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y =>
  unitClamp ((K x y + K y x) / 2)

private theorem graphonize_isGraphon {K : Ω → Ω → ℝ} (hK : GoodK K) :
    IsGraphon (graphonize K) μ := by
  have hswap : Measurable (fun p : Ω × Ω => K p.2 p.1) :=
    hK.meas.comp measurable_swap
  have havg : Measurable
      (fun p : Ω × Ω => (K p.1 p.2 + K p.2 p.1) / 2) :=
    (hK.meas.add hswap).div_const 2
  refine ⟨?_, fun x y => unitClamp_nonneg _, fun x y => unitClamp_le_one _, ?_⟩
  · exact measurable_const.max (measurable_const.min havg)
  · intro x y
    simp only [graphonize]
    rw [add_comm]

/-- Symmetrizing and clamping cannot increase the product-space `L¹` error
from a graphon. -/
private theorem integral_abs_graphonize_sub_le
    {W K : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hK : GoodK K) :
    (∫ p, |graphonize K p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)) ≤
      ∫ p, |K p.1 p.2 - W p.1 p.2| ∂(μ.prod μ) := by
  let f : Ω × Ω → ℝ := fun p => |K p.1 p.2 - W p.1 p.2|
  have hWint : Integrable (Function.uncurry W) (μ.prod μ) :=
    (goodK_of_isGraphon hW).integrable_prod
  have hKint : Integrable (Function.uncurry K) (μ.prod μ) := hK.integrable_prod
  have hfint : Integrable f (μ.prod μ) := by
    simpa [f, Function.uncurry, Real.norm_eq_abs] using (hKint.sub hWint).abs
  have hswap : (∫ p, f p.swap ∂(μ.prod μ)) = ∫ p, f p ∂(μ.prod μ) := by
    simpa using (integral_prod_swap (μ := μ) (ν := μ) f)
  have hfswap : Integrable (fun p : Ω × Ω => f p.swap) (μ.prod μ) := by
    simpa [Function.comp_def] using hfint.swap
  have hpoint (p : Ω × Ω) :
      |graphonize K p.1 p.2 - W p.1 p.2| ≤ (f p + f p.swap) / 2 := by
    let z := (K p.1 p.2 + K p.2 p.1) / 2
    calc
      |graphonize K p.1 p.2 - W p.1 p.2| =
          |unitClamp z - W p.1 p.2| := by rfl
      _ ≤ |z - W p.1 p.2| :=
        abs_unitClamp_sub_le (hW.nonneg p.1 p.2) (hW.le_one p.1 p.2)
      _ = |((K p.1 p.2 - W p.1 p.2) +
          (K p.2 p.1 - W p.2 p.1)) / 2| := by
            congr 1
            dsimp [z]
            rw [hW.symm p.2 p.1]
            ring
      _ ≤ (f p + f p.swap) / 2 := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact div_le_div_of_nonneg_right
          (by simpa [f] using (abs_add_le
            (K p.1 p.2 - W p.1 p.2) (K p.2 p.1 - W p.2 p.1)))
          (by norm_num)
  have hleft : Integrable
      (fun p : Ω × Ω => |graphonize K p.1 p.2 - W p.1 p.2|) (μ.prod μ) :=
    ((goodK_of_isGraphon (graphonize_isGraphon (μ := μ) hK)).integrable_prod.sub
      hWint).abs
  have hright : Integrable (fun p : Ω × Ω => (f p + f p.swap) / 2)
      (μ.prod μ) :=
    (hfint.add hfswap).div_const 2
  calc
    (∫ p, |graphonize K p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)) ≤
        ∫ p, (f p + f p.swap) / 2 ∂(μ.prod μ) := by
          exact integral_mono hleft hright hpoint
    _ = ((∫ p, f p ∂(μ.prod μ)) + ∫ p, f p.swap ∂(μ.prod μ)) / 2 := by
      rw [integral_div, integral_add hfint hfswap]
    _ = ∫ p, f p ∂(μ.prod μ) := by rw [hswap]; ring
    _ = ∫ p, |K p.1 p.2 - W p.1 p.2| ∂(μ.prod μ) := rfl

/-- Finite-step reduction: an arbitrary graphon is `L¹`-approximated by a
graphon whose value is determined by a finite-range feature at each endpoint. -/
private theorem exists_finiteFeature_graphon_L1
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : Type u, ∃ hJ : Fintype J,
    ∃ a b : J → Ω → ℝ, ∃ U : Ω → Ω → ℝ,
      (∀ j, Good (a j)) ∧
      (∀ j, Good (b j)) ∧
      (∀ j, (Set.range (a j)).Finite) ∧
      (∀ j, (Set.range (b j)).Finite) ∧
      (Set.range (fun x : Ω => fun j => (a j x, b j x))).Finite ∧
      IsGraphon U μ ∧
      (∀ x y, U x y = unitClamp
        (((@Finset.univ J hJ).sum (fun j : J => a j x * b j y) +
          (@Finset.univ J hJ).sum (fun j : J => a j y * b j x)) / 2)) ∧
      (∫ p, |U p.1 p.2 - W p.1 p.2| ∂(μ.prod μ)) < ε := by
  rcases exists_graphon_finiteFeature_kernel_L1 hW hε with
    ⟨J, hJ, K, _Bnd, a, b, hK, _hB0, _hKB, ha, hb, hfa, hfb,
      hsep, hfeature, hKW⟩
  let U := graphonize K
  refine ⟨J, hJ, a, b, U, ha, hb, hfa, hfb, hfeature,
    graphonize_isGraphon (μ := μ) hK, ?_, ?_⟩
  · intro x y
    dsimp [U, graphonize]
    rw [hsep x y, hsep y x]
  · exact (integral_abs_graphonize_sub_le hW hK).trans_lt hKW

/-- Edge density is unchanged when a kernel is pulled back along a measurable
map and the measure is pushed forward along the same map. -/
private theorem edgeDensity_map_pullback
    {Q : Type u} [MeasurableSpace Q] (F : Ω → Q) (hF : Measurable F)
    (H : Q → Q → ℝ) (hH : Measurable (Function.uncurry H)) :
    edgeDensity H (μ.map F) = edgeDensity (fun x y => H (F x) (F y)) μ := by
  letI : IsProbabilityMeasure (μ.map F) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  simp only [edgeDensity, mean, degree]
  rw [integral_map hF.aemeasurable]
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (∫ r, H (F x) r ∂(μ.map F)) = ∫ y, H (F x) (F y) ∂μ
      rw [integral_map hF.aemeasurable]
      exact (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · have hdegMeas : StronglyMeasurable
        (fun q : Q => ∫ r, H q r ∂(μ.map F)) :=
      hH.stronglyMeasurable.integral_prod_right'
    exact hdegMeas.aestronglyMeasurable

/-- The analogous pullback identity for triangle density. -/
private theorem triangleDensity_map_pullback
    {Q : Type u} [MeasurableSpace Q] (F : Ω → Q) (hF : Measurable F)
    (H : Q → Q → ℝ) (hH : IsGraphon H (μ.map F))
    (hU : IsGraphon (fun x y => H (F x) (F y)) μ) :
    trace (μ.map F) (compPow (μ.map F) H 2) =
      trace μ (compPow μ (fun x y => H (F x) (F y)) 2) := by
  letI : IsProbabilityMeasure (μ.map F) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  rw [trace_compPow_two_eq_triangleIntegral hH,
    trace_compPow_two_eq_triangleIntegral hU]
  let T : Q → Q → Q → ℝ := fun q r s => H q r * H r s * H s q
  have hT : Measurable (fun p : (Q × Q) × Q => T p.1.1 p.1.2 p.2) := by
    have hqr : Measurable (fun p : (Q × Q) × Q => H p.1.1 p.1.2) :=
      hH.meas.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst))
    have hrs : Measurable (fun p : (Q × Q) × Q => H p.1.2 p.2) :=
      hH.meas.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hsq : Measurable (fun p : (Q × Q) × Q => H p.2 p.1.1) :=
      hH.meas.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    exact (hqr.mul hrs).mul hsq
  have hinner (q r : Q) :
      (∫ s, T q r s ∂(μ.map F)) = ∫ z, T q r (F z) ∂μ := by
    rw [integral_map hF.aemeasurable]
    exact (hT.comp
      ((measurable_const.prodMk measurable_const).prodMk measurable_id)).aestronglyMeasurable
  simp_rw [show ∀ q r, (∫ s, H q r * H r s * H s q ∂(μ.map F)) =
      ∫ z, H q r * H r (F z) * H (F z) q ∂μ by
        intro q r; exact hinner q r]
  have hmiddle (q : Q) :
      (∫ r, (∫ z, H q r * H r (F z) * H (F z) q ∂μ) ∂(μ.map F)) =
        ∫ y, ∫ z, H q (F y) * H (F y) (F z) * H (F z) q ∂μ ∂μ := by
    change (∫ r, (∫ z, T q r (F z) ∂μ) ∂(μ.map F)) =
      ∫ y, ∫ z, T q (F y) (F z) ∂μ ∂μ
    rw [integral_map hF.aemeasurable]
    have hm : StronglyMeasurable (fun r : Q => ∫ z, T q r (F z) ∂μ) := by
      have hjoint : StronglyMeasurable
          (fun p : Q × Ω => T q p.1 (F p.2)) :=
        (hT.comp (((measurable_const.prodMk measurable_fst).prodMk
          (hF.comp measurable_snd)))).stronglyMeasurable
      exact hjoint.integral_prod_right'
    exact hm.aestronglyMeasurable
  simp_rw [hmiddle]
  rw [integral_map hF.aemeasurable]
  have hout : StronglyMeasurable
      (fun q : Q => ∫ y, ∫ z, T q (F y) (F z) ∂μ ∂μ) := by
    have hall : StronglyMeasurable
        (fun p : (Q × Ω) × Ω => T p.1.1 (F p.1.2) (F p.2)) :=
      (hT.comp (((measurable_fst.comp measurable_fst).prodMk
        (hF.comp (measurable_snd.comp measurable_fst))).prodMk
          (hF.comp measurable_snd))).stronglyMeasurable
    exact hall.integral_prod_right'.integral_prod_right'
  exact hout.aestronglyMeasurable

/-- A finite-feature graphon is the pullback of an honest graphon on a finite
probability space, with exactly the same edge and triangle densities. -/
private theorem exists_finite_model_of_finiteFeature
    {J : Type u} [Fintype J] (a b : J → Ω → ℝ) (U : Ω → Ω → ℝ)
    (ha : ∀ j, Good (a j)) (hb : ∀ j, Good (b j))
    (hfeature : (Set.range
      (fun x : Ω => fun j => (a j x, b j x))).Finite)
    (hU : IsGraphon U μ)
    (hUdef : ∀ x y, U x y = unitClamp
      (((Finset.univ).sum (fun j : J => a j x * b j y) +
        (Finset.univ).sum (fun j : J => a j y * b j x)) / 2)) :
    ∃ Q : Type u, ∃ hQ : Fintype Q, ∃ mQ : MeasurableSpace Q,
    ∃ msQ : @MeasurableSingletonClass Q mQ,
    ∃ ν : @Measure Q mQ, ∃ H : Q → Q → ℝ,
      @IsProbabilityMeasure Q mQ ν ∧
      @IsGraphon Q mQ H ν ∧
      edgeDensity H ν = edgeDensity U μ ∧
      trace ν (compPow ν H 2) = trace μ (compPow μ U 2) := by
  classical
  let F : Ω → (J → ℝ × ℝ) := fun x j => (a j x, b j x)
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro j
    exact (ha j).meas.measurable.prodMk (hb j).meas.measurable
  let Q := Set.range F
  let hQ : Fintype Q := hfeature.fintype
  letI : Fintype Q := hQ
  let FQ : Ω → Q := fun x => ⟨F x, ⟨x, rfl⟩⟩
  have hFQ : Measurable FQ := hF.subtype_mk
  let ν : Measure Q := μ.map FQ
  have hν : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hFQ.aemeasurable
  letI : IsProbabilityMeasure ν := hν
  let H : Q → Q → ℝ := fun q r => unitClamp
    (((Finset.univ).sum (fun j : J => (q.1 j).1 * (r.1 j).2) +
      (Finset.univ).sum (fun j : J => (r.1 j).1 * (q.1 j).2)) / 2)
  have hH : IsGraphon H ν := by
    refine ⟨measurable_of_finite _, fun q r => unitClamp_nonneg _,
      fun q r => unitClamp_le_one _, ?_⟩
    intro q r
    dsimp [H]
    rw [add_comm]
  have hpull : (fun x y => H (FQ x) (FQ y)) = U := by
    funext x y
    dsimp [H, FQ, F]
    exact (hUdef x y).symm
  have hedge := edgeDensity_map_pullback (μ := μ) FQ hFQ H hH.meas
  have htri := triangleDensity_map_pullback (μ := μ) FQ hFQ H hH (by
    simpa [hpull] using hU)
  refine ⟨Q, hQ, inferInstance, inferInstance, ν, H, hν, hH, ?_, ?_⟩
  · simpa [hpull] using hedge
  · simpa [hpull] using htri

/-- Finite weighted graphons are dense for the two densities needed here. -/
private theorem exists_finite_weighted_density_approx
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Type u, ∃ hQ : Fintype Q, ∃ mQ : MeasurableSpace Q,
    ∃ msQ : @MeasurableSingletonClass Q mQ,
    ∃ ν : @Measure Q mQ, ∃ H : Q → Q → ℝ,
      @IsProbabilityMeasure Q mQ ν ∧
      @IsGraphon Q mQ H ν ∧
      |edgeDensity H ν - edgeDensity W μ| < ε ∧
      |trace ν (compPow ν H 2) - trace μ (compPow μ W 2)| < ε := by
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  rcases exists_finiteFeature_graphon_L1 hW hthird with
    ⟨J, hJ, a, b, U, ha, hb, _hfa, _hfb, hfeature, hU, hUdef, hUW⟩
  letI : Fintype J := hJ
  rcases exists_finite_model_of_finiteFeature (μ := μ) a b U ha hb hfeature hU
      hUdef with ⟨Q, hQ, mQ, msQ, ν, H, hν, hH, hedgeEq, htriEq⟩
  letI : MeasurableSpace Q := mQ
  letI : MeasurableSingletonClass Q := msQ
  letI : IsProbabilityMeasure ν := hν
  have hdiffInt : Integrable
      (fun p : Ω × Ω => |U p.1 p.2 - W p.1 p.2|) (μ.prod μ) :=
    (((goodK_of_isGraphon hU).integrable_prod.sub
      (goodK_of_isGraphon hW).integrable_prod).abs)
  have hdist : kernelL1Dist (μ := μ) U W < ε / 3 := by
    rw [kernelL1Dist]
    rw [← integral_prod _ hdiffInt]
    exact hUW
  have hedgeBound := abs_edgeDensity_sub_le_kernelL1Dist hU hW
  have htriBound := abs_triangleDensity_sub_le_three_mul_kernelL1Dist hU hW
  refine ⟨Q, hQ, mQ, msQ, ν, H, hν, hH, ?_, ?_⟩
  · rw [hedgeEq]
    exact hedgeBound.trans_lt (hdist.trans (by linarith))
  · rw [htriEq]
    exact htriBound.trans_lt (by nlinarith)

private theorem finiteGraphKernel_isGraphon_anyMeasure
    {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure V) :
    IsGraphon (finiteGraphKernel G) ν := by
  refine ⟨measurable_of_finite _, ?_, ?_, ?_⟩
  · intro x y
    by_cases h : G.Adj x y <;> simp [finiteGraphKernel, h]
  · intro x y
    by_cases h : G.Adj x y <;> simp [finiteGraphKernel, h]
  · intro x y
    simp only [finiteGraphKernel]
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hyx => h hyx.symm)]

/-- On a fixed finite vertex set, convergence of all atom masses implies
convergence of the edge and triangle densities of a fixed graph kernel. -/
private theorem finiteGraphKernel_density_tendsto_of_atom_masses
    {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (νn : ℕ → Measure V) (ν : Measure V)
    (hνn : ∀ n, IsProbabilityMeasure (νn n))
    (hν : IsProbabilityMeasure ν)
    (hmass : ∀ v, Tendsto (fun n => (νn n).real {v}) atTop
      (𝓝 (ν.real {v}))) :
    Tendsto (fun n => edgeDensity (finiteGraphKernel G) (νn n)) atTop
        (𝓝 (edgeDensity (finiteGraphKernel G) ν)) ∧
      Tendsto (fun n => trace (νn n)
        (compPow (νn n) (finiteGraphKernel G) 2)) atTop
        (𝓝 (trace ν (compPow ν (finiteGraphKernel G) 2))) := by
  letI : IsProbabilityMeasure ν := hν
  let K := finiteGraphKernel G
  have hK (ρ : Measure V) : IsGraphon K ρ :=
    finiteGraphKernel_isGraphon_anyMeasure G ρ
  have hedgeFormula (ρ : Measure V) [IsProbabilityMeasure ρ] :
      edgeDensity K ρ =
        ∑ x : V, ρ.real {x} * ∑ y : V, ρ.real {y} * K x y := by
    simp only [edgeDensity, mean, degree]
    have hout : Integrable (fun x => ∫ y, K x y ∂ρ) ρ := by
      change Integrable (degree K ρ) ρ
      exact Good.integrable (μ := ρ) (good_degree (μ := ρ) (hK ρ))
    rw [integral_fintype hout]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [integral_fintype ((goodK_of_isGraphon (hK ρ)).integrable_row x)]
    simp [smul_eq_mul]
  have htriFormula (ρ : Measure V) [IsProbabilityMeasure ρ] :
      trace ρ (compPow ρ K 2) =
        ∑ x : V, ρ.real {x} * ∑ y : V, ρ.real {y} *
          ∑ z : V, ρ.real {z} * (K x y * K y z * K z x) := by
    rw [trace_compPow_two_eq_triangleIntegral (hK ρ)]
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply congrArg (fun t : ℝ => ρ.real {x} * t)
    apply Finset.sum_congr rfl
    intro y _hy
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul]
  constructor
  · have hform : ∀ n, edgeDensity K (νn n) =
        ∑ x : V, (νn n).real {x} *
          ∑ y : V, (νn n).real {y} * K x y := by
      intro n
      letI := hνn n
      exact hedgeFormula (νn n)
    rw [show (fun n => edgeDensity K (νn n)) = fun n =>
      ∑ x : V, (νn n).real {x} *
        ∑ y : V, (νn n).real {y} * K x y by funext n; exact hform n]
    rw [hedgeFormula (ρ := ν)]
    apply tendsto_finset_sum
    intro x _hx
    apply (hmass x).mul
    apply tendsto_finset_sum
    intro y _hy
    exact (hmass y).mul tendsto_const_nhds
  · have hform : ∀ n, trace (νn n) (compPow (νn n) K 2) =
        ∑ x : V, (νn n).real {x} * ∑ y : V, (νn n).real {y} *
          ∑ z : V, (νn n).real {z} * (K x y * K y z * K z x) := by
      intro n
      letI := hνn n
      exact htriFormula (νn n)
    rw [show (fun n => trace (νn n) (compPow (νn n) K 2)) = fun n =>
      ∑ x : V, (νn n).real {x} * ∑ y : V, (νn n).real {y} *
        ∑ z : V, (νn n).real {z} * (K x y * K y z * K z x) by
          funext n; exact hform n]
    rw [htriFormula (ρ := ν)]
    apply tendsto_finset_sum
    intro x _hx
    apply (hmass x).mul
    apply tendsto_finset_sum
    intro y _hy
    apply (hmass y).mul
    apply tendsto_finset_sum
    intro z _hz
    exact (hmass z).mul tendsto_const_nhds

/-- A finite `0/1` graphon with arbitrary atom weights is approximated by
uniform blow-ups of its underlying simple graph. -/
private theorem exists_uniform_blowup_density_approximants
    {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : Measure V) [IsProbabilityMeasure ν] :
    ∃ A : ℕ → FiniteGraphApprox.{u},
      Tendsto (fun n => (A n).edgeDensity) atTop
          (𝓝 (edgeDensity (finiteGraphKernel G) ν)) ∧
      Tendsto (fun n => (A n).triangleDensity) atTop
          (𝓝 (trace ν (compPow ν (finiteGraphKernel G) 2))) := by
  classical
  let p : V → ℝ := fun v => ν.real {v}
  let c : ℕ → V → ℕ := fun n v => ⌊p v * n⌋₊ + 1
  let X : ℕ → Type u := fun n => Σ v : V, Fin (c n v)
  let mX : (n : ℕ) → MeasurableSpace (X n) := fun _ => ⊤
  letI (n : ℕ) : MeasurableSpace (X n) := mX n
  letI (n : ℕ) : MeasurableSingletonClass (X n) := ⟨fun _ => by simp⟩
  let graph : (n : ℕ) → SimpleGraph (X n) := fun n => G.comap Sigma.fst
  have hXnonempty (n : ℕ) : Nonempty (X n) := by
    let v : V := Classical.choice inferInstance
    exact ⟨⟨v, ⟨0, by simp [c]⟩⟩⟩
  let νn : ℕ → Measure V := fun n => by
    letI : Nonempty (X n) := hXnonempty n
    exact (finiteUniformMeasure (V := X n)).map Sigma.fst
  have hνn (n : ℕ) : IsProbabilityMeasure (νn n) := by
    letI : Nonempty (X n) := hXnonempty n
    exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  have hfiberCard (n : ℕ) (v : V) :
      Nat.card (↑({x : X n | x.1 = v} : Set (X n))) = c n v := by
    let e : (↑({x : X n | x.1 = v} : Set (X n))) ≃ Fin (c n v) := {
      toFun := fun x => Fin.cast (congrArg (c n)
        (show x.1.1 = v from x.property)) x.1.2
      invFun k := ⟨⟨v, k⟩, rfl⟩
      left_inv x := by
        rcases x with ⟨⟨w, k⟩, hw⟩
        change w = v at hw
        subst w
        rfl
      right_inv _ := rfl }
    exact (Nat.card_congr e).trans (Nat.card_fin _)
  have hmassFormula (n : ℕ) (v : V) :
      (νn n).real {v} = (c n v : ℝ) / Fintype.card (X n) := by
    letI : Nonempty (X n) := hXnonempty n
    have hmap : νn n {v} = finiteUniformMeasure (V := X n)
        ((Sigma.fst : X n → V) ⁻¹' ({v} : Set V)) := by
      exact Measure.map_apply_of_aemeasurable
        (measurable_of_finite _).aemeasurable (MeasurableSet.singleton v)
    rw [measureReal_def, hmap, finiteUniformMeasure,
      PMF.toMeasure_uniformOfFintype_apply]
    rw [ENNReal.toReal_div]
    · simp only [ENNReal.toReal_natCast]
      congr 1
      have hcpre : Fintype.card
          ((Sigma.fst : X n → V) ⁻¹' ({v} : Set V)) = c n v := by
        have hset : ((Sigma.fst : X n → V) ⁻¹' ({v} : Set V)) =
            {x : X n | x.1 = v} := by
          ext x
          change (x.1 = v) ↔ (x.1 = v)
          rfl
        rw [hset]
        rw [Fintype.card_eq_nat_card]
        exact hfiberCard n v
      exact_mod_cast hcpre
    · simp
  have hp0 (v : V) : 0 ≤ p v := by simp [p]
  have hcdiv (v : V) : Tendsto (fun n => (c n v : ℝ) / n) atTop (𝓝 (p v)) := by
    have hfloor := tendsto_nat_floor_mul_div_atTop (R := ℝ) (hp0 v)
    have hfloorNat := hfloor.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hone := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    convert hfloorNat.add hone using 1 <;> simp [c, add_div]
  have hpsum : ∑ v : V, p v = 1 := by
    simpa [p] using (Measure.sum_measureReal_singleton (μ := ν))
  have hcarddiv : Tendsto (fun n => (Fintype.card (X n) : ℝ) / n)
      atTop (𝓝 1) := by
    have hs := tendsto_finset_sum (s := (Finset.univ : Finset V))
      (fun v _ => hcdiv v)
    simpa [X, Fintype.card_sigma, div_eq_mul_inv, Finset.sum_mul, hpsum] using hs
  have hmass (v : V) : Tendsto (fun n => (νn n).real {v}) atTop
      (𝓝 (ν.real {v})) := by
    have hratio := (hcdiv v).div hcarddiv (by norm_num)
    have hr : Tendsto
        ((fun n => (c n v : ℝ) / n) /
          fun n => (Fintype.card (X n) : ℝ) / n) atTop (𝓝 (p v)) := by
      simpa using hratio
    apply hr.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hmassFormula]
    simp only [Pi.div_apply]
    field_simp [Nat.ne_of_gt hn]
  obtain ⟨hedge, htri⟩ := finiteGraphKernel_density_tendsto_of_atom_masses
    G νn ν hνn inferInstance hmass
  let A : ℕ → FiniteGraphApprox.{u} := fun n => by
    letI : Nonempty (X n) := hXnonempty n
    exact {
      V := X n
      fintype := inferInstance
      nonempty := inferInstance
      decidableEq := inferInstance
      graph := graph n
      adjDecidable := inferInstance }
  refine ⟨A, ?_, ?_⟩
  · -- Pullback along `Sigma.fst` identifies the uniform blow-up density with
    -- the density of `G` under the pushed-forward empirical atom measure.
    have hid (n : ℕ) : (A n).edgeDensity =
        edgeDensity (finiteGraphKernel G) (νn n) := by
      letI : Nonempty (X n) := hXnonempty n
      letI : IsProbabilityMeasure (νn n) := hνn n
      have hkern : finiteGraphKernel (graph n) =
          fun x y : X n => finiteGraphKernel G x.1 y.1 := by
        funext x y
        simp [finiteGraphKernel, graph, SimpleGraph.comap_adj]
      calc
        (A n).edgeDensity = edgeDensity (finiteGraphKernel (graph n))
            (finiteUniformMeasure (V := X n)) := by
          rw [edgeDensity_finiteGraphKernel]
          simp [A, FiniteGraphApprox.edgeDensity]
        _ = edgeDensity (fun x y : X n => finiteGraphKernel G x.1 y.1)
            (finiteUniformMeasure (V := X n)) := by rw [hkern]
        _ = edgeDensity (finiteGraphKernel G) (νn n) := by
          symm
          simpa [νn] using edgeDensity_map_pullback
            (μ := finiteUniformMeasure (V := X n))
            (Sigma.fst : X n → V) (measurable_of_finite _)
            (finiteGraphKernel G)
            (finiteGraphKernel_isGraphon_anyMeasure G (νn n)).meas
    exact hedge.congr' (Filter.Eventually.of_forall fun n => (hid n).symm)
  · have hid (n : ℕ) : (A n).triangleDensity =
        trace (νn n) (compPow (νn n) (finiteGraphKernel G) 2) := by
      letI : Nonempty (X n) := hXnonempty n
      letI : IsProbabilityMeasure (νn n) := hνn n
      have hkern : finiteGraphKernel (graph n) =
          fun x y : X n => finiteGraphKernel G x.1 y.1 := by
        funext x y
        simp [finiteGraphKernel, graph, SimpleGraph.comap_adj]
      calc
        (A n).triangleDensity = trace (finiteUniformMeasure (V := X n))
            (compPow (finiteUniformMeasure (V := X n))
              (finiteGraphKernel (graph n)) 2) := by
          rw [triangleDensity_finiteGraphKernel]
          simp [A, FiniteGraphApprox.triangleDensity]
        _ = trace (finiteUniformMeasure (V := X n))
            (compPow (finiteUniformMeasure (V := X n))
              (fun x y : X n => finiteGraphKernel G x.1 y.1) 2) := by rw [hkern]
        _ = trace (νn n) (compPow (νn n) (finiteGraphKernel G) 2) := by
          symm
          simpa [νn] using triangleDensity_map_pullback
            (μ := finiteUniformMeasure (V := X n))
            (Sigma.fst : X n → V) (measurable_of_finite _)
            (finiteGraphKernel G)
            (finiteGraphKernel_isGraphon_anyMeasure G (νn n))
            (finiteGraphKernel_isGraphon_anyMeasure (graph n)
              (finiteUniformMeasure (V := X n)))
    exact htri.congr' (Filter.Eventually.of_forall fun n => (hid n).symm)

/-- Every finite weighted graphon can be approximated, for the edge and
triangle densities, by one finite simple graph with uniform vertex weights. -/
private theorem exists_finiteGraph_density_close_of_finite_weighted
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (ν : Measure Q) [IsProbabilityMeasure ν]
    {H : Q → Q → ℝ} (hH : IsGraphon H ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : FiniteGraphApprox.{u},
      |A.edgeDensity - edgeDensity H ν| < ε ∧
      |A.triangleDensity - trace ν (compPow ν H 2)| < ε := by
  classical
  letI : Nonempty Q := nonempty_of_isProbabilityMeasure ν
  rcases roundingGraph_density_tendsto hH with ⟨hedgeRound, htriRound⟩
  rcases Metric.tendsto_atTop.1 hedgeRound (ε / 2) (by linarith) with
    ⟨ne, hne⟩
  rcases Metric.tendsto_atTop.1 htriRound (ε / 2) (by linarith) with
    ⟨nt, hnt⟩
  let n := max ne nt
  have hedgeN :
      |edgeDensity (finiteGraphKernel (roundingGraph H n))
          (roundingMeasure ν n) - edgeDensity H ν| < ε / 2 := by
    simpa [Real.dist_eq] using hne n (le_max_left _ _)
  have htriN :
      |trace (roundingMeasure ν n)
          (compPow (roundingMeasure ν n)
            (finiteGraphKernel (roundingGraph H n)) 2) -
          trace ν (compPow ν H 2)| < ε / 2 := by
    simpa [Real.dist_eq] using hnt n (le_max_right _ _)
  let G := roundingGraph H n
  let ρ := roundingMeasure ν n
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : IsProbabilityMeasure ρ := by
    exact roundingMeasure_isProbability ν n
  rcases exists_uniform_blowup_density_approximants G ρ with
    ⟨A, hedgeA, htriA⟩
  rcases Metric.tendsto_atTop.1 hedgeA (ε / 2) (by linarith) with
    ⟨me, hme⟩
  rcases Metric.tendsto_atTop.1 htriA (ε / 2) (by linarith) with
    ⟨mt, hmt⟩
  let m := max me mt
  refine ⟨A m, ?_, ?_⟩
  · have hclose :
        |(A m).edgeDensity - edgeDensity (finiteGraphKernel G) ρ| < ε / 2 := by
      simpa [Real.dist_eq] using hme m (le_max_left _ _)
    dsimp [G, ρ] at hclose
    calc
      |(A m).edgeDensity - edgeDensity H ν| ≤
          |(A m).edgeDensity -
            edgeDensity (finiteGraphKernel (roundingGraph H n))
              (roundingMeasure ν n)| +
          |edgeDensity (finiteGraphKernel (roundingGraph H n))
              (roundingMeasure ν n) - edgeDensity H ν| := by
            exact abs_sub_le _ _ _
      _ < ε := by linarith
  · have hclose :
        |(A m).triangleDensity -
          trace ρ (compPow ρ (finiteGraphKernel G) 2)| < ε / 2 := by
      simpa [Real.dist_eq] using hmt m (le_max_right _ _)
    dsimp [G, ρ] at hclose
    calc
      |(A m).triangleDensity - trace ν (compPow ν H 2)| ≤
          |(A m).triangleDensity -
            trace (roundingMeasure ν n)
              (compPow (roundingMeasure ν n)
                (finiteGraphKernel (roundingGraph H n)) 2)| +
          |trace (roundingMeasure ν n)
              (compPow (roundingMeasure ν n)
                (finiteGraphKernel (roundingGraph H n)) 2) -
            trace ν (compPow ν H 2)| := by
              exact abs_sub_le _ _ _
      _ < ε := by linarith

/-- The edge and triangle densities of finite graph samples converge to those
of the graphon.  This is the precise finite-sampling theorem required by the
Fisher transfer; no cut-distance or graphon quotient infrastructure is needed
downstream. -/
theorem exists_finiteGraph_density_approximants
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    ∃ G : ℕ → FiniteGraphApprox.{u},
      Tendsto (fun n => (G n).edgeDensity) atTop (𝓝 (edgeDensity W μ)) ∧
      Tendsto (fun n => (G n).triangleDensity) atTop
        (𝓝 (trace μ (compPow μ W 2))) := by
  classical
  have hexists (n : ℕ) : ∃ A : FiniteGraphApprox.{u},
      |A.edgeDensity - edgeDensity W μ| <
          2 * ((1 : ℝ) / (n + 1)) ∧
      |A.triangleDensity - trace μ (compPow μ W 2)| <
          2 * ((1 : ℝ) / (n + 1)) := by
    have hε : 0 < (1 : ℝ) / (n + 1) := by positivity
    rcases exists_finite_weighted_density_approx hW hε with
      ⟨Q, hQ, mQ, msQ, ν, H, hν, hH, hedgeH, htriH⟩
    letI : Fintype Q := hQ
    letI : MeasurableSpace Q := mQ
    letI : MeasurableSingletonClass Q := msQ
    letI : IsProbabilityMeasure ν := hν
    letI : DecidableEq Q := Classical.decEq Q
    rcases exists_finiteGraph_density_close_of_finite_weighted ν hH hε with
      ⟨A, hedgeA, htriA⟩
    refine ⟨A, ?_, ?_⟩
    · calc
        |A.edgeDensity - edgeDensity W μ| ≤
            |A.edgeDensity - edgeDensity H ν| +
              |edgeDensity H ν - edgeDensity W μ| := by
                exact abs_sub_le _ _ _
        _ < 2 * ((1 : ℝ) / (n + 1)) := by linarith
    · calc
        |A.triangleDensity - trace μ (compPow μ W 2)| ≤
            |A.triangleDensity - trace ν (compPow ν H 2)| +
              |trace ν (compPow ν H 2) - trace μ (compPow μ W 2)| := by
                exact abs_sub_le _ _ _
        _ < 2 * ((1 : ℝ) / (n + 1)) := by linarith
  let G : ℕ → FiniteGraphApprox.{u} := fun n => Classical.choose (hexists n)
  have hG (n : ℕ) :
      |(G n).edgeDensity - edgeDensity W μ| <
          2 * ((1 : ℝ) / (n + 1)) ∧
      |(G n).triangleDensity - trace μ (compPow μ W 2)| <
          2 * ((1 : ℝ) / (n + 1)) :=
    Classical.choose_spec (hexists n)
  have hzero : Tendsto (fun n : ℕ => 2 * ((1 : ℝ) / (n + 1)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  refine ⟨G, ?_, ?_⟩
  · apply Metric.tendsto_atTop.2
    intro ε hε
    rcases Metric.tendsto_atTop.1 hzero ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hb := hN n hn
    have hg := (hG n).1
    rw [Real.dist_eq]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hb
    exact hg.trans hb
  · apply Metric.tendsto_atTop.2
    intro ε hε
    rcases Metric.tendsto_atTop.1 hzero ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hb := hN n hn
    have hg := (hG n).2
    rw [Real.dist_eq]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hb
    exact hg.trans hb

end OddCycleBound
