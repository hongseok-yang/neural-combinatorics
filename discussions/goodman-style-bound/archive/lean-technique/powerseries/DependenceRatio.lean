import OddCycleBound.Fisher.DependencePolynomial
import OddCycleBound.Fisher.PowerSeriesPositivity

/-!
# Coefficientwise positivity of dependence-polynomial ratios

For every induced subgraph `G[S]` of a finite graph `G`, the formal power
series `D_{G[S]} / D_G` has nonnegative coefficients.  The proof follows the
vertex-deletion recurrence and expands one deletion step as a geometric sum.
-/

namespace Fisher

open SimpleGraph Finset Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The dependence polynomial regarded as a formal power series. -/
noncomputable def depSeries : PowerSeries ℝ :=
  (depPoly G : PowerSeries ℝ)

@[simp] theorem depSeries_coeff (n : ℕ) :
    PowerSeries.coeff n (depSeries G) = (depPoly G).coeff n := by
  simp [depSeries]

@[simp] theorem depSeries_constantCoeff :
    PowerSeries.constantCoeff (depSeries G) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [depPoly_coeff_zero]

theorem depSeries_iso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (f : G ≃g H) :
    depSeries G = depSeries H := by
  simp only [depSeries, depPoly_iso G f]

/-- Vertex deletion, now as an identity of formal power series. -/
theorem depSeries_delete_vertex (v : V) :
    depSeries G =
      depSeries (G.induce (↑(Finset.univ.erase v) : Set V)) -
        PowerSeries.X * depSeries (G.induce (↑(commonNbhd G {v}) : Set V)) := by
  change (depPoly G : PowerSeries ℝ) =
    (depPoly (G.induce (↑(Finset.univ.erase v) : Set V)) : PowerSeries ℝ) -
      PowerSeries.X *
        (depPoly (G.induce (↑(commonNbhd G {v}) : Set V)) : PowerSeries ℝ)
  rw [← Polynomial.coe_X, ← Polynomial.coe_mul, ← Polynomial.coe_sub,
    Polynomial.coe_inj]
  exact depPoly_delete_vertex G v

private def induceFinsetUnivIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    G.induce (↑(Finset.univ : Finset V) : Set V) ≃g G where
  toEquiv :=
    ({ toFun := fun x : (↑(Finset.univ : Finset V) : Set V) => x.1
       invFun := fun x : V => ⟨x, Finset.mem_univ x⟩
       left_inv := fun x => Subtype.ext (by rfl)
       right_inv := fun _ => rfl } :
      (↑(Finset.univ : Finset V) : Set V) ≃ V)
  map_rel_iff' := Iff.rfl

/-- Every induced-subgraph ratio `D_{G[S]} / D_G` has nonnegative formal
power-series coefficients. -/
theorem depSeriesRatioNonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ S : Finset V,
      PowerSeries.CoeffNonneg
        (depSeries (G.induce (↑S : Set V)) * (depSeries G)⁻¹) := by
  classical
  intro S
  by_cases hS : S = Finset.univ
  · subst S
    have he := depSeries_iso
      (G.induce (↑(Finset.univ : Finset V) : Set V))
      (induceFinsetUnivIso G)
    rw [he, PowerSeries.mul_inv_cancel (depSeries G) (by simp)]
    exact PowerSeries.coeffNonneg_one
  · obtain ⟨v, hv⟩ : ∃ v : V, v ∉ S := by
      simpa [Finset.eq_univ_iff_forall] using hS
    let D : Finset V := Finset.univ.erase v
    let H := G.induce (↑D : Set V)
    have hSD : S ⊆ D := by
      intro x hx
      change x ∈ Finset.univ.erase v
      rw [Finset.mem_erase]
      exact ⟨fun hxv => hv (hxv ▸ hx), Finset.mem_univ x⟩
    let S' : Finset (↑D : Set V) := S.subtype fun x => x ∈ D
    let eS : G.induce (↑S : Set V) ≃g
        H.induce (↑S' : Set (↑D : Set V)) := induceSubsetIso G hSD
    let T : Finset V := commonNbhd G {v}
    let K := G.induce (↑T : Set V)
    have hTD : T ⊆ D := by
      intro x hx
      change x ∈ commonNbhd G {v} at hx
      rw [commonNbhd, Finset.mem_filter] at hx
      change x ∈ Finset.univ.erase v
      rw [Finset.mem_erase]
      exact ⟨by simpa using hx.2.1, Finset.mem_univ x⟩
    let T' : Finset (↑D : Set V) := T.subtype fun x => x ∈ D
    let eT : K ≃g H.induce (↑T' : Set (↑D : Set V)) :=
      induceSubsetIso G hTD
    have hDcard : D.card < Fintype.card V := by
      simpa [D] using
        (Finset.card_erase_lt_of_mem (s := (Finset.univ : Finset V))
          (Finset.mem_univ v))
    have ihH := depSeriesRatioNonneg H
    have hSH0 := ihH S'
    have hSH : PowerSeries.CoeffNonneg
        (depSeries (G.induce (↑S : Set V)) * (depSeries H)⁻¹) := by
      rw [depSeries_iso (G.induce (↑S : Set V)) eS]
      exact hSH0
    have hKH0 := ihH T'
    have hKH : PowerSeries.CoeffNonneg
        (depSeries K * (depSeries H)⁻¹) := by
      rw [depSeries_iso K eT]
      exact hKH0
    have hHG : PowerSeries.CoeffNonneg
        (depSeries H * (depSeries G)⁻¹) := by
      apply PowerSeries.coeffNonneg_mul_inv_of_eq_sub_X_mul
        (A := depSeries H) (B := depSeries K)
      · simp
      · simpa [H, D, K, T] using depSeries_delete_vertex G v
      · exact hKH
    exact PowerSeries.coeffNonneg_ratio_trans (by simp :
      PowerSeries.constantCoeff (depSeries H) ≠ 0) hSH hHG
termination_by Fintype.card V
decreasing_by
  simpa [H, D] using hDcard

/-- In particular, the reciprocal dependence polynomial itself has
nonnegative coefficients. -/
theorem depSeries_inv_coeffNonneg :
    PowerSeries.CoeffNonneg (depSeries G)⁻¹ := by
  have h := depSeriesRatioNonneg G (∅ : Finset V)
  have hempty :
      depSeries (G.induce (↑(∅ : Finset V) : Set V)) = 1 := by
    ext n
    simp [depSeries, depPoly, cliqueCount_zero]
  simpa [hempty] using h

end Fisher
