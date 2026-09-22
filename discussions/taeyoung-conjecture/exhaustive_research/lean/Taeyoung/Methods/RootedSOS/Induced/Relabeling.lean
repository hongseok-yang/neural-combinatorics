import Taeyoung.Methods.RootedSOS.Induced.Patterns
import Taeyoung.Foundation.Relabeling

/-! Relabelling induced patterns and completing unspecified edges. -/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {E F U : Type*} [Fintype E] [Fintype F] [Fintype U]
  [DecidableEq E] [DecidableEq F] [DecidableEq U]

theorem patternWeight_sum (w : F ⊕ U → Real) (p : F → Fin 2) (q : U → Fin 2) :
    patternWeight w (Sum.elim p q) =
      patternWeight (fun i => w (.inl i)) p * patternWeight (fun j => w (.inr j)) q := by
  simp [patternWeight, Fintype.prod_sum_type]

theorem patternWeight_reindex (e : E ≃ F) (w : F → Real) (p : F → Fin 2) :
    patternWeight (fun i => w (e i)) (fun i => p (e i)) = patternWeight w p :=
  e.prod_comp (fun i => bitWeight (w i) (p i))

/-- Enumerate only the free bits, while keeping every prescribed bit fixed. -/
theorem patternWeight_completions (e : F ⊕ U ≃ E) (w : E → Real) (p : F → Fin 2) :
    (∑ q : U → Fin 2, patternWeight w (fun i => Sum.elim p q (e.symm i))) =
      patternWeight (fun i => w (e (.inl i))) p := by
  have h (q : U → Fin 2) :
      patternWeight w (fun i => Sum.elim p q (e.symm i)) =
        patternWeight (fun i => w (e (.inl i))) p *
          patternWeight (fun i => w (e (.inr i))) q := by
    rw [← patternWeight_reindex e]
    simp only [Equiv.symm_apply_apply]
    exact patternWeight_sum _ _ _
  simp_rw [h]
  rw [← Finset.mul_sum, sum_patternWeight, mul_one]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']

theorem inducedWeight_relabel (a : E → V × V) (b : F → V' × V')
    (p : E → Fin 2) (q : F → Fin 2) (v : V ≃ V') (e : E ≃ F)
    (hbits : ∀ i, p i = q (e i))
    (hpairs : ∀ i,
      (v (a i).1 = (b (e i)).1 ∧ v (a i).2 = (b (e i)).2) ∨
      (v (a i).1 = (b (e i)).2 ∧ v (a i).2 = (b (e i)).1))
    (W : Taeyoung.Graphon Ω μ) (z : V' → Ω) :
    inducedWeight a p W (fun i => z (v i)) = inducedWeight b q W z := by
  unfold inducedWeight
  rw [← patternWeight_reindex e]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  rw [hbits]
  rcases hpairs i with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2,W.symm]

theorem inducedDensity_relabel (a : E → V × V) (b : F → V' × V')
    (p : E → Fin 2) (q : F → Fin 2) (v : V ≃ V') (e : E ≃ F)
    (hbits : ∀ i, p i = q (e i))
    (hpairs : ∀ i,
      (v (a i).1 = (b (e i)).1 ∧ v (a i).2 = (b (e i)).2) ∨
      (v (a i).1 = (b (e i)).2 ∧ v (a i).2 = (b (e i)).1))
    (W : Taeyoung.Graphon Ω μ) : inducedDensity a p W = inducedDensity b q W := by
  let t : (V' → Ω) ≃ᵐ (V → Ω) :=
    MeasurableEquiv.piCongrLeft (fun _ : V => Ω) v.symm
  have ht : MeasurePreserving t (Taeyoung.assignmentMeasure V' μ)
      (Taeyoung.assignmentMeasure V μ) := by
    simpa [t, Taeyoung.assignmentMeasure] using
      (measurePreserving_piCongrLeft (α := fun _ : V => Ω) (fun _ : V => μ) v.symm)
  simp only [inducedDensity]
  rw [← ht.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with z
  have htz : t z = fun i => z (v i) := by
    funext i
    simp [t, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [htz]
  exact inducedWeight_relabel a b p q v e hbits hpairs W z

/-- Base-two codes are an exhaustive, nonduplicating enumeration of patterns. -/
theorem sum_inducedDensity_codes {n : Nat} (pairs : Fin n → V × V)
    (W : Taeyoung.Graphon Ω μ) :
    (∑ code : Fin (2^n), inducedDensity pairs (finFunctionFinEquiv.symm code) W) = 1 := by
  rw [finFunctionFinEquiv.symm.sum_comp (fun p => inducedDensity pairs p W)]
  exact sum_inducedDensity pairs W

end Taeyoung.Methods.RootedSOS.Induced
