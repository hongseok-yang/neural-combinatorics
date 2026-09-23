import Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Coloring

/-! The admissible range `[1/2, 7/12]` of Atlas 174, where the catalogue target is
already nonpositive and no certificate is needed. The compact S4 pieces cover
`[7/12, 2/3]` and `[2/3, 1]`. -/

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Low

open MeasureTheory Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `target174 p = p * (2p - 1) * (13p³ - 25p² + 17p - 4)` is nonpositive on
`[1/2, 7/12]`. The cubic factor is strictly increasing, because

    (13p³ - 25p² + 17p - 4) + 17/1728 = (p - 7/12) * (13 * (p - 209/312)² + 7539/7488),

so on `p ≤ 7/12` it is at most its value `-17/1728` at the right endpoint, while
the two remaining factors are nonnegative on `1/2 ≤ p`. -/
theorem target_nonpos {p : Real} (hp : (1 : Real)/2 ≤ p) (hp1 : p ≤ (7 : Real)/12) :
    target174 p ≤ 0 := by
  have hu : (0 : Real) ≤ 7/12 - p := by linarith
  have hsq : (0 : Real) ≤ 13 * (p - 209/312)^2 := by positivity
  have hQ : 13*p^3 - 25*p^2 + 17*p - 4 ≤ 0 := by
    nlinarith [mul_nonneg hu hsq]
  have h0 : (0 : Real) ≤ p := by linarith
  have h2 : (0 : Real) ≤ 2*p - 1 := by linarith
  have hprod : (0 : Real) ≤ p * (2*p - 1) * (-(13*p^3 - 25*p^2 + 17*p - 4)) :=
    mul_nonneg (mul_nonneg h0 h2) (by linarith)
  unfold target174
  nlinarith [hprod]

/-- The Atlas 174 catalogue bound on `[1/2, 7/12]`, in the statement shape the row
assembler expects of an interval piece. -/
theorem graphon_bound (W : Graphon Ω μ)
    (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) (hp1 : cliqueDensity 2 W ≤ (7 : Real)/12) :
    target174 (cliqueDensity 2 W) ≤ homDensity graph174 W :=
  le_trans (target_nonpos hp hp1) (homDensity_nonneg graph174 W)

#print axioms graphon_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Low
