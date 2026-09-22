import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Coloring

/-! The admissible range `[1/2, 5/8]` of Atlas 171, where the catalogue target is
already nonpositive and no certificate is needed. The compact S4 pieces cover
`[5/8, 2/3]` and `[2/3, 1]`. -/

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Low

open MeasureTheory Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `target171 p = p * (2p - 1) * (11p³ - 20p² + 13p - 3)` is nonpositive on
`[1/2, 5/8]`. The cubic factor is strictly increasing, because

    (11p³ - 20p² + 13p - 3) + 1/512 = (p - 5/8) * (11 * (p - 105/176)² + 2483/2816),

so on `p ≤ 5/8` it is at most its value `-1/512` at the right endpoint, while the
two remaining factors are nonnegative on `1/2 ≤ p`. -/
theorem target_nonpos {p : Real} (hp : (1 : Real)/2 ≤ p) (hp1 : p ≤ (5 : Real)/8) :
    target171 p ≤ 0 := by
  have hu : (0 : Real) ≤ 5/8 - p := by linarith
  have hsq : (0 : Real) ≤ 11 * (p - 105/176)^2 := by positivity
  have hQ : 11*p^3 - 20*p^2 + 13*p - 3 ≤ 0 := by
    nlinarith [mul_nonneg hu hsq]
  have h0 : (0 : Real) ≤ p := by linarith
  have h2 : (0 : Real) ≤ 2*p - 1 := by linarith
  have hprod : (0 : Real) ≤ p * (2*p - 1) * (-(11*p^3 - 20*p^2 + 13*p - 3)) :=
    mul_nonneg (mul_nonneg h0 h2) (by linarith)
  unfold target171
  nlinarith [hprod]

/-- The Atlas 171 catalogue bound on `[1/2, 5/8]`, in the statement shape the row
assembler expects of an interval piece. -/
theorem graphon_bound (W : Graphon Ω μ)
    (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) (hp1 : cliqueDensity 2 W ≤ (5 : Real)/8) :
    target171 (cliqueDensity 2 W) ≤ homDensity graph171 W :=
  le_trans (target_nonpos hp hp1) (homDensity_nonneg graph171 W)

#print axioms graphon_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Low
