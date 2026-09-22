import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Coloring

/-! The admissible range `[1/2, 3/5]` of Atlas 153, where the catalogue target is
already nonpositive and no certificate is needed. The compact S4 pieces cover
`[3/5, 2/3]` and `[2/3, 1]`. -/

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Low

open MeasureTheory Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `target153 p = p * (2p - 1) * (7p³ - 12p² + 8p - 2)` is nonpositive on
`[1/2, 3/5]`. The cubic factor is strictly increasing, because

    (7p³ - 12p² + 8p - 2) + 1/125 = (p - 3/5) * (7 * (p - 39/70)² + 803/700),

so on `p ≤ 3/5` it is at most its value `-1/125` at the right endpoint, while the
two remaining factors are nonnegative on `1/2 ≤ p`. -/
theorem target_nonpos {p : Real} (hp : (1 : Real)/2 ≤ p) (hp1 : p ≤ (3 : Real)/5) :
    target153 p ≤ 0 := by
  have hu : (0 : Real) ≤ 3/5 - p := by linarith
  have hsq : (0 : Real) ≤ 7 * (p - 39/70)^2 := by positivity
  have hQ : 7*p^3 - 12*p^2 + 8*p - 2 ≤ 0 := by
    nlinarith [mul_nonneg hu hsq]
  have h0 : (0 : Real) ≤ p := by linarith
  have h2 : (0 : Real) ≤ 2*p - 1 := by linarith
  have hprod : (0 : Real) ≤ p * (2*p - 1) * (-(7*p^3 - 12*p^2 + 8*p - 2)) :=
    mul_nonneg (mul_nonneg h0 h2) (by linarith)
  unfold target153
  nlinarith [hprod]

/-- The Atlas 153 catalogue bound on `[1/2, 3/5]`, in the statement shape the row
assembler expects of an interval piece. -/
theorem graphon_bound (W : Graphon Ω μ)
    (hp : (1 : Real)/2 ≤ cliqueDensity 2 W) (hp1 : cliqueDensity 2 W ≤ (3 : Real)/5) :
    target153 (cliqueDensity 2 W) ≤ homDensity graph153 W :=
  le_trans (target_nonpos hp hp1) (homDensity_nonneg graph153 W)

#print axioms graphon_bound

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Low
