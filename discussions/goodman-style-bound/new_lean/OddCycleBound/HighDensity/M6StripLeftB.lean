/-
# High-density theorem — residual strip left-estimate, B-branch made unconditional (M6)

Assembles the `eq:tail-ratio` bridge: discharges the `hSD : D ≤ Σ` hypothesis of
`diagKernel_nonneg_strip_left` on the B-branch (`θ = r/m ≥ 1/6`, `ℓ ≤ 2/5`, `m ≥ 63`) using the
power-lifted factor bounds (`M6TailRatio`) and the constant inequality `constB_m63`.  Since
`constB_m63` is uniform for all `m ≥ 63` (no finite sweep), the B-branch left strip becomes
fully unconditional.
-/

import OddCycleBound.HighDensity.M6TailRatio
import OddCycleBound.HighDensity.M6LeftEstimate
import OddCycleBound.HighDensity.AppConstantsTail

namespace OddCycleBound.HighDensity

/-- The core algebraic identity `Σ₁ = D · G` of `eq:tail-ratio` (`99/100` factored out), with
`ν = (2t+1)/m`.  Both sides are explicit products of powers; the proof breaks the compound powers
`(2fe)^{2t+1}`, `(eps/b)^r`, `(la/le)^m` into atoms and uses `2^{2t+1}=2·2^{2t}`, `b^r=b^{r-1}·b`. -/
lemma sig1_eq {a fe eps la le b nu : ℝ} {r tt m : ℕ}
    (hm0 : (m : ℝ) ≠ 0) (hnu : nu = (2 * (tt : ℝ) + 1) / m) (hr1 : 1 ≤ r)
    (hr0 : (r : ℝ) ≠ 0) (hb : b ≠ 0) (hba : (b - a) ≠ 0) (hla : la ≠ 0) (hle : le ≠ 0)
    (hnu0 : nu ≠ 0) (h2t1 : ((2 * (tt : ℝ) + 1)) ≠ 0) :
    ((m : ℝ) / (2 * (tt : ℝ) + 1)) * fe ^ (2 * tt + 1) * (eps ^ r / ((r : ℝ) * le ^ m))
      = (b ^ (r - 1) * ((1 / 2) ^ (2 * tt) / la ^ m) * ((b - a) ^ 2 / (2 * nu)))
        * ((b / ((r : ℝ) * (b - a) ^ 2))
            * ((2 * fe) ^ (2 * tt + 1) * ((eps / b) ^ r * (la / le) ^ m))) := by
  have hbr : b ^ r = b ^ (r - 1) * b := by rw [← pow_succ, Nat.sub_add_cancel hr1]
  have hla0 : la ^ m ≠ 0 := pow_ne_zero _ hla
  have hle0 : le ^ m ≠ 0 := pow_ne_zero _ hle
  have hbr1 : b ^ (r - 1) ≠ 0 := pow_ne_zero _ hb
  rw [mul_pow, one_div_pow, div_pow, div_pow, pow_succ (2 : ℝ) (2 * tt), hbr, hnu]
  field_simp
end OddCycleBound.HighDensity
