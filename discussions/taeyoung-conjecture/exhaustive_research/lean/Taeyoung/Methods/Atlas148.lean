import Taeyoung.Methods.Atlas148.Density
import Taeyoung.Methods.Atlas148.LowScalar
import Taeyoung.Methods.Atlas148.LowEdge
import Taeyoung.Methods.Atlas148.LowSymm
import Taeyoung.Methods.Atlas148.Low
import Taeyoung.Methods.Atlas148.Chromatic

/-!
# Atlas 148

`notes/atlas148_paw_bias_hilbert_projection.tex` splits at `p = 3/5`.

The **high interval** `[3/5, 1]` is complete and needs no triangle-density
input.  `Scalar.lean` proves the pointwise supporting line, `GeoMean.lean` the
three facts about `Z = √(d(x)d(y))`, `Linear.lean` the estimate
`p²G - qΔ ≥ pcf`, `Projection.lean` the linearized two-term Bessel bound, and
`High.lean` assembles them; `Density.lean` supplies the peeling identity, so
`homDensity_graph148_high` bounds the homomorphism density itself.

The **low interval** `[1/2, 3/5]` needs the sharp triangle profile, which is
where the vendored Fisher theorem enters through `Methods/TriangleDensity.lean`.
`LowScalar.lean` holds everything scalar in that branch: the two coordinates,
the comparison `c²f ≤ p·g(p)²`, the normalized monotonicity, and the two
lemmas that feed a tilted triangle bound through to `p·g(p) ≤ z·T` — one for
each side of the `s = 2/3` split, where Fisher hands over to Goodman.  None of
it needs the note's Bernstein data.

`LowEdge.lean` supplies the analytic inputs `M³ ≤ p` and `N³ ≥ p⁵` that those
lemmas consume, by one two-factor Cauchy--Schwarz where the note uses a
three-factor Hölder.  `LowSymm.lean` proves the leaf symmetrization, and
`Low.lean` builds the tilt `ν = d^{1/3}μ/M`, applies Fisher below `s = 2/3`
and Goodman above it, and assembles the interval.

`homDensity_graph148_bound` is the note's analytic theorem in full, on
`[1/2, 1]`.  `Chromatic.lean` adds the chromatic data — by surjective counts,
because `r²-3r+3` does not split and so no attachment tower produces it — and
`satisfiesLowerBound_148`.
-/
