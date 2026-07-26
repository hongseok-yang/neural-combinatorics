import PureChordal.Main
import PureChordal.Examples.N4
import PureChordal.Examples.N5
import PureChordal.Examples.N6

/-!
# Worked examples: `k`-partite optimality for small pure chordal graphs

This module collects certificates and `k`-partite optimality theorems for all
`17` non-clique pure chordal graphs on at most six vertices (`1` on four
vertices, `4` on five, `12` on six; the complete graphs `Kᵣ` are excluded).
They are grouped by vertex count in `Examples/N4`, `Examples/N5`, and
`Examples/N6`.

Each graph is named `G<n>_<i>` and lives in its own namespace
`PureChordal.Examples.G<n>_<i>`, exhibiting a `PureCliqueTreeDecomp` and deriving
`optimality` from `PureCliqueTreeDecomp.balancedMultipartite_minimal` — so no
chordality or maximal-clique reasoning is used, only the explicit certificate.
-/
