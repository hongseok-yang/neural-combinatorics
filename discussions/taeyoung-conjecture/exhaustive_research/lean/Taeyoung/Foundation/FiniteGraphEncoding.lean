import Taeyoung.Foundation.Status

/-!
# Small finite graph encodings

Atlas modules store both graph6 metadata and a transparent edge list.  The
edge list is the Lean definition; graph6 is retained as an external stable ID
until a verified graph6 decoder is added.
-/

namespace Taeyoung

/-- Build a simple graph on `Fin n` from an oriented list of unordered edges.
`SimpleGraph.fromRel` supplies symmetry and discards loops. -/
def graphFromEdges (n : ℕ) (edges : List (Nat × Nat)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => (u.val, v.val) ∈ edges

/-- Adjacency in an edge-list graph is decidable *by computation*: membership in
a `List (Nat × Nat)` is.  Declaring this canonical instance is what lets an
isomorphism between an Atlas graph and a method representative be discharged by
`decide`.  Modules must therefore not shadow it with `Classical.decRel`, which
would block kernel reduction. -/
instance graphFromEdges_decidableAdj (n : ℕ) (edges : List (Nat × Nat)) :
    DecidableRel (graphFromEdges n edges).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

/-- Metadata shared by the generated catalogue and its count checks. -/
structure CatalogueRow where
  atlasId : ℕ
  vertexCount : ℕ
  edgeCount : ℕ
  chromaticNumber : ℕ
  graph6 : String
  status : CatalogueStatus
  formalization : FormalizationState
  deriving DecidableEq, Repr

end Taeyoung
