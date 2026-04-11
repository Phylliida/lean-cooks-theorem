/-!
# Simple finite graphs

A minimal `Graph` type for use as the instance type of graph-based
NP-complete problems. Vertices are natural numbers `0, 1, ..., V - 1`
and the adjacency relation is a function `Nat → Nat → Bool`.

We do **not** enforce symmetry or irreflexivity as structural
invariants. Predicates that need them (e.g., the IS / VC / CLIQUE
predicates) state them explicitly or use the simplified form. The
graph constructions in our reductions all produce symmetric,
irreflexive graphs by construction.
-/

namespace CooksTheorem

/-- A finite graph: `V` is the vertex count and `E u v` is the
adjacency relation. -/
structure Graph where
  /-- The vertex count. Vertices are indexed `0, …, V - 1`. -/
  V : Nat
  /-- Adjacency. For "well-formed" graphs this is symmetric and
  irreflexive, but we don't enforce these as invariants. -/
  E : Nat → Nat → Bool

namespace Graph

/-- The complement of a graph: same vertices, the edge relation is
inverted on distinct pairs. (Self-loops are removed in the
complement.) -/
def complement (G : Graph) : Graph where
  V := G.V
  E u v := decide (u ≠ v) && !G.E u v

@[simp]
theorem complement_V (G : Graph) : G.complement.V = G.V := rfl

@[simp]
theorem complement_E (G : Graph) (u v : Nat) :
    G.complement.E u v = (decide (u ≠ v) && !G.E u v) := rfl

end Graph

end CooksTheorem
