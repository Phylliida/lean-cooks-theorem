import CooksTheorem.SAT
import CooksTheorem.Graph
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
# Independent Set

The independent-set decision problem: given a graph `G` and a target
size `k ≤ G.V`, is there a set of `k` pairwise non-adjacent vertices
in `G`?

We constrain `k ≤ G.V` at the type level (via a subtype). This
eliminates an awkward edge case in the IS↔VC duality reduction
without sacrificing generality (for `k > V`, no IS of size `k` can
exist anyway).

The SAT → IS gadget reduction is the canonical first hard Karp
reduction; it requires substantial bookkeeping and is left for a
focused follow-up. The structural reductions in `VertexCover.lean`
and `Clique.lean` (IS↔VC duality, IS↔CLIQUE complement) do not
depend on it and chain via transitivity to give NP-hardness of the
companion problems once the gadget is in place.
-/

namespace CooksTheorem

/-- An IS / VC / CLIQUE instance: a graph plus a target size that
does not exceed the vertex count. We bake `k ≤ V` in at the type
level to make the IS↔VC duality reduction clean. -/
structure BoundedSize where
  graph : Graph
  k : Nat
  k_le_V : k ≤ graph.V

/-- The independent-set decision problem. -/
def IndependentSet : DecisionProblem where
  α := BoundedSize
  pred := fun p => ∃ S : Finset Nat,
    p.k ≤ S.card ∧
    (∀ v ∈ S, v < p.graph.V) ∧
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → p.graph.E u v = false)
  size := fun p => p.graph.V

end CooksTheorem
