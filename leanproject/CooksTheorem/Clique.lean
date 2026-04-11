import CooksTheorem.IndependentSet

/-!
# Clique and the IS ↔ CLIQUE complement reduction

The clique decision problem: given a graph `G` and `k ≤ G.V`, is
there a set of `k` pairwise *adjacent* vertices?

The reduction from `IndependentSet` is the standard graph complement
trick: a set `S` is an independent set in `G` iff `S` is a clique in
the complement of `G`. Together with `VertexCover.lean`, this puts
`IS`, `VC`, `CLIQUE` in the same Karp-equivalence class as soon as
`SAT → IS` is in place.
-/

namespace CooksTheorem

/-- The clique decision problem. -/
def Clique : DecisionProblem where
  α := BoundedSize
  pred := fun p => ∃ S : Finset Nat,
    p.k ≤ S.card ∧
    (∀ v ∈ S, v < p.graph.V) ∧
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → p.graph.E u v = true)
  size := fun p => p.graph.V

/-- IS reduces to CLIQUE: a set is an independent set in `G` iff it
is a clique in the complement of `G`. -/
noncomputable def is_reduces_to_clique :
    IndependentSet.Reduces Clique where
  fn p :=
    { graph := p.graph.complement
      k := p.k
      k_le_V := by simp [Graph.complement_V]; exact p.k_le_V }
  correct p := by
    refine ⟨?_, ?_⟩
    · -- IS in G ⇒ clique in complement G
      rintro ⟨S, hcard, hvalid, hindep⟩
      refine ⟨S, hcard, ?_, ?_⟩
      · intro v hv
        simp [Graph.complement_V]
        exact hvalid v hv
      · intro u hu v hv huv
        simp [Graph.complement_E, huv]
        exact hindep u hu v hv huv
    · -- Clique in complement G ⇒ IS in G
      rintro ⟨S, hcard, hvalid, hclique⟩
      refine ⟨S, hcard, ?_, ?_⟩
      · intro v hv
        have := hvalid v hv
        simp [Graph.complement_V] at this
        exact this
      · intro u hu v hv huv
        have := hclique u hu v hv huv
        simp [Graph.complement_E, huv] at this
        exact this
  bound := Polynomial.X
  bound_holds p := by simp [IndependentSet, Clique, Graph.complement_V]

end CooksTheorem
