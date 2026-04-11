import CooksTheorem.IndependentSet

/-!
# Vertex Cover and the IS↔VC duality

The vertex-cover decision problem: given a graph `G` and a target
size `k ≤ G.V`, is there a set of `≤ k` vertices covering every
edge?

The classical IS↔VC duality says `S` is an independent set iff
`V \ S` is a vertex cover, with `|V \ S| = V - |S|`. So
`(G, k)` has an IS of size `≥ k` iff `(G, V - k)` has a VC of
size `≤ V - k`. We give both directions of this reduction.

Together with `Clique.lean`, this means once `SAT → IS` is in place,
all of `IS`, `VC`, `CLIQUE` are NP-hard by transitivity.
-/

namespace CooksTheorem

/-- The vertex-cover decision problem. -/
def VertexCover : DecisionProblem where
  α := BoundedSize
  pred := fun p => ∃ S : Finset Nat,
    S.card ≤ p.k ∧
    (∀ v ∈ S, v < p.graph.V) ∧
    (∀ u v, u < p.graph.V → v < p.graph.V → u ≠ v →
      p.graph.E u v = true → u ∈ S ∨ v ∈ S)
  size := fun p => p.graph.V

/-- Take the complement of `S` within the vertex set `Finset.range V`. -/
private def vertexComplement (V : Nat) (S : Finset Nat) : Finset Nat :=
  Finset.range V \ S

private theorem vertexComplement_card {V : Nat} {S : Finset Nat}
    (hS : ∀ v ∈ S, v < V) :
    (vertexComplement V S).card = V - S.card := by
  have hsub : S ⊆ Finset.range V := fun v hv =>
    Finset.mem_range.mpr (hS v hv)
  unfold vertexComplement
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]

private theorem vertexComplement_mem {V : Nat} {S : Finset Nat} {v : Nat} :
    v ∈ vertexComplement V S ↔ v < V ∧ v ∉ S := by
  simp [vertexComplement, Finset.mem_sdiff, Finset.mem_range]

/-- IS reduces to VC: `(G, k)` has an IS of size `≥ k` iff
`(G, V - k)` has a VC of size `≤ V - k`. -/
noncomputable def is_reduces_to_vertexCover :
    IndependentSet.Reduces VertexCover where
  fn p :=
    { graph := p.graph
      k := p.graph.V - p.k
      k_le_V := Nat.sub_le _ _ }
  correct p := by
    refine ⟨?_, ?_⟩
    · -- Forward: IS of size ≥ k ⇒ VC of size ≤ V - k
      rintro ⟨S, hcard, hvalid, hindep⟩
      refine ⟨vertexComplement p.graph.V S, ?_, ?_, ?_⟩
      · -- |VC| ≤ V - k
        rw [vertexComplement_card hvalid]
        exact Nat.sub_le_sub_left hcard p.graph.V
      · -- VC vertices are valid
        intro v hv
        exact (vertexComplement_mem.mp hv).1
      · -- VC covers every edge
        intro u v hu hv huv hedge
        by_contra hboth
        push_neg at hboth
        obtain ⟨hu_notin_VC, hv_notin_VC⟩ := hboth
        have hu_in_S : u ∈ S := by
          by_contra hu_notin
          exact hu_notin_VC (vertexComplement_mem.mpr ⟨hu, hu_notin⟩)
        have hv_in_S : v ∈ S := by
          by_contra hv_notin
          exact hv_notin_VC (vertexComplement_mem.mpr ⟨hv, hv_notin⟩)
        have := hindep u hu_in_S v hv_in_S huv
        rw [this] at hedge
        exact Bool.false_ne_true hedge
    · -- Backward: VC of size ≤ V - k ⇒ IS of size ≥ k
      rintro ⟨VC, hVCcard, hVCvalid, hVCcovers⟩
      refine ⟨vertexComplement p.graph.V VC, ?_, ?_, ?_⟩
      · -- |IS| ≥ k
        rw [vertexComplement_card hVCvalid]
        -- Use `set` to give omega clean local Nat values
        set V := p.graph.V with hV
        set k := p.k with hk
        set vc := VC.card with hvc
        have h1 : vc ≤ V - k := hVCcard
        have h2 : k ≤ V := p.k_le_V
        change k ≤ V - vc
        omega
      · -- IS vertices are valid
        intro v hv
        exact (vertexComplement_mem.mp hv).1
      · -- IS has no internal edges
        intro u hu v hv huv
        rcases vertexComplement_mem.mp hu with ⟨hu_lt, hu_notin⟩
        rcases vertexComplement_mem.mp hv with ⟨hv_lt, hv_notin⟩
        by_contra hedge
        rw [Bool.not_eq_false] at hedge
        have := hVCcovers u v hu_lt hv_lt huv hedge
        rcases this with h | h
        · exact hu_notin h
        · exact hv_notin h
  bound := Polynomial.X
  bound_holds p := by simp [IndependentSet, VertexCover]

end CooksTheorem
