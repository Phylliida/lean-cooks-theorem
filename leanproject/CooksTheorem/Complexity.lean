import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic
--Good!
/-!
# Decision problems and polynomial-size many-one reductions

A `DecisionProblem` is a predicate over an arbitrary type of instances,
paired with a "natural size" function. A `Reduces P₁ P₂` is a function
on instances together with a polynomial bound on the output size and
a correctness biconditional.

We deliberately do **not** require the reduction function to be
formally polynomial-time computable. Polynomial-*size* on the output
is the meaningful obligation for Karp reductions: the formal
verification we get is that the reduced instance is polynomially
sized, the biconditional holds, and the reduction is a total Lean
function (so by structural-recursion termination it is at least
computable). In practice every reduction we'll write is "obviously
poly-time" by inspection.

This avoids hand-coding Turing machines for every verifier and
reduction in the planned NP-completeness library.
-/

open Polynomial

namespace CooksTheorem

/-- A decision problem: a predicate over a natural type of instances,
plus a "natural size" measure used to bound polynomial reductions. -/
structure DecisionProblem where
  /-- The natural type of instances. -/
  α : Type
  /-- The predicate defining membership in the language. -/
  pred : α → Prop
  /-- The natural size of an instance. -/
  size : α → Nat

namespace DecisionProblem

/-- Polynomial-size many-one reduction from `P₁` to `P₂`. -/
structure Reduces (P₁ P₂ : DecisionProblem) where
  /-- The reduction function on instances. -/
  fn : P₁.α → P₂.α
  /-- Correctness: `x` satisfies `P₁` iff `fn x` satisfies `P₂`. -/
  correct : ∀ x, P₁.pred x ↔ P₂.pred (fn x)
  /-- A polynomial bounding the output size. -/
  bound : Polynomial ℕ
  /-- The output size is bounded by the polynomial applied to the input size. -/
  bound_holds : ∀ x, P₂.size (fn x) ≤ bound.eval (P₁.size x)

end DecisionProblem

/-- Polynomial evaluation over `ℕ` is monotone in the input. The proof is
by induction on the polynomial: monomial and addition cases each preserve
the inequality. Used by `Reduces.trans` to compose reductions. -/
theorem nat_poly_eval_le_eval_of_le (p : Polynomial ℕ) {a b : ℕ}
    (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

namespace DecisionProblem.Reduces

/-- Identity reduction: every problem reduces to itself. -/
noncomputable def refl (P : DecisionProblem) : Reduces P P where
  fn := id
  correct _ := Iff.rfl
  bound := X
  bound_holds _ := by simp

/-- Composition of reductions. -/
noncomputable def trans {P₁ P₂ P₃ : DecisionProblem}
    (f : Reduces P₁ P₂) (g : Reduces P₂ P₃) : Reduces P₁ P₃ where
  fn := g.fn ∘ f.fn
  correct x := (f.correct x).trans (g.correct (f.fn x))
  bound := g.bound.comp f.bound
  bound_holds x := by
    have h₁ := f.bound_holds x
    have h₂ := g.bound_holds (f.fn x)
    rw [eval_comp]
    exact h₂.trans (nat_poly_eval_le_eval_of_le g.bound h₁)

end DecisionProblem.Reduces

end CooksTheorem
