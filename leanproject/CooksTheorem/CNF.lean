/-!
# Conjunctive normal form

A minimal CNF representation: a literal is a positive or negated
variable, and a formula is a list of clauses (each clause is a list
of literals). The semantics are Boolean evaluation under an
assignment, plus a `Satisfiable` predicate.

This is the only formula representation we use: the Cook–Levin
tableau directly produces CNF formulas, so we don't need a richer
propositional-formula AST or a Tseitin-style conversion.
-/

namespace CooksTheorem.CNF

/-- A literal: a positive or negated propositional variable. -/
inductive Literal where
  | pos (n : Nat)
  | neg (n : Nat)
  deriving DecidableEq

/-- Boolean evaluation of a literal under an assignment. -/
def Literal.eval (σ : Nat → Bool) : Literal → Bool
  | .pos n => σ n
  | .neg n => !σ n

/-- A CNF formula: a conjunction of clauses, each clause a
disjunction of literals. -/
abbrev Formula := List (List Literal)

namespace Formula

/-- Boolean evaluation of a formula under an assignment. -/
def eval (σ : Nat → Bool) (φ : Formula) : Bool :=
  φ.all fun clause => clause.any (Literal.eval σ)

/-- `σ` satisfies `φ` iff `φ` evaluates to `true` under `σ`. -/
abbrev Satisfies (σ : Nat → Bool) (φ : Formula) : Prop :=
  φ.eval σ = true

/-- `φ` is satisfiable iff some assignment satisfies it. -/
def Satisfiable (φ : Formula) : Prop :=
  ∃ σ, φ.Satisfies σ

/-- The total literal count of a formula, used as the natural size
measure for `SAT` as a decision problem. -/
def size (φ : Formula) : Nat :=
  (φ.map List.length).sum

end Formula

/-! ### Spike example -/

/-- Excluded middle as a one-clause CNF: `x₀ ∨ ¬x₀` is satisfiable. -/
example : Formula.Satisfiable [[.pos 0, .neg 0]] :=
  ⟨fun _ => true, by decide⟩

end CooksTheorem.CNF
