/-!
# Propositional formulas

A minimal inductive presentation of propositional logic with
natural-number variables, plus a Boolean `eval` and the standard
`Satisfies` / `Satisfiable` predicates.

This is the Phase 0 spike for the Cook–Levin formalization. We keep
the surface area as small as possible: just enough to state and
decide concrete satisfiability examples.
-/

namespace CooksTheorem.PropLogic

/-- Propositional formulas with natural-number variables. -/
inductive PropFormula where
  | var : Nat → PropFormula
  | fls : PropFormula
  | neg : PropFormula → PropFormula
  | and : PropFormula → PropFormula → PropFormula
  | or  : PropFormula → PropFormula → PropFormula
  | imp : PropFormula → PropFormula → PropFormula
  deriving DecidableEq, Repr

namespace PropFormula

/-- Boolean evaluation under an assignment. -/
def eval (σ : Nat → Bool) : PropFormula → Bool
  | var n   => σ n
  | fls     => false
  | neg φ   => !eval σ φ
  | and φ ψ => eval σ φ && eval σ ψ
  | or  φ ψ => eval σ φ || eval σ ψ
  | imp φ ψ => !eval σ φ || eval σ ψ

/-- `σ` satisfies `φ` when `φ` evaluates to `true` under `σ`. -/
abbrev Satisfies (σ : Nat → Bool) (φ : PropFormula) : Prop :=
  eval σ φ = true

/-- `φ` is satisfiable when some assignment satisfies it. -/
def Satisfiable (φ : PropFormula) : Prop :=
  ∃ σ, Satisfies σ φ

/-! ### Spike examples -/

/-- A concrete assignment satisfies a concrete formula. -/
example : Satisfies (fun n => n == 0) (and (var 0) (neg (var 1))) := by
  decide

/-- Excluded middle is satisfiable: any constant assignment witnesses it. -/
example : Satisfiable (or (var 0) (neg (var 0))) :=
  ⟨fun _ => true, by decide⟩

end PropFormula
end CooksTheorem.PropLogic
