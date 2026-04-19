--Good!

/-!
# Conjunctive normal form

A minimal CNF representation: a literal is a positive or negated
variable, and a formula is a list of clauses (each clause is a list
of literals). The semantics are Boolean evaluation under an
assignment, plus a `Satisfiable` predicate.

Following mathlib's `Polynomial` (which derives `degree`/`natDegree`
from a `Finsupp` rather than bundling it), we leave the variable
count *implicit* in the data and provide derived helpers
(`maxVar`, `numVars`) plus an equivalence between satisfiability
over `Nat → Bool` and satisfiability over `Fin numVars → Bool`.
This keeps the core representation simple at the cost of carrying
no invariant on the literal indices — the same trade-off mathlib
makes for polynomials.

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

namespace Literal

/-- Boolean evaluation of a literal under an assignment. -/
def eval (σ : Nat → Bool) : Literal → Bool
  | .pos n => σ n
  | .neg n => !σ n

/-- The variable index referenced by a literal. -/
def varIdx : Literal → Nat
  | .pos n => n
  | .neg n => n

/-- Two assignments that agree on a literal's variable give it the
same value. -/
theorem eval_congr {σ₁ σ₂ : Nat → Bool} {l : Literal}
    (h : σ₁ l.varIdx = σ₂ l.varIdx) :
    l.eval σ₁ = l.eval σ₂ := by
  cases l <;> simp [eval, varIdx] at h ⊢ <;> rw [h]

end Literal

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

/-! ### Variable counts -/

/-- Maximum variable index appearing in a clause, or `0` if the clause
has no literals. -/
def clauseMaxVar : List Literal → Nat
  | [] => 0
  | l :: rest => max l.varIdx (clauseMaxVar rest)

/-- Maximum variable index appearing anywhere in the formula, or `0`
if no literals appear. -/
def maxVar : Formula → Nat
  | [] => 0
  | c :: rest => max (clauseMaxVar c) (maxVar rest)

/-- The number of variable "slots" needed to assign all variables in
`φ`: `maxVar φ + 1`. For the empty formula or a formula with no
literals this is `1` rather than `0`, which is harmless because such
formulas don't reference any variable. -/
def numVars (φ : Formula) : Nat := φ.maxVar + 1

/-- Every literal in a clause has variable index bounded by the
clause's `clauseMaxVar`. -/
theorem varIdx_le_clauseMaxVar {l : Literal} {c : List Literal} (h : l ∈ c) :
    l.varIdx ≤ clauseMaxVar c := by
  induction c with
  | nil => exact absurd h (List.not_mem_nil)
  | cons l' rest ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-- Every clause's `clauseMaxVar` is bounded by the formula's `maxVar`. -/
theorem clauseMaxVar_le_maxVar {c : List Literal} {φ : Formula} (h : c ∈ φ) :
    clauseMaxVar c ≤ maxVar φ := by
  induction φ with
  | nil => exact absurd h (List.not_mem_nil)
  | cons c' rest ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-- Two assignments that agree below `clauseMaxVar c` give the same
value to every literal in `c`, hence to the clause as a whole. -/
theorem clause_eval_congr {σ₁ σ₂ : Nat → Bool} (c : List Literal)
    (h : ∀ n ≤ clauseMaxVar c, σ₁ n = σ₂ n) :
    c.any (Literal.eval σ₁) = c.any (Literal.eval σ₂) := by
  induction c with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.any_cons]
    have hl : σ₁ l.varIdx = σ₂ l.varIdx := by
      apply h
      simp only [clauseMaxVar]
      exact Nat.le_max_left _ _
    have hrest : rest.any (Literal.eval σ₁) = rest.any (Literal.eval σ₂) := by
      apply ih
      intro n hn
      apply h
      simp only [clauseMaxVar]
      exact Nat.le_trans hn (Nat.le_max_right _ _)
    rw [Literal.eval_congr hl, hrest]

/-- Two assignments that agree on all variables `≤ φ.maxVar` give `φ`
the same evaluation. The "variable extensionality" lemma. -/
theorem eval_congr {σ₁ σ₂ : Nat → Bool} (φ : Formula)
    (h : ∀ n ≤ φ.maxVar, σ₁ n = σ₂ n) :
    φ.eval σ₁ = φ.eval σ₂ := by
  induction φ with
  | nil => rfl
  | cons c rest ih =>
    have hc : ∀ n ≤ clauseMaxVar c, σ₁ n = σ₂ n := by
      intro n hn
      exact h n (Nat.le_trans hn (Nat.le_max_left _ _))
    have hrest : Formula.eval σ₁ rest = Formula.eval σ₂ rest := by
      apply ih
      intro n hn
      exact h n (Nat.le_trans hn (Nat.le_max_right _ _))
    have hclause := clause_eval_congr c hc
    simp [eval, List.all_cons] at hrest ⊢
    rw [hclause, hrest]

/-- Extend a finite `Fin numVars` assignment to a `Nat` assignment by
filling unconstrained positions with `false`. -/
def extendAssignment (φ : Formula) (σ : Fin φ.numVars → Bool) : Nat → Bool :=
  fun n => if h : n < φ.numVars then σ ⟨n, h⟩ else false

/-- Satisfiability is equivalent to satisfaction by a finite assignment
over `Fin numVars`. The forward direction restricts a `Nat → Bool`
witness; the backward direction uses `extendAssignment` to fill
positions outside the variable range with `false`. -/
theorem satisfiable_iff_fin (φ : Formula) :
    φ.Satisfiable ↔
      ∃ σ : Fin φ.numVars → Bool, φ.eval (φ.extendAssignment σ) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun i => σ i.val, ?_⟩
    rw [eval_congr (σ₂ := σ)]
    · exact hσ
    · intro n hn
      simp only [extendAssignment, numVars]
      have : n < φ.maxVar + 1 := Nat.lt_succ_of_le hn
      simp [this]
  · rintro ⟨σ, hσ⟩
    exact ⟨φ.extendAssignment σ, hσ⟩

end Formula

/-! ### Spike example -/

/-- Excluded middle as a one-clause CNF: `x₀ ∨ ¬x₀` is satisfiable. -/
example : Formula.Satisfiable [[.pos 0, .neg 0]] :=
  ⟨fun _ => true, by decide⟩

end CooksTheorem.CNF
