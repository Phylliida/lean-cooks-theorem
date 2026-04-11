import CooksTheorem.SAT

/-!
# 3-SAT and a worked variable-shifting reduction

This file is the workflow validation for the per-problem effort under
the new framework. It demonstrates two patterns we'll use over and
over for the planned NP-completeness library:

1. A `DecisionProblem` whose instance type is a *subtype* of an
   existing problem's instance type (here: 3-SAT, the subtype of CNF
   formulas with all clauses of length ≤ 3).
2. A non-trivial reduction with a real correctness proof: SAT to a
   variant `SAT_NoVar0` where variable index 0 is forbidden, via
   variable shifting.
-/

namespace CooksTheorem

open CNF

/-! ### 3-SAT -/

/-- The subtype of CNF formulas where every clause has at most 3
literals. The natural instance type for 3-SAT. -/
abbrev ThreeFormula := { φ : Formula // ∀ c ∈ φ, c.length ≤ 3 }

/-- The 3-SAT decision problem. -/
def Three_SAT : DecisionProblem where
  α := ThreeFormula
  pred := fun φ => φ.val.Satisfiable
  size := fun φ => φ.val.size

/-- Trivial reduction: every 3-SAT instance is already a SAT instance.
The function unwraps the subtype, the predicate is identical, and the
output size equals the input size. -/
noncomputable def threeSAT_reduces_to_SAT : Three_SAT.Reduces SAT where
  fn := Subtype.val
  correct _ := Iff.rfl
  bound := Polynomial.X
  bound_holds _ := by simp [SAT, Three_SAT]

/-! ### `SAT_NoVar0` and the variable-shifting reduction

A second decision problem demonstrating a different shape constraint
and a non-trivial reduction. `SAT_NoVar0` is SAT with the additional
constraint that variable index 0 is never used. The reduction from
SAT shifts every variable index up by one. -/

/-- The subtype of CNF formulas in which variable index 0 never
appears. -/
abbrev NoVar0Formula := { φ : Formula // ∀ c ∈ φ, ∀ l ∈ c,
  l ≠ Literal.pos 0 ∧ l ≠ Literal.neg 0 }

/-- The `SAT_NoVar0` decision problem. -/
def SAT_NoVar0 : DecisionProblem where
  α := NoVar0Formula
  pred := fun φ => φ.val.Satisfiable
  size := fun φ => φ.val.size

/-- Shift a literal's variable index up by one. -/
def shiftLiteral : Literal → Literal
  | .pos n => .pos (n + 1)
  | .neg n => .neg (n + 1)

/-- Shift every literal in a clause. -/
def shiftClause (c : List Literal) : List Literal :=
  c.map shiftLiteral

/-- Shift every literal in a formula. -/
def shiftFormula (φ : Formula) : Formula :=
  φ.map shiftClause

/-- Shifted literals are never `pos 0` or `neg 0`. -/
theorem shiftLiteral_ne_var0 (l : Literal) :
    shiftLiteral l ≠ Literal.pos 0 ∧ shiftLiteral l ≠ Literal.neg 0 := by
  cases l <;> simp [shiftLiteral]

/-- The shifted formula contains no occurrence of variable 0. -/
theorem shiftFormula_no_var0 (φ : Formula) :
    ∀ c ∈ shiftFormula φ, ∀ l ∈ c,
      l ≠ Literal.pos 0 ∧ l ≠ Literal.neg 0 := by
  intro c hc l hl
  simp only [shiftFormula, List.mem_map] at hc
  obtain ⟨c', _, rfl⟩ := hc
  simp only [shiftClause, List.mem_map] at hl
  obtain ⟨l', _, rfl⟩ := hl
  exact shiftLiteral_ne_var0 l'

/-- Evaluating a shifted literal under any assignment equals evaluating
the original literal under the assignment shifted-back. -/
theorem shiftLiteral_eval (σ : Nat → Bool) (l : Literal) :
    Literal.eval σ (shiftLiteral l) = Literal.eval (fun n => σ (n + 1)) l := by
  cases l <;> simp [shiftLiteral, Literal.eval]

/-- Same identity at the formula level: evaluating the shifted formula
under `σ` equals evaluating the original under `(fun n => σ (n + 1))`. -/
theorem shiftFormula_eval (σ : Nat → Bool) (φ : Formula) :
    (shiftFormula φ).eval σ = φ.eval (fun n => σ (n + 1)) := by
  unfold Formula.eval shiftFormula shiftClause
  rw [List.all_map]
  congr 1
  funext c
  rw [Function.comp_apply, List.any_map]
  congr 1
  funext l
  exact shiftLiteral_eval σ l

/-- Satisfiability is preserved under shifting. -/
theorem shiftFormula_satisfiable (φ : Formula) :
    φ.Satisfiable ↔ (shiftFormula φ).Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun n => match n with | 0 => false | k + 1 => σ k, ?_⟩
    change (shiftFormula φ).eval _ = true
    rw [shiftFormula_eval]
    exact hσ
  · rintro ⟨σ, hσ⟩
    exact ⟨fun n => σ (n + 1), (shiftFormula_eval σ φ).symm.trans hσ⟩

/-- Shifting preserves the literal count. -/
theorem shiftFormula_size (φ : Formula) : (shiftFormula φ).size = φ.size := by
  unfold Formula.size shiftFormula shiftClause
  simp [List.map_map, Function.comp_def]

/-- The reduction from SAT to SAT_NoVar0 via variable shifting. -/
noncomputable def sat_reduces_to_sat_noVar0 : SAT.Reduces SAT_NoVar0 where
  fn φ := ⟨shiftFormula φ, shiftFormula_no_var0 φ⟩
  correct φ := shiftFormula_satisfiable φ
  bound := Polynomial.X
  bound_holds φ := by
    simp [SAT, SAT_NoVar0]
    rw [shiftFormula_size]

end CooksTheorem
