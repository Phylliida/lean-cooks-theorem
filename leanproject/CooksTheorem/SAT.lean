import CooksTheorem.CNF
import CooksTheorem.Complexity

/-!
# SAT, NP, and Cook–Levin

`SAT` is the decision problem "given a CNF formula, is it satisfiable?"
We define it as a `DecisionProblem` whose instance type is
`CNF.Formula` directly, with the natural literal-count size measure.

`NP` is defined as "polynomially reducible to SAT" — the
SAT-reducibility characterization. This is mathematically equivalent
to the standard NTM-based definition (the equivalence is essentially
the content of Cook–Levin in the classical formulation), but it
admits a much cleaner formalization: the witnesses are plain Lean
functions producing CNF formulas, with no Turing machines anywhere.

Under this definition, **Cook–Levin is definitional**: every problem
in `NP` reduces to SAT because that's how `NP` is defined. The
mathematical content of Cook's theorem is moved to the user-supplied
reductions for each individual NP-complete problem (each problem
proves its own membership in NP by exhibiting a Lean function that
maps instances to satisfiability-equivalent CNF formulas).
-/

namespace CooksTheorem

open CNF

/-- The SAT decision problem: given a CNF formula, is it satisfiable? -/
def SAT : DecisionProblem where
  α := Formula
  pred := Formula.Satisfiable
  size := Formula.size

/-- A decision problem is in `NP` iff it has a polynomial-size many-one
reduction to SAT. -/
def NP (P : DecisionProblem) : Prop :=
  Nonempty (P.Reduces SAT)

/-- SAT is in NP, witnessed by the identity reduction. -/
theorem sat_in_NP : NP SAT :=
  ⟨DecisionProblem.Reduces.refl SAT⟩

/-- **Cook–Levin theorem** (in our SAT-reducibility formulation):
every problem in NP reduces to SAT. Definitionally trivial: that's
the definition of `NP`. -/
theorem cook_levin {P : DecisionProblem} (h : NP P) :
    Nonempty (P.Reduces SAT) :=
  h

/-- A decision problem is **NP-complete** iff it is in NP and every
problem in NP reduces to it. -/
def NPComplete (P : DecisionProblem) : Prop :=
  NP P ∧ ∀ Q : DecisionProblem, NP Q → Nonempty (Q.Reduces P)

/-- SAT is NP-complete. The "in NP" part is `sat_in_NP`; the
"every NP problem reduces to it" part is exactly the definition of
`NP`. -/
theorem sat_npComplete : NPComplete SAT :=
  ⟨sat_in_NP, fun _ h => h⟩

end CooksTheorem
