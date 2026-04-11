# Proof Plan: NP-Completeness Library (formerly Cook–Levin)

## Goal

Build a Lean 4 + mathlib library of **100+ NP-complete decision
problems** with formally verified Karp reductions between them.

The seed of the library is `SAT`, with `cook_levin : ∀ L ∈ NP, L
reduces to SAT`. Every other problem is added by

1. defining its `DecisionProblem` (a predicate over a natural type
   of instances + a size measure),
2. proving its `NP` membership by exhibiting a Lean function that
   maps instances to satisfiability-equivalent CNF formulas, and
3. proving NP-hardness via a chain of Karp reductions back to SAT.

## Pivot history

The original plan tried to formalize Cook–Levin via the standard
NTM-tableau construction. After several iterations of trying to
make this work cleanly, we settled on the present architecture
because the library scale (100+ problems) makes any TM-construction
approach hopeless.

The key insight was: **define `NP` via SAT-formula reducibility
instead of NTM-acceptance**. Both definitions are equivalent (this
*is* the content of Cook–Levin in the classical formulation), but
the SAT-reducibility version makes the entire framework collapse
to plain Lean functions over plain Lean types — no Turing machines,
no DSL, no realizability obligations beyond polynomial size bounds.

## Architecture

### Core types (Phase 0)

**`CooksTheorem/CNF.lean`** — `Literal`, `Formula = List (List Literal)`,
`eval`, `Satisfies`, `Satisfiable`, `size`. ~50 lines.

**`CooksTheorem/Complexity.lean`** — `DecisionProblem` (a record of
`α`, `pred`, `size`), `Reduces P₁ P₂` (a record of `fn`, `correct`,
polynomial `bound`, `bound_holds`), plus `Reduces.refl`,
`Reduces.trans`, and the small lemma `Polynomial.eval_le_eval_of_le`
needed by `trans`. ~90 lines.

**`CooksTheorem/SAT.lean`** — `SAT : DecisionProblem`,
`NP : DecisionProblem → Prop := fun P => Nonempty (P.Reduces SAT)`,
`sat_in_NP`, `cook_levin`, `NPComplete`, `sat_npComplete`. The
"hard" theorems are essentially definitional under our framing. ~60 lines.

### Per-problem files

For each NP-complete problem `L_i`, one file at
`CooksTheorem/Problems/L_i.lean` (or grouped by topic) containing:

- The instance type (often a subtype of `CNF.Formula` or a custom
  record like `Graph × Nat`)
- The `DecisionProblem` definition
- An `NP` proof (a `Reduces L_i SAT` with a Lean function producing
  the equivalent CNF)
- An NP-hardness proof (a `Reduces L_j L_i` from some already-defined
  NP-complete `L_j`)

Validation file `CooksTheorem/ThreeSAT.lean` contains the first two
non-trivial examples:

- `Three_SAT` (CNF with all clauses ≤ 3 literals; subtype α)
- A trivial reduction `Three_SAT.Reduces SAT`
- `SAT_NoVar0` (CNF avoiding variable index 0; subtype α)
- A non-trivial reduction `SAT.Reduces SAT_NoVar0` via variable
  shifting, with a real correctness proof (assignment
  transformation + structural induction over the formula
  representation)

The variable-shifting example came in at ~135 lines including
docstrings, which is comfortably within budget for ~100-line per
problem.

## What we're (not) verifying

We verify, for every reduction:

- **Correctness** of the biconditional `x ∈ L₁ ↔ fn x ∈ L₂` (a real
  Lean proof obligation)
- **Polynomial size bound** on the output: `(fn x).size ≤ p.eval (input.size)`
  for an explicit polynomial `p`
- **Lean termination** of the reduction function (automatic via
  Lean's structural recursion checking)

We do **not** explicitly verify polynomial-time *evaluation* of the
reduction function. The output-size bound is the meaningful Karp
reduction obligation; "obviously poly-time computable in Lean" is
left as a conventional reading of the function's structure (this is
how every textbook reduction is presented). For the planned use case
(a teaching/reference library), this trade-off is appropriate. We
sacrifice formal time-bound verification to gain the ability to
write 100+ reductions in plain Lean.

The equivalence between this SAT-reducibility-based `NP` and the
standard NTM-based `NP` is folklore (Cook–Levin in its original
direction). If anyone wants the equivalence theorem, it can be
proved later as an isolated, optional one-time investment.

## Status

- ✓ Phase 0: Core types (`CNF`, `Complexity`)
- ✓ Phase 1: SAT, NP, Cook–Levin theorem
- ✓ Phase 2: Workflow validation via `ThreeSAT.lean` (Three_SAT,
  SAT_NoVar0, variable-shifting reduction)
- ◐ Phase 3: First batch of standard NP-complete problems
  - ✓ `IndependentSet` (definition only — see Phase 3 deferred work)
  - ✓ `VertexCover` + the IS↔VC duality reduction
  - ✓ `Clique` + the IS↔CLIQUE complement reduction
  - **Deferred:** the canonical SAT → IS gadget reduction. The
    bookkeeping for flat-list positions ↔ (clause, literal-in-clause)
    pairs is non-trivial and worth a separate focused session. Once
    in place, NP-hardness of `IS`, `VC`, `CLIQUE` follows by
    transitivity from the chains `SAT → IS → VC` and `SAT → IS → CLIQUE`.
- ◯ Phase 4+: 3-SAT splitting reduction, 3-COLORING,
  HAMILTONIAN-CYCLE, SUBSET-SUM, more graph problems...

## Per-problem playbook

For an NP-complete problem `L`:

1. **Define the instance type.** Use a subtype of an existing type
   when possible; otherwise define a small `structure`.
2. **Define the `DecisionProblem`.** Three fields: `α`, `pred`, `size`.
3. **Define the size measure.** Should be the natural complexity-theory
   notion (number of vertices for graph problems, number of literals
   for SAT-like problems, etc.).
4. **Prove `NP` membership** by writing a Lean function from `L.α`
   to `CNF.Formula` whose output is satisfiable iff the predicate
   holds, and bounding its output size by a polynomial. Package as a
   `Reduces L SAT`.
5. **Prove NP-hardness** by writing a Lean function from some
   already-defined NP-complete problem's instance type to `L.α`,
   with the analogous correctness biconditional and size bound.
   Package as a `Reduces (existing) L`.
6. **Optional:** prove additional reductions to/from `L` for
   convenience.

Per-problem budget under this playbook: **~100 lines**, dominated
by the correctness proofs of the reductions.

## Risks

1. **Proof noise on the eval lemmas.** The variable-shifting
   reduction's `shiftFormula_eval` proof requires ~10 lines of
   `List.all_map` / `List.any_map` / `congr` / `funext` plumbing.
   For many similar reductions, we may want to extract a small
   tactic or set of helper lemmas. *Mitigation:* deal with this
   when it actually becomes painful (after the first 5–10 problems).
2. **Subtype manipulation friction.** Working with subtype-α
   problems requires `Subtype.val` unwrapping in places. So far this
   is manageable. *Mitigation:* if it becomes annoying, define
   helper definitions on the subtype directly.
3. **Polynomial composition is `noncomputable`.** Mathlib's
   `Polynomial.X` and `Polynomial.comp` are noncomputable, so all
   our `Reduces` constructors are `noncomputable`. This is fine
   (`#print axioms` confirms only Lean core axioms are used). If
   computability ever becomes a concern, swap to a `Nat → Nat`
   bound predicate.

## First concrete next step

Pick a real NP-complete problem with a different instance type
(suggestion: **INDEPENDENT-SET** with a graph type) and complete
the per-problem playbook end-to-end. This stress-tests the
framework on a non-CNF instance type and gives us our first
"real" Karp reduction (the standard 3-SAT → INDEPENDENT-SET gadget
construction).
