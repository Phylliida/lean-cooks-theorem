# Proof Plan: Cook–Levin Theorem in Lean 4

## Goal

Formalize and prove the **Cook–Levin theorem** in Lean 4 + mathlib:

> **SAT is NP-complete.** Equivalently: every language in NP polynomial-time
> many-one reduces to the Boolean satisfiability problem.

The full statement we want to land in `CooksTheorem/Main.lean`:

```lean
theorem cook_levin :
    ∀ L : Language, L ∈ NP → L ≤ₚ SAT
```

with `SAT` itself proved to be in `NP` as a corollary, giving NP-completeness.

**Scope, locked in:** end-to-end proof, **zero `sorry` / `axiom` /
`admit`**, with a proved-poly-time reduction.

## Pivot history

The original plan had a Phase 1 building nondeterministic Turing machines
(`NTM2`, `NTM1`) on top of mathlib's `Turing.TM2`/`TM1`, and a Phase 2
proving a nondeterministic multi-tape → single-tape simulation
(`NTM2to1`) with a polynomial overhead bound. That entire body of work
was estimated at ~1000 lines of intricate `ListBlank`/`Tape` proof
engineering.

We pivoted to the **witness-based definition of `NP`**: rather than
"`L ∈ NP` iff some nondeterministic poly-time TM accepts `L`", we use
the equivalent "`L ∈ NP` iff some *deterministic* poly-time TM `V`
and polynomial `p` satisfy `x ∈ L ↔ ∃ w, |w| ≤ p(|x|), V(⟨x, w⟩) = accept`".
This formulation:

- needs only deterministic TMs, so we can use mathlib's `Turing.TM2` /
  `Turing.FinTM2` directly with no nondeterministic infrastructure;
- doesn't require us to write any TM-to-TM simulation, since the
  Cook–Levin tableau encodes both tape contents and witness bits as
  SAT variables (the witness bits become "free variables" the
  satisfying assignment picks);
- is mathematically equivalent to the NTM-based definition (standard
  textbook result);
- collapses the original Phase 1 + Phase 2 into a single small phase.

The deleted files (`CooksTheorem/TM/NTM2.lean`, `NTM1.lean`, `StepN.lean`,
`Accepts.lean`, `Example.lean`, `Sim/Notes.md`) live in commit history.

## Why This Is Still Hard

Even after the pivot, this is one of the larger formalizations one
can attempt in complexity theory:

1. **No off-the-shelf complexity classes.** Mathlib has Turing
   machines and bundled `FinTM2`/`TM2OutputsInTime` for *function
   computation*, but not `P`, not `NP`, not propositional SAT, not
   the Cook–Levin tableau. We build all of it.
2. **The tableau encoding is bookkeeping-heavy.** The standard proof
   builds a 2D table of cells, defines O(n²) Boolean variables, and
   writes O(n²) clauses across four constraint families. Each
   constraint family requires its own correctness lemma. Plenty of
   off-by-one and indexing risk.
3. **The reduction must itself be poly-time computable.** It's not
   enough to *define* the formula; we need a function that constructs
   it whose runtime is bounded by a polynomial in `|x|`. That means
   building a second time-bound proof on the reduction itself.
4. **Mathlib's `FinTM2` is multi-stack, not single-tape.** The
   tableau is most cleanly built on a single-tape machine, which
   means we either build the tableau over multi-stack configurations
   (more complex constraints) or invoke mathlib's `Turing.TM2to1`
   construction and prove it polynomial. We'll cross that bridge
   when we get to it.

## What Mathlib Gives Us

**Have:**
- `Mathlib.Computability.TuringMachine` — `Turing.TM0`, `TM1`, `TM2`
  models, plus the deterministic `Turing.TM2to1` simulation (with
  evaluation correctness, no time bound).
- `Mathlib.Computability.TMComputable` — `FinTM2` (bundled
  finite-state TM2), `EvalsTo` / `EvalsToInTime` (step-counted
  iteration), `TM2OutputsInTime`, `TM2ComputableInPolyTime` for
  function computation.
- `Mathlib.Computability.Encoding` — `Encoding`, `FinEncoding`
  infrastructure, encoders for `Bool`, `Nat`, etc.
- `Mathlib.Computability.Language` — `Language α := Set (List α)`.
- General-purpose tools: `Polynomial`, `Finset`, `Decidable`,
  `Fintype`.

**Don't have (we will build):**
- A propositional-logic AST and a `Satisfiable` predicate.
  *(Phase 0, done.)*
- An acceptance predicate for `FinTM2` that doesn't impose mathlib's
  restrictive output convention. *(Phase 1, done.)*
- A bundled poly-time decider, `P`, and `NP`. *(Phase 1, done.)*
- The SAT language and a verifier proving `SAT ∈ NP`. *(Phase 2.)*
- The Cook–Levin tableau construction. *(Phase 3.)*
- The final assembly. *(Phase 4.)*

## Locked Design Decisions

### D1. Computational model

Use mathlib's `Turing.FinTM2` (bundled deterministic multi-stack
TM with `Fintype`/`DecidableEq` on `K`/`Λ`/`σ`) as the underlying
machine.

### D2. Acceptance predicate

We do **not** use mathlib's `TM2OutputsInTime`, which is designed
for function computation and forces the TM to leave `var` at
`initialState` and clean up all non-output stacks before halting.
Instead our `AcceptsIn tm acceptLabel x t` says:

> Some configuration on the trace of `tm` from input `x` within the
> first `t` steps has label `some acceptLabel`.

This is much friendlier to writing verifiers that just want to
"jump to accept and stop caring".

### D3. Witness-based NP

```lean
def NP : Set Language :=
  { L | ∃ (V : Decider) (witnessLen : Polynomial ℕ),
      ∀ x, x ∈ L ↔ ∃ w : List Bool,
        w.length ≤ witnessLen.eval x.length ∧
        V.Accepts (encodePair x w) }
```

`encodePair x w := unary(|x|) ++ false :: x ++ w` — length-prefix
encoding so `(x, w)` can be recovered.

### D4. Formula representation

Define a general inductive `PropFormula` *and* a CNF representation
when Phase 3 needs it. The Cook–Levin construction natively
produces CNF, so we'll define both with an equisatisfiability
lemma.

### D5. Poly-time reductions: abstract definition + concrete witnesses

`P` / `NP` definitions use existential polynomial bounds. Every
*instance* (the SAT verifier, the Cook–Levin reduction itself)
exposes its concrete polynomial witness as part of its statement.

### D6. Alphabet

Input alphabet is `Bool`. The TM's tape alphabets can be richer;
the `Decider` carries an `Equiv` between its input stack alphabet
and `Bool` so callers always work with `List Bool`.

## Phases

Each phase ends in a verified Lean module that compiles standalone.
Commit at every phase boundary so we can always back up.

### Phase 0 — Propositional logic foundations ✓ DONE

`CooksTheorem/PropLogic/Formula.lean`: `PropFormula`, `eval`,
`Satisfies`, `Satisfiable`, two `decide`-checked examples. About
55 lines.

We'll add `CooksTheorem/PropLogic/CNF.lean` (Literal / Clause /
CNF / equisat lemma) at the start of Phase 3, when the tableau
needs it.

### Phase 1 — Complexity classes ✓ DONE

`CooksTheorem/Complexity.lean`: `Language`, `encodePair` with a
length lemma, `AcceptsIn`, `Decider`, `P`, `NP`. About 100 lines.

### Phase 2 — SAT ∈ NP

**Deliverables:**
- `CooksTheorem/SAT/Encoding.lean` — encoding of `PropFormula`
  as `List Bool` and a decoder, plus `decode_encode` round-trip.
- `CooksTheorem/SAT/Defs.lean` — the SAT language as a `Language`.
- `CooksTheorem/SAT/Verifier.lean` — a concrete `FinTM2` that
  reads an encoded formula plus an encoded assignment from its
  input stack, evaluates the formula on the assignment, and
  jumps to its accept label iff the result is `true`.
- `CooksTheorem/SAT/InNP.lean` — `theorem sat_in_NP : SAT ∈ NP`.
  The witness is the assignment.

The verifier's correctness proof is the bulk of the work for this
phase. Time bound: linear in the encoded input length.

**Exit criterion:** `theorem sat_in_NP : SAT ∈ NP` typechecks
sorry-free, and `#print axioms sat_in_NP` shows only Lean core
axioms.

### Phase 3 — The Cook–Levin tableau

This is the bulk of the formalization. Split into substeps that
each end at a checkpoint.

**3a. CNF infrastructure.**
- `CooksTheorem/PropLogic/CNF.lean` — `Literal`, `Clause`, `CNF`,
  satisfaction, conversion to `PropFormula` and equisat lemma.

**3b. Tableau data structure.**
- `CooksTheorem/CookLevin/Tableau.lean` — indexing, cell contents,
  variable indexing function `var : ℕ → ℕ → CellContent → ℕ`.
  Decision: do we build the tableau on a single-tape machine
  (requires `Turing.TM2to1`-style preprocessing of the verifier
  and a polynomial-time bound on it), or on the multi-stack
  `FinTM2` directly (more complex constraints)? Resolve at the
  start of 3b.

**3c. Constraint families.**
- `.../Constraints/Cell.lean` — exactly-one cell content.
- `.../Constraints/Start.lean` — initial-row constraints
  (encodes both input and the witness's free bits).
- `.../Constraints/Accept.lean` — some cell contains the accept
  label.
- `.../Constraints/Move.lean` — every 2×3 window (or its
  multi-stack analogue) is consistent. **The trickiest constraint**
  because the set of "valid windows" is enumerated from the TM's
  transition relation. Prototype on a 2-state, 2-symbol toy TM
  before writing the general version.

**3d. The big formula.**
- `CooksTheorem/CookLevin/Reduction.lean`:
  ```lean
  def cookLevinFormula (V : Decider) (witnessLen : Polynomial ℕ)
    (x : List Bool) : CNF
  ```
- Polynomial size bound on the formula
  (`O((V.time(2|x|+1+witnessLen|x|)² + ...))` clauses).

**3e. Reduction soundness and completeness.**
- `theorem cookLevin_complete : (∃ w, V.Accepts (encodePair x w)) → (cookLevinFormula V wL x).Sat`
- `theorem cookLevin_sound : (cookLevinFormula V wL x).Sat → (∃ w, V.Accepts (encodePair x w))`

Both are structural inductions on the tableau. The "sound"
direction is the harder one.

**3f. Reduction is poly-time.** *Mandatory, no sorry.*
- A function `buildFormula` with an explicit poly-time bound
  proved by structural recursion on the construction.

**Exit criterion:** all of `cookLevinFormula`, `cookLevin_complete`,
`cookLevin_sound`, and the time bound on `buildFormula` are
sorry-free.

### Phase 4 — Cook–Levin

**Deliverables:**
- `CooksTheorem/Main.lean`:
  ```lean
  theorem cook_levin (L : Language) (hL : L ∈ NP) : L ≤ₚ SAT
  theorem sat_npComplete : NPComplete SAT
  ```
  The `cook_levin` proof is "unpack `hL` to get the verifier `V`
  and witness-length `p`; hand both to `cookLevinFormula`; cite
  Phase 3's correctness and time-bound lemmas; done."

**Exit criterion:** `theorem cook_levin` at the top of this plan
compiles with no `sorry`, no `axiom`, no `admit`. Run
`#print axioms cook_levin` and verify it depends only on Lean's
core axioms.

## Risks and Where We Might Get Stuck

1. **Tableau over multi-stack vs single-tape.** Building the
   tableau over `FinTM2`'s multi-stack configuration is novel
   territory; building over a single-tape machine requires us to
   either restrict to TM1-like deciders (forcing a one-stack
   `FinTM2`) or invoke and prove polynomial bounds on
   `Turing.TM2to1`. *Mitigation:* in Phase 3a, prototype on a
   one-stack `Decider` first to keep the tableau 2D.
2. **The `Move` constraint.** Enumerating valid 2×3 windows
   generates a lot of cases; the soundness lemma is the single
   biggest proof-engineering risk. *Mitigation:* prototype on a
   2-state, 2-symbol toy `Decider` in 3c before writing the
   general version.
3. **Polynomial composition.** Several places need to compose
   polynomials (verifier runtime composed with reduction runtime).
   Mathlib's `Polynomial` API is heavy; consider a thin
   `IsPolyBound : (ℕ → ℕ) → Prop` wrapper that says "bounded by
   *some* polynomial," which composes more cleanly than carrying
   `Polynomial ℕ` witnesses everywhere.
4. **Rebuild times.** Mathlib v4.25.0 is large; expect cold
   rebuilds to be slow. Use `lake exe cache get` after every dep
   change and keep modules small so re-elaboration on edit is
   fast.

## Status

- Phase 0: ✓ complete (`PropLogic/Formula.lean`)
- Phase 1: ✓ complete (`Complexity.lean`)
- Phase 2: not started (next)
- Phase 3: not started
- Phase 4: not started
