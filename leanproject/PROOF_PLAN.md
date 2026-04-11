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
`admit`**. Includes a proved-poly-time reduction and a proved
multi-tape → single-tape NTM simulation. Build everything on top of
mathlib's existing `Turing.TM*` rather than rolling our own TM model.

## Why This Is Hard

Cook–Levin is one of the larger formalizations one can attempt in
complexity theory. The reasons it's painful in any proof assistant:

1. **No off-the-shelf complexity classes.** Mathlib has Turing machines
   in `Mathlib.Computability.TuringMachine`, but they're built for
   *computability* (halting, partial recursive functions, decidable
   predicates) — there is no `P`, no `NP`, no notion of time bound, and
   no propositional-logic SAT formulation. We have to build the
   complexity-theory layer ourselves.
2. **Nondeterminism is not in mathlib's TMs.** All of `Turing.TM0`,
   `Turing.TM1`, `Turing.TM2` are deterministic (transition is a
   function `Cfg → Option Cfg`). We need to lift each model we use to
   a relational / set-valued transition.
3. **Time bounds on Turing machines are finicky.** The textbook
   definition ("M halts in ≤ p(|x|) steps") needs a clean,
   manipulable encoding of "step count" that the TM model supports.
   Mathlib's evaluation goes through `Part`/`Turing.eval`, which
   doesn't expose a step counter directly; we'll define a parallel
   `stepN` semantics that does.
4. **The multi-tape → single-tape simulation must itself be proved.**
   Mathlib has `Turing.TM2to1` which simulates multi-stack `TM2` by
   single-tape `TM1` *deterministically*. We need a nondeterministic
   analogue, with an explicit polynomial slowdown bound, and a
   correctness theorem connecting time bounds on both sides.
5. **The tableau encoding is bookkeeping-heavy.** The standard proof
   builds a 2D table of cells, defines O(n²) Boolean variables, and
   writes O(n²) clauses across four constraint families. Each
   constraint family requires its own correctness lemma. Plenty of
   off-by-one and indexing risk.
6. **The reduction must itself be poly-time computable.** It's not
   enough to *define* the formula; we need a function that constructs
   it whose runtime is bounded by a polynomial in `|x|`. That means
   building a second time-bound proof on the reduction itself.

Be honest with ourselves: a careful end-to-end proof is on the order
of thousands of lines of Lean. The plan below sequences it so we get a
working artifact at every milestone, with frequent commits and small
phase boundaries.

## What Mathlib Gives Us (and What It Doesn't)

**Have:**
- `Mathlib.Computability.TuringMachine` — `Turing.TM0`, `TM1`, `TM2`,
  `Turing.TM2to1` (single-stack and multi-stack models, plus the
  deterministic multi→single simulation).
- `Mathlib.Computability.Halting`, `Mathlib.Computability.Partrec` —
  computability theory, halting problem, partial recursive functions.
- `Mathlib.Computability.Language` — formal-language definitions
  (`Language α := Set (List α)`).
- `Mathlib.Computability.Encoding` — encodings of types into
  `List Γ` for some finite alphabet, used by the `Computability`
  hierarchy.
- General-purpose tools we'll lean on: `Polynomial`, `Finset.sum`,
  `BigOperators`, `Decidable`, `Fintype`.

**Don't have (we will build):**
- Nondeterministic versions of `Turing.TM1` and `Turing.TM2`.
- A propositional-logic AST and a `satisfiable` predicate.
- A time-bounded acceptance predicate on (nondeterministic) TMs.
- Complexity classes `P` and `NP` as `Set Language`.
- Polynomial-time many-one reductions `≤ₚ`.
- The SAT language (set of encoded satisfiable formulas).
- A nondeterministic multi-tape → single-tape simulation theorem
  with polynomial overhead.
- The Cook–Levin tableau construction.

## Locked Design Decisions

### D1. Computational model — extend mathlib's `Turing.TM2`

Build `NTM2` as a thin wrapper around `Turing.TM2`'s state, alphabet,
and configuration types, but with a *relational* transition
`step : Cfg → Set Cfg` (or `Finset Cfg` if we need decidability for
the verifier). The deterministic case `Turing.TM2.step` becomes the
special case `step c = {c'} | step₀ c = some c'` and `step c = ∅` when
`step₀ c = none`. This keeps us as compatible with mathlib's
`Turing.TM2` machinery as possible — we reuse `Cfg`, the stack/tape
representation, and as many lemmas as we can.

We will also need `NTM1` (nondeterministic single-tape) the same
way, by extending `Turing.TM1`. The tableau construction in Phase 5
operates on `NTM1`.

**Step counting** is added on top: define `stepRel : Cfg → Cfg → Prop`
from the `Set Cfg` and `Reaches : Cfg → Cfg → ℕ → Prop` as the
*indexed* transitive closure, plus an `acceptsIn (M : NTM2) (x : List Γ) (t : ℕ) : Prop`
predicate that quantifies over `Reaches` chains of length `≤ t`.

### D2. Multi-tape, with the simulation theorem proved

We'll work natively in **multi-tape** NTMs (`NTM2`-style multi-stack,
in mathlib's nomenclature) and **prove the simulation lemma**
`NTM2to1` ourselves with an explicit polynomial overhead. We do
*not* cite the simulation as a black box, because its time-bound
statement is exactly what Cook–Levin needs and mathlib's existing
`Turing.TM2to1` is deterministic-only.

This is a substantial sub-project — Phase 2 below — but it's the
right call for "no shortcuts."

### D3. Formula representation

Define a general inductive `PropFormula` *and* a CNF representation
(`List (List Literal)`), plus an equisatisfiability lemma. The
Cook–Levin construction natively produces CNF, so we never actually
run the conversion in the proof, but having both lets us state `SAT`
cleanly and reuse `PropFormula` for the verifier.

### D4. Poly-time reductions: abstract definition + concrete witnesses

The *definitions* of `P` / `NP` / `≤ₚ` use existential polynomial
bounds (`∃ p : Polynomial ℕ, ...`). But every *instance* (SAT ∈ NP,
the Cook–Levin reduction itself) exposes its concrete polynomial
witness as part of its statement, so downstream consumers don't have
to re-extract it.

### D5. Alphabet

Fix the input alphabet to `Bool` (or `Fin 2`) throughout, with TMs
allowed a larger constant tape alphabet `Γ = Fin k`. Keeps SAT
cleanly defined as a language over `Bool` without alphabet-encoding
paperwork everywhere.

## Phases

Each phase ends in a verified Lean module that compiles standalone.
Commit at every phase boundary so we can always back up.

### Phase 0 — Foundations and infrastructure

**Deliverables:**
- `CooksTheorem/PropLogic/Formula.lean` — `PropFormula`, semantics,
  `satisfies`, `satisfiable`, decidable equality on formulas.
- `CooksTheorem/PropLogic/CNF.lean` — `Literal`, `Clause`, `CNF`,
  satisfaction, `cnf_to_formula` and the equisat lemma.
- `CooksTheorem/Util/Polynomial.lean` — small wrappers
  (`IsPolyBound`, composition lemmas, `polyAdd`, `polyMul`, `polyComp`).

**Exit criterion:** can state `def isSatisfiable (φ : PropFormula) : Prop`
and prove a couple of trivial sat/unsat examples by `decide`.

### Phase 1 — Nondeterministic TM models on top of mathlib

**Deliverables:**
- `CooksTheorem/TM/NTM2.lean` — `NTM2` extending `Turing.TM2`'s
  state/alphabet/config with `step : Cfg → Set Cfg`. Inherit
  `Cfg` and the stack representation from mathlib so as much
  existing infrastructure as possible carries over.
- `CooksTheorem/TM/NTM1.lean` — analogous wrapper around
  `Turing.TM1` for the single-tape case.
- `CooksTheorem/TM/StepN.lean` — `Reaches : Cfg → Cfg → ℕ → Prop`,
  `stepN : Cfg → ℕ → Set Cfg`, and the lemmas connecting them
  (`Reaches.refl`, `Reaches.trans`, `Reaches_iff_stepN`,
  `stepN_succ`, monotonicity).
- `CooksTheorem/TM/Accepts.lean` — `accepts`, `acceptsIn`,
  `runsInTime`. State that for *deterministic* TMs (`step c` is a
  singleton when nonempty), `acceptsIn` collapses to mathlib's
  `Turing.eval`.

**Exit criterion:** define a tiny `NTM2` example (e.g., one
nondeterministically accepting `{w : w contains the substring 010}`),
prove it accepts a specific input in a specific step count by
`decide` or `simp`.

### Phase 2 — Nondeterministic multi-tape → single-tape simulation

This is the new big sub-project. Mathlib's `Turing.TM2to1` is the
guide for the construction; the work is in adapting it to
nondeterminism and bolting on a time-bound theorem.

**2a. Study `Turing.TM2to1` carefully.** Read the mathlib source,
understand the encoding of multi-stack tapes onto a single tape, the
"main loop" structure, and the existing correctness statement for
the deterministic case. Write notes in
`CooksTheorem/TM/Sim/Notes.md` so we don't have to re-derive
intuition each time we hit a snag.

**2b. Define `NTM2to1`.** A function turning an `NTM2` into an
`NTM1` whose configurations encode the multi-stack state on a single
tape. The transition function lifts each multi-tape transition to
the right number of single-tape micro-steps. **The construction is
deterministic in shape** — nondeterminism is preserved by the lifted
transition relation, not introduced.

**2c. Simulation correctness — soundness and completeness.**
- `theorem ntm2to1_complete : M.acceptsIn x t → (NTM2to1 M).acceptsIn x (overhead M t)`
- `theorem ntm2to1_sound : (NTM2to1 M).acceptsIn x t → ∃ t', M.acceptsIn x t' ∧ t' ≤ t`

**2d. Polynomial-overhead bound.** Prove
`overhead M t = c_M · t² + c_M'` (or whatever the exact bound from
the construction works out to be) and package it as
`overhead_isPoly : IsPolyBound (overhead M)`.

**2e. End-to-end corollary.** A clean lemma:
`theorem ntm2to1_polyTime : M.runsInTime p → (NTM2to1 M).runsInTime (polyComp overhead_poly p)`
that downstream phases can cite without unfolding the construction.

**Exit criterion:** all of 2c, 2d, 2e are sorry-free. Sanity-check
by running the example NTM2 from Phase 1 through `NTM2to1` and
verifying that the resulting NTM1 still accepts the same input
within the bound.

### Phase 3 — Complexity classes

**Deliverables:**
- `CooksTheorem/Complexity/Classes.lean`:
  ```lean
  def P : Set (Language Bool)
  def NP : Set (Language Bool)
  def PolyReducible (L₁ L₂ : Language Bool) : Prop  -- L₁ ≤ₚ L₂
  ```
  Definitions phrased over `NTM1` (single-tape) so the tableau in
  Phase 5 has a clean target. Multi-tape NTMs feed into these
  definitions via Phase 2's simulation corollary.
- Basic structural lemmas: `P ⊆ NP`, `≤ₚ` is reflexive and
  transitive, `NP` is closed under `≤ₚ`.
- `Complexity/MultiTape.lean`: a convenience layer for "L is in NP
  via a multi-tape verifier" — packages Phase 2's simulation so we
  can write multi-tape verifiers naturally and still land in the
  single-tape `NP` definition.

**Exit criterion:** prove the example language from Phase 1 is in
`P` (and therefore `NP`) using its concrete polynomial bound.

### Phase 4 — SAT ∈ NP

**Deliverables:**
- `CooksTheorem/SAT/Defs.lean` — `SAT : Language Bool`, the encoding
  of `PropFormula` (or `CNF`) as a `List Bool`.
- `CooksTheorem/SAT/Verifier.lean` — an explicit multi-tape NTM
  that on input `⟨φ, σ⟩` checks `σ ⊨ φ` in time linear in `|φ|`.
  Proved via Phase 3's `Complexity/MultiTape` convenience layer.
- `CooksTheorem/SAT/InNP.lean` — `theorem sat_in_NP : SAT ∈ NP`.

**Exit criterion:** `sat_in_NP` typechecks without `sorry`.

### Phase 5 — The tableau encoding (the bulk of the work)

This is where the bookkeeping piles up. Split into substeps that
each end at a checkpoint.

**5a. Tableau data structure.**
- `CooksTheorem/CookLevin/Tableau.lean`: indexing, cell contents,
  variable indexing function `var : ℕ → ℕ → CellContent → ℕ`.

**5b. Constraint families.**
- `CooksTheorem/CookLevin/Constraints/Cell.lean` — exactly-one
  cell content.
- `.../Start.lean` — initial-row constraints.
- `.../Accept.lean` — some cell contains the accept state.
- `.../Move.lean` — every 2×3 window is consistent. **This is the
  trickiest constraint** because the set of "valid windows" is
  enumerated from the NTM1's transition relation; expect to spend
  significant time on the helper lemmas. Prototype on a 2-state,
  2-symbol toy NTM1 before writing the general version.

**5c. The big formula.**
- `CooksTheorem/CookLevin/Reduction.lean`:
  ```lean
  def cookLevinFormula (M : NTM1) (p : Polynomial ℕ) (x : List Bool) : CNF
  ```
- Polynomial size bound on the formula (`O(p(|x|)²)` clauses, each
  of constant width).

**5d. Reduction soundness and completeness.**
- `theorem cookLevin_complete : M.acceptsIn x (p.eval |x|) → (cookLevinFormula M p x).Sat`
- `theorem cookLevin_sound : (cookLevinFormula M p x).Sat → M.acceptsIn x (p.eval |x|)`

Both are structural inductions on the tableau. The "sound"
direction is the harder one: from a satisfying assignment we have
to read off an actual accepting computation, including showing
that the chain of windows assembles into a valid step sequence.

**5e. Reduction is poly-time.** *Mandatory, no sorry.*
- A function `buildFormula : NTM1 → Polynomial ℕ → List Bool → CNF`
  with an explicit time bound proved by structural recursion on
  the construction. Either we write it as a `do`-block in some
  monad we can reason about, or we write it as a primitive
  recursive function with a hand-proved step count.

**Exit criterion:** all of `cookLevinFormula`, `cookLevin_complete`,
`cookLevin_sound`, and the time bound on `buildFormula` are
sorry-free.

### Phase 6 — Cook–Levin

**Deliverables:**
- `CooksTheorem/Main.lean`:
  ```lean
  theorem cook_levin (L : Language Bool) (hL : L ∈ NP) : L ≤ₚ SAT
  theorem sat_npComplete : NPComplete SAT
  ```
  Both are short consequences of Phases 4 and 5. The `cook_levin`
  proof is "unpack `hL` to get the verifier `NTM1` (multi-tape
  verifiers convert via Phase 3) and polynomial bound `p`, hand
  both to `cookLevinFormula`, cite Phase 5's correctness and
  time-bound lemmas, done."

**Exit criterion:** `theorem cook_levin` at the top of this plan
compiles with no `sorry`, no `axiom`, no `admit`. Run
`#print axioms cook_levin` and verify it depends only on Lean's
core axioms (`propext`, `Quot.sound`, `Classical.choice`).

## Risks and Where We Might Get Stuck

1. **Mathlib's `Turing.TM*` may resist nondeterministic extension.**
   The `TM2.Cfg` type and the existing lemmas may bake in
   determinism in places that bite us when we try to lift `step`
   to a `Set`. *Mitigation:* in Phase 1, write `NTM2` as a fresh
   structure that *contains* a `Turing.TM2` field plus an
   override for the transition, and verify we can still reuse
   the tape encoding without inheriting any determinism lemma.
   If that pattern doesn't work, fall back to a sibling type that
   mirrors mathlib's shape but doesn't structurally extend it.
2. **`NTM2to1` is a new sub-proof.** Mathlib's `Turing.TM2to1` is
   several hundred lines of careful construction. Adapting it to
   nondeterminism *and* adding a polynomial time bound is the
   single biggest risk in this plan after the tableau itself.
   *Mitigation:* before starting Phase 2, do a focused read of
   `Turing.TM2to1` and write `Sim/Notes.md`. If the deterministic
   lemma is structured in a way that the nondeterministic case
   factors through cleanly, great; if not, we may end up writing
   a parallel construction from scratch.
3. **The `Move` constraint.** Enumerating valid 2×3 windows
   generates a lot of cases; the soundness lemma is the single
   biggest proof-engineering risk in Phase 5. *Mitigation:*
   prototype on a 2-state, 2-symbol toy NTM1 in 5b before writing
   the general version.
4. **Polynomial composition.** Several places need to compose
   polynomials (verifier runtime composed with reduction runtime
   composed with simulation overhead). Mathlib's `Polynomial` API
   is heavy; we may want a thin `IsPolyBound : (ℕ → ℕ) → Prop`
   wrapper that says "bounded by *some* polynomial," which
   composes more cleanly than carrying `Polynomial ℕ` witnesses
   everywhere.
5. **Step counting on `Reaches`.** Defining `Reaches` as an
   inductive `Prop` is easy; getting a workable elimination
   principle for "there exists a path of length ≤ t" can be
   surprisingly painful. *Mitigation:* define both
   `Reaches : Cfg → Cfg → ℕ → Prop` (indexed) and
   `stepN : Cfg → ℕ → Set Cfg` (functional) up front, and
   prove they're equivalent so we can pick whichever is more
   convenient at each use site.
6. **Rebuild times.** Mathlib v4.25.0 is large; expect cold
   rebuilds to be slow. Use `lake exe cache get` after every dep
   change and keep modules small so re-elaboration on edit is
   fast.

## First Concrete Step

Spike Phase 0 in a single sitting: write `PropFormula`,
`satisfies`, and a 5-line example evaluated by `decide`. This
confirms the toolchain is comfortable, the editor / build loop
is responsive, and we have a feel for mathlib v4.25.0's
ergonomics before we commit to weeks of building on top of it.

After that, Phase 1 begins by reading mathlib's `Turing.TM2`
source end-to-end and sketching the `NTM2` extension we want.
