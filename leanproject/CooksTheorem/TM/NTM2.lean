import Mathlib.Computability.TuringMachine

/-!
# Nondeterministic multi-stack Turing machine (NTM2)

A nondeterministic version of mathlib's `Turing.TM2`, the multi-stack
Turing machine with structured (block-structured) programs.

## Design

We considered three ways to extend `Turing.TM2` with nondeterminism:

1. **Wrapper.** `NTM2` contains a `Turing.TM2` plus an "override"
   transition. Rejected: the wrapper would have to subvert mathlib's
   deterministic `step`, and the override field would carry all the
   semantic content anyway. No reuse is bought.

2. **Sibling type sharing `Cfg` only.** `NTM2` has its own `NStmt`,
   its own `stepAux`, and its own `step : Cfg → Set Cfg`, but
   reuses `Turing.TM2.Cfg` directly. *This is what we use.*
   - Configuration shape (`l : Option Λ`, `var : σ`, `stk : ∀ k, List (Γ k)`)
     is determinism-agnostic, so the reuse is honest.
   - `Turing.TM2.Stmt`'s seven deterministic constructors cannot
     express nondeterministic choice without a new constructor, so
     we define `NStmt` parallel to `Turing.TM2.Stmt` with one
     additional `choose` constructor.
   - `Turing.TM2.step` returns `Option Cfg` which is structurally
     wrong for NTM (`Set Cfg`); we redefine.

3. **From-scratch.** Define everything fresh, share nothing.
   Rejected: Phase 2's simulation theorem (`NTM2to1`) wants to
   interoperate with mathlib's `TM2to1` machinery, and sharing
   `Cfg` makes that interop free.

## Nondeterminism via `choose`

The new constructor is

    choose : NStmt → NStmt → NStmt

`choose q₁ q₂` nondeterministically continues with either `q₁` or
`q₂`. Every other constructor is identical to its `Turing.TM2.Stmt`
counterpart and contributes a singleton successor set; nondeterminism
enters the machine *only* through `choose`.

A program can use `choose` followed by `load` to "guess" a bit into
the local variable store — that's enough to encode the witness-guessing
verifiers we need for Cook–Levin.
-/

namespace CooksTheorem.TM

open Turing

variable {K : Type*} (Γ : K → Type*) (Λ σ : Type*)

/-- Statements of the nondeterministic TM2 model. Mirrors
`Turing.TM2.Stmt` with one extra constructor, `choose`, for
nondeterministic branching. -/
inductive NStmt where
  | push : ∀ k, (σ → Γ k) → NStmt → NStmt
  | peek : ∀ k, (σ → Option (Γ k) → σ) → NStmt → NStmt
  | pop : ∀ k, (σ → Option (Γ k) → σ) → NStmt → NStmt
  | load : (σ → σ) → NStmt → NStmt
  | branch : (σ → Bool) → NStmt → NStmt → NStmt
  | choose : NStmt → NStmt → NStmt
  | goto : (σ → Λ) → NStmt
  | halt : NStmt

/-- A nondeterministic multi-stack Turing machine. -/
structure NTM2 where
  /-- The program: a statement body for each label. -/
  prog : Λ → NStmt Γ Λ σ
  /-- The label at which execution begins. -/
  startLabel : Λ
  /-- The designated accept label. The machine accepts whenever a
  reachable configuration has `l = some acceptLabel`. -/
  acceptLabel : Λ

variable {Γ Λ σ}

namespace NStmt

/-- One-step semantics of an `NStmt`, returning the set of successor
configurations. Identical to `Turing.TM2.stepAux` on the
deterministic constructors (each producing a singleton set), with
`choose` contributing a binary union. -/
def stepAux [DecidableEq K] :
    NStmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Set (TM2.Cfg Γ Λ σ)
  | push k f q, v, S => stepAux q v (Function.update S k (f v :: S k))
  | peek k f q, v, S => stepAux q (f v (S k).head?) S
  | pop k f q, v, S => stepAux q (f v (S k).head?) (Function.update S k (S k).tail)
  | load a q, v, S => stepAux q (a v) S
  | branch p q₁ q₂, v, S => cond (p v) (stepAux q₁ v S) (stepAux q₂ v S)
  | choose q₁ q₂, v, S => stepAux q₁ v S ∪ stepAux q₂ v S
  | goto f, v, S => {⟨some (f v), v, S⟩}
  | halt, v, S => {⟨none, v, S⟩}

end NStmt

namespace NTM2

variable [DecidableEq K]

/-- One-step transition relation: the set of configurations reachable
from `c` in a single step of `M`. The empty set if `c` is halted
(`c.l = none`). -/
def step (M : NTM2 Γ Λ σ) : TM2.Cfg Γ Λ σ → Set (TM2.Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => ∅
  | ⟨some l, v, S⟩ => NStmt.stepAux (M.prog l) v S

variable [Inhabited σ]

/-- The initial configuration on input `L`, placed on stack `k`.
The label is `M.startLabel` and the local variables start at the
`Inhabited` default. -/
def init (M : NTM2 Γ Λ σ) (k : K) (L : List (Γ k)) : TM2.Cfg Γ Λ σ :=
  ⟨some M.startLabel, default, Function.update (fun _ ↦ []) k L⟩

/-- A configuration is accepting iff its label is the accept label. -/
def IsAccepting (M : NTM2 Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : Prop :=
  c.l = some M.acceptLabel

end NTM2
end CooksTheorem.TM
