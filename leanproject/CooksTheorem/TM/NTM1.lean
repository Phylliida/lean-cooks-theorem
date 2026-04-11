import Mathlib.Computability.PostTuringMachine

/-!
# Nondeterministic single-tape Turing machine (NTM1)

A nondeterministic version of mathlib's `Turing.TM1`, the
single-bidirectional-tape Turing machine with structured programs.

The design mirrors `CooksTheorem.TM.NTM2` exactly: parallel `Stmt`
type (`NStmt1`) with one extra `choose` constructor for
nondeterministic branching, set-valued `stepAux`, and an `NTM1`
structure carrying the program and a designated accept label.
`Turing.TM1.Cfg` is reused directly since the configuration shape
(`l : Option Λ`, `var : σ`, `Tape : Tape Γ`) is determinism-agnostic.
-/

namespace CooksTheorem.TM

open Turing

variable (Γ : Type*) (Λ σ : Type*)

/-- Statements of the nondeterministic TM1 model. Mirrors
`Turing.TM1.Stmt` with one extra constructor, `choose`, for
nondeterministic branching. -/
inductive NStmt1 where
  | move : Dir → NStmt1 → NStmt1
  | write : (Γ → σ → Γ) → NStmt1 → NStmt1
  | load : (Γ → σ → σ) → NStmt1 → NStmt1
  | branch : (Γ → σ → Bool) → NStmt1 → NStmt1 → NStmt1
  | choose : NStmt1 → NStmt1 → NStmt1
  | goto : (Γ → σ → Λ) → NStmt1
  | halt : NStmt1

/-- A nondeterministic single-tape Turing machine. -/
structure NTM1 where
  /-- The program: a statement body for each label. -/
  prog : Λ → NStmt1 Γ Λ σ
  /-- The label at which execution begins. -/
  startLabel : Λ
  /-- The designated accept label. The machine accepts whenever a
  reachable configuration has `l = some acceptLabel`. -/
  acceptLabel : Λ

variable {Γ Λ σ}

namespace NStmt1

/-- One-step semantics of an `NStmt1`, returning the set of successor
configurations. Identical to `Turing.TM1.stepAux` on the
deterministic constructors (each producing a singleton set), with
`choose` contributing a binary union. -/
def stepAux [Inhabited Γ] :
    NStmt1 Γ Λ σ → σ → Tape Γ → Set (TM1.Cfg Γ Λ σ)
  | move d q, v, T => stepAux q v (T.move d)
  | write a q, v, T => stepAux q v (T.write (a T.1 v))
  | load s q, v, T => stepAux q (s T.1 v) T
  | branch p q₁ q₂, v, T => cond (p T.1 v) (stepAux q₁ v T) (stepAux q₂ v T)
  | choose q₁ q₂, v, T => stepAux q₁ v T ∪ stepAux q₂ v T
  | goto l, v, T => {⟨some (l T.1 v), v, T⟩}
  | halt, v, T => {⟨none, v, T⟩}

end NStmt1

namespace NTM1

variable [Inhabited Γ]

/-- One-step transition relation: the set of configurations reachable
from `c` in a single step of `M`. The empty set if `c` is halted
(`c.l = none`). -/
def step (M : NTM1 Γ Λ σ) : TM1.Cfg Γ Λ σ → Set (TM1.Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => ∅
  | ⟨some l, v, T⟩ => NStmt1.stepAux (M.prog l) v T

variable [Inhabited σ]

/-- The initial configuration on input `L`, placed on the tape
starting at the head and going right. -/
def init (M : NTM1 Γ Λ σ) (L : List Γ) : TM1.Cfg Γ Λ σ :=
  ⟨some M.startLabel, default, Tape.mk₁ L⟩

/-- A configuration is accepting iff its label is the accept label. -/
def IsAccepting (M : NTM1 Γ Λ σ) (c : TM1.Cfg Γ Λ σ) : Prop :=
  c.l = some M.acceptLabel

end NTM1
end CooksTheorem.TM
