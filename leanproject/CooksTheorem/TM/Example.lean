import CooksTheorem.TM.Accepts

/-!
# Worked example of an NTM2

A trivial machine that immediately jumps to its accept label, and a
proof that it accepts the empty input in one step. This is the
Phase 1 exit criterion: it confirms the NTM2 model + step-counted
reachability + acceptance predicates compose into something one
can actually compute with.
-/

namespace CooksTheorem.TM.Example

open CooksTheorem.TM Turing

/-- Two-state machine: start and accept. -/
inductive Q where
  | start
  | accept
  deriving DecidableEq

/-- A single-stack NTM2 with empty stack alphabet whose program
unconditionally jumps from `start` to `accept` and then halts. -/
def trivial : NTM2 (K := Unit) (fun _ => Empty) Q Unit where
  prog
    | .start => .goto (fun _ => .accept)
    | .accept => .halt
  startLabel := .start
  acceptLabel := .accept

/-- The trivial machine accepts the empty input in one step. -/
example : trivial.AcceptsIn () [] 1 := by
  refine ⟨⟨some .accept, (), fun _ => []⟩, ⟨1, le_refl _, ?_⟩, rfl⟩
  simp [Reaches, stepN, NTM2.step, NTM2.init, NStmt.stepAux, trivial]

/-- Nondeterministic example: from `start`, the machine guesses
between jumping to `accept` (good) or looping back to `start`
(unproductive). At least one path accepts, so the machine accepts. -/
def nondet : NTM2 (K := Unit) (fun _ => Empty) Q Unit where
  prog
    | .start => .choose (.goto (fun _ => .accept)) (.goto (fun _ => .start))
    | .accept => .halt
  startLabel := .start
  acceptLabel := .accept

/-- The nondeterministic machine accepts the empty input in one step,
witnessed by the left branch of `choose`. -/
example : nondet.AcceptsIn () [] 1 := by
  refine ⟨⟨some .accept, (), fun _ => []⟩, ⟨1, le_refl _, ?_⟩, rfl⟩
  simp [Reaches, stepN, NTM2.step, NTM2.init, NStmt.stepAux, nondet]

end CooksTheorem.TM.Example
