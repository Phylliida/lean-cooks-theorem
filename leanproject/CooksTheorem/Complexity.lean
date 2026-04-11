import Mathlib.Computability.TMComputable
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Languages and the complexity classes P and NP

We use mathlib's bundled `Turing.FinTM2` (deterministic multi-stack
TM with finiteness conditions) as the underlying machine model. On
top of it we define our own minimal acceptance predicate
`AcceptsIn` (configuration-trace passes through a designated accept
label within `t` steps), then bundle it into a `Decider` carrying
a polynomial time bound.

The witness-based definition of `NP` is then:
> `L ∈ NP` iff some `Decider` accepts the encoded pair `⟨x, w⟩`
> for some witness `w` of polynomially-bounded length.
-/

namespace CooksTheorem.Complexity

open Turing

/-- A language is a set of binary strings. -/
abbrev Language := Set (List Bool)

/-! ### Pair encoding

Length-prefix encoding: `unary(|x|) ++ [false] ++ x ++ w`, so the
length of `x` can be read off the prefix and the rest of the list
splits cleanly into `x` and `w`. -/

/-- `encodePair x w = (true repeated |x| times) ++ false :: x ++ w`. -/
def encodePair (x w : List Bool) : List Bool :=
  List.replicate x.length true ++ false :: (x ++ w)

@[simp]
theorem encodePair_length (x w : List Bool) :
    (encodePair x w).length = 2 * x.length + 1 + w.length := by
  simp [encodePair, two_mul, List.length_append]
  omega

/-! ### Acceptance predicate -/

/-- The starting label of a `FinTM2` is its `main` field. -/
@[simp]
theorem initList_l (tm : FinTM2) (x : List (tm.Γ tm.k₀)) :
    (initList tm x).l = some tm.main := rfl

/-- `AcceptsIn tm acceptLabel x t` says: starting from the initial
configuration of `tm` on input `x`, some configuration on the trace
within the first `t` steps has label `some acceptLabel`. -/
def AcceptsIn (tm : FinTM2) (acceptLabel : tm.Λ)
    (x : List (tm.Γ tm.k₀)) (t : ℕ) : Prop :=
  ∃ s ≤ t, ∃ c : tm.Cfg,
    (flip bind tm.step)^[s] (some (initList tm x)) = some c ∧
    c.l = some acceptLabel

/-- `AcceptsIn` is monotone in the time bound: if a machine accepts
within `t` steps, it accepts within any `t' ≥ t`. -/
theorem AcceptsIn.mono {tm : FinTM2} {acceptLabel : tm.Λ}
    {x : List (tm.Γ tm.k₀)} {t t' : ℕ} (htt' : t ≤ t') :
    AcceptsIn tm acceptLabel x t → AcceptsIn tm acceptLabel x t' := by
  rintro ⟨s, hs, c, hc, hl⟩
  exact ⟨s, hs.trans htt', c, hc, hl⟩

/-! ### Polynomial-time deciders -/

/-- A polynomial-time decision verifier for languages over `Bool`.
Bundles a `FinTM2`, the equivalence between its input alphabet
and `Bool`, a designated accept label, and a polynomial time
bound. -/
structure Decider where
  /-- The underlying bundled deterministic TM. -/
  tm : FinTM2
  /-- The TM's input alphabet is equivalent to `Bool`. -/
  inputEquiv : tm.Γ tm.k₀ ≃ Bool
  /-- Designated accept label. -/
  acceptLabel : tm.Λ
  /-- Polynomial bound on the number of steps. -/
  time : Polynomial ℕ

namespace Decider

variable (V : Decider)

/-- Encode a `List Bool` input into the TM's native input alphabet. -/
def encodeInput (x : List Bool) : List (V.tm.Γ V.tm.k₀) :=
  x.map V.inputEquiv.symm

/-- `V` accepts the boolean input `x`: the trace from `x`'s encoded
initial configuration passes through `V.acceptLabel` within
`V.time.eval x.length` steps. -/
def Accepts (x : List Bool) : Prop :=
  AcceptsIn V.tm V.acceptLabel (V.encodeInput x) (V.time.eval x.length)

end Decider

/-! ### The classes P and NP -/

/-- The complexity class P: languages decidable in polynomial time. -/
def P : Set Language :=
  { L | ∃ V : Decider, ∀ x, x ∈ L ↔ V.Accepts x }

/-- The complexity class NP, witness-based formulation: a language
`L` is in `NP` iff there is a polynomial-time `Decider V` and a
polynomial witness-length bound `witnessLen` such that `x ∈ L`
exactly when some witness `w` of length `≤ witnessLen(|x|)` makes
`V` accept the encoded pair `⟨x, w⟩`. -/
def NP : Set Language :=
  { L | ∃ (V : Decider) (witnessLen : Polynomial ℕ),
      ∀ x, x ∈ L ↔ ∃ w : List Bool,
        w.length ≤ witnessLen.eval x.length ∧
        V.Accepts (encodePair x w) }

end CooksTheorem.Complexity
