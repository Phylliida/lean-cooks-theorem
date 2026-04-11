import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Common

/-!
# Step-counted reachability for set-valued transition systems

A small generic library: given a transition `step : α → Set α`,
define `stepN : α → ℕ → Set α` (configurations reachable in exactly
`n` steps), `Reaches step c c' n` (predicate version), and
`ReachesIn step c c' t` (≤ `t` steps).

The same library covers both NTM2 and NTM1 — they instantiate `α`
with their respective `Cfg` type and `step` with their respective
transition relation.
-/

namespace CooksTheorem.TM

variable {α : Type*}

/-- The set of configurations reachable from `c` in exactly `n`
single steps of `step`. Defined in "head" form: one step out of
`c`, then `n` more steps. -/
def stepN (step : α → Set α) : α → ℕ → Set α
  | c, 0 => {c}
  | c, n + 1 => ⋃ c' ∈ step c, stepN step c' n

/-- `Reaches step c c' n` iff `c'` is reachable from `c` in exactly
`n` steps. Definitionally `c' ∈ stepN step c n`. -/
def Reaches (step : α → Set α) (c c' : α) (n : ℕ) : Prop :=
  c' ∈ stepN step c n

/-- `ReachesIn step c c' t` iff `c'` is reachable from `c` in at
most `t` steps. -/
def ReachesIn (step : α → Set α) (c c' : α) (t : ℕ) : Prop :=
  ∃ n ≤ t, Reaches step c c' n

namespace stepN

variable {step : α → Set α}

@[simp]
theorem mem_zero {c c' : α} : c' ∈ stepN step c 0 ↔ c' = c := by
  simp [stepN]

@[simp]
theorem mem_succ {c c'' : α} {n : ℕ} :
    c'' ∈ stepN step c (n + 1) ↔ ∃ c', c' ∈ step c ∧ c'' ∈ stepN step c' n := by
  simp [stepN]

end stepN

namespace Reaches

variable {step : α → Set α}

theorem refl (c : α) : Reaches step c c 0 := by
  simp [Reaches]

theorem head {c c' c'' : α} {n : ℕ}
    (h₁ : c' ∈ step c) (h₂ : Reaches step c' c'' n) :
    Reaches step c c'' (n + 1) := by
  simp only [Reaches, stepN.mem_succ]
  exact ⟨c', h₁, h₂⟩

theorem tail {c c' c'' : α} {n : ℕ}
    (h₁ : Reaches step c c' n) (h₂ : c'' ∈ step c') :
    Reaches step c c'' (n + 1) := by
  induction n generalizing c with
  | zero =>
    simp only [Reaches, stepN.mem_zero] at h₁
    subst h₁
    exact head h₂ (refl c'')
  | succ k ih =>
    simp only [Reaches, stepN.mem_succ] at h₁
    obtain ⟨d, hd_step, hd_reach⟩ := h₁
    exact head hd_step (ih hd_reach)

theorem trans {a b c : α} {m n : ℕ}
    (h₁ : Reaches step a b m) (h₂ : Reaches step b c n) :
    Reaches step a c (m + n) := by
  induction m generalizing a with
  | zero =>
    simp only [Reaches, stepN.mem_zero] at h₁
    subst h₁
    simpa using h₂
  | succ k ih =>
    simp only [Reaches, stepN.mem_succ] at h₁
    obtain ⟨d, hd_step, hd_reach⟩ := h₁
    have : Reaches step a c (k + n + 1) := head hd_step (ih hd_reach)
    rwa [show k + 1 + n = k + n + 1 from by omega]

end Reaches

namespace ReachesIn

variable {step : α → Set α}

theorem refl (c : α) : ReachesIn step c c 0 :=
  ⟨0, le_refl 0, Reaches.refl c⟩

theorem of_reaches {c c' : α} {n : ℕ} (h : Reaches step c c' n) :
    ReachesIn step c c' n :=
  ⟨n, le_refl n, h⟩

theorem mono {c c' : α} {t t' : ℕ} (htt' : t ≤ t') (h : ReachesIn step c c' t) :
    ReachesIn step c c' t' := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn.trans htt', hr⟩

end ReachesIn

end CooksTheorem.TM
