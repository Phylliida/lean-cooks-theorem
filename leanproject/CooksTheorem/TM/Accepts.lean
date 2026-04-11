import CooksTheorem.TM.NTM2
import CooksTheorem.TM.NTM1
import CooksTheorem.TM.StepN

/-!
# Acceptance and time bounds

`Accepts`, `AcceptsIn`, and `RunsInTime` for both NTM2 and NTM1.

`AcceptsIn M x t` means there is some accepting configuration
reachable from `M.init x` in at most `t` steps. `RunsInTime M f`
says that the time bound `f` is tight enough: every accepted input
is accepted within `f (|x|)` steps.
-/

namespace CooksTheorem.TM

namespace NTM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] [Inhabited σ]

/-- `M` accepts input `L` placed on stack `k` if some reachable
configuration is accepting. -/
def Accepts (M : NTM2 Γ Λ σ) (k : K) (L : List (Γ k)) : Prop :=
  ∃ c, (∃ n, Reaches M.step (M.init k L) c n) ∧ M.IsAccepting c

/-- `M` accepts input `L` in at most `t` steps. -/
def AcceptsIn (M : NTM2 Γ Λ σ) (k : K) (L : List (Γ k)) (t : ℕ) : Prop :=
  ∃ c, ReachesIn M.step (M.init k L) c t ∧ M.IsAccepting c

/-- `M` runs in time `f` if every accepted input is accepted within
`f (length of input)` steps. -/
def RunsInTime (M : NTM2 Γ Λ σ) (f : ℕ → ℕ) : Prop :=
  ∀ k (L : List (Γ k)), Accepts M k L ↔ AcceptsIn M k L (f L.length)

theorem accepts_of_acceptsIn {M : NTM2 Γ Λ σ} {k : K} {L : List (Γ k)} {t : ℕ}
    (h : AcceptsIn M k L t) : Accepts M k L := by
  obtain ⟨c, ⟨n, _, hr⟩, hc⟩ := h
  exact ⟨c, ⟨n, hr⟩, hc⟩

end NTM2

namespace NTM1

variable {Γ : Type*} {Λ σ : Type*}
variable [Inhabited Γ] [Inhabited σ]

/-- `M` accepts input `L` if some reachable configuration is
accepting. -/
def Accepts (M : NTM1 Γ Λ σ) (L : List Γ) : Prop :=
  ∃ c, (∃ n, Reaches M.step (M.init L) c n) ∧ M.IsAccepting c

/-- `M` accepts input `L` in at most `t` steps. -/
def AcceptsIn (M : NTM1 Γ Λ σ) (L : List Γ) (t : ℕ) : Prop :=
  ∃ c, ReachesIn M.step (M.init L) c t ∧ M.IsAccepting c

/-- `M` runs in time `f` if every accepted input is accepted within
`f (length of input)` steps. -/
def RunsInTime (M : NTM1 Γ Λ σ) (f : ℕ → ℕ) : Prop :=
  ∀ L, Accepts M L ↔ AcceptsIn M L (f L.length)

theorem accepts_of_acceptsIn {M : NTM1 Γ Λ σ} {L : List Γ} {t : ℕ}
    (h : AcceptsIn M L t) : Accepts M L := by
  obtain ⟨c, ⟨n, _, hr⟩, hc⟩ := h
  exact ⟨c, ⟨n, hr⟩, hc⟩

end NTM1

end CooksTheorem.TM
