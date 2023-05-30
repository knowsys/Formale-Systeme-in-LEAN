import FormalSystems.Chomsky.Regular.RegularGrammar

structure NFA (α: Type _) (qs: Type _) where
  Z: Finset α
  Q: Finset qs
  δ: (Q × Z) → Finset Q
  Q₀: Finset Q
  F: Finset Q

namespace NFA

class run (M: NFA α qs) (w: Word M.Z) (states: List M.Q): Prop where
  states_len: states.length = Nat.succ w.length

  start: 
    have q₀ := states[0]'(states_len ▸ Nat.zero_lt_succ _)
    q₀ ∈ M.Q₀

  finish:
    have qₑ := states[w.length]'(states_len ▸ Nat.lt_succ_of_le (Nat.le_refl _))
    qₑ ∈ M.F

  step: ∀(i: Fin w.length),
    have qa := states[i]'(states_len ▸ Nat.lt_succ_of_lt i.2)
    have qb := states[Nat.succ i]'
    (states_len ▸ Nat.lt_succ_of_le (Nat.le_of_lt_succ $ Nat.succ_lt_succ_iff.mpr i.2))
    qb ∈ M.δ ⟨ qa, w.get i ⟩

def generatedLanguage (M: NFA α qs) : Language M.Z :=
  fun w => ∃r: List M.Q, M.run w r

