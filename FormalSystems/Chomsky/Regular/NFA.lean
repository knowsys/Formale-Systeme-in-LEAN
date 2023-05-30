import FormalSystems.Chomsky.Regular.RegularGrammar

import Mathlib.Data.Finset.Option

structure NFA (α qs: Type) where
  Z: Finset α
  Q: Finset qs
  δ: (Q × Z) → Finset Q
  Q₀: Finset Q
  F: Finset Q

namespace NFA

def accept_from (M: NFA α qs) (current: Finset M.Q) : Word M.Z → List M.Q → Prop
  | List.nil, x :: [] => x ∈ current ∧ x ∈ M.F
  | w :: ws, x :: xs => x ∈ current ∧ M.accept_from (M.δ (x, w)) ws xs
  | _, _ => False

def GeneratedLanguage (M: NFA α qs) : Language M.Z :=
  fun w => ∃run: List M.Q, M.accept_from M.Q₀ w run

end NFA

inductive SingAcceptingState
  | accept

instance : Fintype SingAcceptingState where
  elems := { SingAcceptingState.accept }
  complete := by simp

instance : DecidableEq SingAcceptingState := fun _ _ => Decidable.isTrue rfl

variable { Z: Finset α } [DecidableEq α]
variable { V: Finset nt } [DecidableEq nt]

def RegularProduction.nextState (a: Z) (current: V):
  RegularProduction Z V → Option (V ⊕ SingAcceptingState)
  | RegularProduction.eps _ => .none
  | RegularProduction.alpha l r => if l = current ∧ r = a then .some (.inr .accept) else .none
  | RegularProduction.cons l ⟨ r1, r2 ⟩ => if l = current ∧ r1 = a then .some (.inl r2) else .none

def Fintype.wrap [inst: Fintype t] (a: t) : inst.elems := ⟨ a, Fintype.complete _ ⟩

def RegularGrammar.toNFA (G: RegularGrammar α nt) : NFA α (G.V ⊕ SingAcceptingState) where
  Z := G.Z

  Q := Fintype.elems
  Q₀ := { ⟨ .inl G.start, Fintype.complete _ ⟩ }

  F := { ⟨ .inr .accept, Fintype.complete _ ⟩ } ∪
    (G.productions.filter (fun p => p.isEps)).image λp => ⟨ .inl p.lhs, Fintype.complete _ ⟩

  δ := fun (q, a) =>
    match q.val with
    | .inr _ => {}
    | .inl q => Finset.eraseNone $ 
        G.productions.image ((Fintype.wrap <$> .) ∘ RegularProduction.nextState a q)

variable (G: RegularGrammar α nt)
def M := RegularGrammar.toNFA G

theorem nfa_lang_subs_grammar : (M G).GeneratedLanguage ⊆ G.GeneratedLanguage := by
  intro word ⟨ run, runh ⟩
  sorry
