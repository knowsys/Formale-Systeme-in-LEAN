import FormalSystems.Chomsky.Regular.RegularGrammar

import Mathlib.Data.Finset.Option

structure NFA (α qs: Type) where
  Z: Finset α
  Q: Finset qs
  δ: (Q × Z) → Finset Q
  Q₀: Finset Q
  F: Finset Q

namespace NFA

inductive accept_from (M: NFA α qs) : Finset M.Q → Word M.Z → List M.Q → Prop
  | final (h₁: x ∈ current) (h₂: x ∈ M.F) : M.accept_from current [] [x]
  | step (h₁: x ∈ current) : M.accept_from (M.δ (x, w)) ws xs -> M.accept_from current (w::ws) (x::xs)

theorem accept_from_contains (h: accept_from M current word (x :: xs)) : x ∈ current := by
  cases h
  case step r _ => exact r
  case final r => exact r

def GeneratedLanguage (M: NFA α qs) : Language M.Z :=
  fun w => ∃run: List M.Q, M.accept_from M.Q₀ w run

end NFA

variable { Z: Finset α } [DecidableEq α]
variable { V: Finset nt } [DecidableEq nt]

def RegularProduction.nextState (a: Z) (current: V):
  RegularProduction Z V → Option (V ⊕ ({ "qₐ" }: Finset _))
  | RegularProduction.eps _ => .none
  | RegularProduction.alpha l r => if l = current ∧ r = a then .some (.inr ⟨"qₐ", by simp⟩) else .none
  | RegularProduction.cons l ⟨ r1, r2 ⟩ => if l = current ∧ r1 = a then .some (.inl r2) else .none

def Fintype.wrap [inst: Fintype t] (a: t) : inst.elems := ⟨ a, Fintype.complete _ ⟩

def RegularGrammar.toNFA (G: RegularGrammar α nt) : NFA α (G.V ⊕ ({ "qₐ" }: Finset _)) where
  Z := G.Z

  Q := Fintype.elems
  Q₀ := { ⟨ .inl G.start, Fintype.complete _ ⟩ }

  F := { ⟨ .inr ⟨"qₐ", by simp⟩, Fintype.complete _ ⟩ } ∪
    (G.productions.filter (·.isEps)).image (Fintype.wrap ∘ .inl ∘ (·.lhs))

  δ := fun (q, a) =>
    match q.val with
    | .inr _ => {}
    | .inl q => Finset.eraseNone $ 
        G.productions.image ((Fintype.wrap <$> .) ∘ RegularProduction.nextState a q)

variable (G: RegularGrammar α nt)
def M := RegularGrammar.toNFA G

theorem nfa_run_to_derivation_1 (runh: (M G).accept_from (M G).Q₀ w run) :
  [.inl x] (G)⇒* (.inr <$> w) := by
  sorry

theorem nfa_run_to_derivation_2 (runh: (M G).accept_from ((M G).δ (q, a)) w run) :
  [.inl x] (G)⇒* (.inr <$> w) := by
  sorry

theorem nfa_lang_subs_grammar : (M G).GeneratedLanguage ⊆ G.GeneratedLanguage := by
  intro word ⟨ run, runh ⟩
  exact nfa_run_to_derivation_1 _ runh
