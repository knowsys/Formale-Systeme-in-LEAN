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

theorem accept_from_empty : accept_from M current word [] = False := by 
  unfold accept_from
  split
  . contradiction
  . contradiction
  . rfl

theorem accept_from_contains (h: accept_from M current word (x :: xs)) : x ∈ current := by
  unfold accept_from at h
  split at h
  case h_1 h eq => exact (List.cons_eq_cons.mp eq).1 ▸ h.1
  case h_2 h eq => exact (List.cons_eq_cons.mp eq).1 ▸ h.1
  case h_3 => apply False.elim; assumption

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

theorem nfa_run_to_derivation_1 (runh: (M G).accept_from (M G).Q₀ w (⟨ .inl x, p ⟩ :: xs)) :
  [.inl x] (G)⇒* (.inr <$> w) := by
  match xs, w with
  -- in this case there is a rule S -> ε
  | [], [] =>
    cases runh
    case intro _ r =>
      unfold M RegularGrammar.toNFA at r; simp at r
      simp; sorry

  -- this cannot happen
  | [], w :: ws => sorry

  -- a rule S -> a
  | [ ⟨ .inr _ , _ ⟩ ], [ a ] => sorry

  -- finally a rule S -> w x'
  | x' :: xs, w :: ws => sorry

theorem nfa_run_to_derivation_2 (runh: (M G).accept_from ((M G).δ (q, a)) w (⟨ .inl x, p ⟩ :: xs)) :
  [.inl x] (G)⇒* (.inr <$> w) := by
  match xs, w with
  -- in this case there is a rule A -> ε
  | [], [] =>
    cases runh
    case intro l r => sorry

  -- this cannot happen
  | [], w :: ws => sorry

  -- a rule A -> a
  | [ ⟨ .inr _ , _ ⟩ ], [ a ] => sorry

  -- finally a rule A -> w x'
  | x' :: xs, w :: ws => sorry

theorem nfa_lang_subs_grammar : (M G).GeneratedLanguage ⊆ G.GeneratedLanguage := by
  intro word ⟨ run, runh ⟩
  match run with
  -- empty runs are not valid
  | [] => apply False.elim; exact NFA.accept_from_empty ▸ runh 

  -- in this case the run would begin with the single accepting state, which is not in Q₀
  | ⟨ .inr _, _ ⟩ :: _ =>
    have p := NFA.accept_from_contains runh
    unfold M RegularGrammar.toNFA at p; simp at p

  -- this is the interesting case, where v ∈ Q₀ and thus v = G.start
  | ⟨ .inl v, _ ⟩ :: _ =>
      have p := NFA.accept_from_contains runh
      unfold M RegularGrammar.toNFA at p; simp at p
      have tmp := nfa_run_to_derivation_1 G runh
      rw [p] at tmp
      exact tmp
