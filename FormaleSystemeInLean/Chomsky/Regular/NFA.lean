import FormaleSystemeInLean.Chomsky.Regular.RegularGrammar

import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.Sum

/--Structure: Define Nondeterministic Finite Automatas. Requires an Alphabet and Set of States. The structure includes:

- Z - An alphabet (a finite set of symbols),

- Q - A set of states,

- δ - A transition relation: takes a state and symbol and returns a set of states,

- Q₀  - A starting state (from Q),

- F - A final/terminal state (from Q).-/
structure NFA (α qs: Type) where
  /--An alphabet (a finite set of symbols)-/
  Z: Finset α
  /--A set of states-/
  Q: Finset qs
  /--A transition relation: takes a state and symbol and returns a set of states-/
  δ: (Q × Z) → Finset Q
  /--A starting state (from Q)-/
  Q₀: Finset Q
  /--A final/terminal state (from Q)-/
  F: Finset Q

namespace NFA

/--Define a run of an NFA M from a starting state for an input word.
  Is an inductive definition:

  - `final`- either the word w is`ε`and we are done, or

  - `step`- Given a previous state q₁, a proof that q₂ is the state resulting from q₁ thanks to δ,
    a run r from q₂ to w and a proof that w' is a ∘ w, we have a run from q₁ to w.-/
inductive Run (M: NFA α qs) : M.Q → Word M.Z → Type
  /--The run with zero steps reads the empty word.-/
  | final (q: M.Q) (h: w = ε) : M.Run q w
  /--Given a previous state q₁, a proof that q₂ is the state resulting from q₁ thanks to δ,
    a run r from q₂ to w and a proof that w' is a ∘ w, we have a run in M from q₁ to w'.-/
  | step (q₁: M.Q) (_: q₂ ∈ M.δ (q₁, a)) (r: M.Run q₂ w) (h: w' = a :: w) : M.Run q₁ w'

variable {M: NFA α qs}

/--The final state of a run. Is calculated using the inductive definition.-/
def Run.last: (r: M.Run q w) → M.Q
  | final q _ => q
  | step _ _ r _ => r.last

/--The length of a run. Is calculated using the inductive definition.-/
def Run.len: (r: M.Run q w) → Nat
  | final _ _ => 0
  | step _ _ r _ => Nat.succ r.len

/--The generated language of an NFA is defined as those words whose runs (starting in
  a starting state) end in a final state. Requires existance of an initial state and of such a run.
  (Reminder: a language is defined by a set inclusion criterium with input word w.)-/
def AcceptedLanguage (M: NFA α qs) : Language M.Z :=
  fun w => ∃q₀ ∈ M.Q₀, ∃run: M.Run q₀ w, run.last ∈ M.F

end NFA

variable { Z: Finset α } [DecidableEq α]
variable { V: Finset nt } [DecidableEq nt]

/---/
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

namespace NFA

open RegularGrammar

def Run.toDerivation
  (run: G.toNFA.Run q w)
  (h_q: q.val = .inl q')
  (hlast: run.last ∈ G.toNFA.F):
  G.RegularDerivation q' w :=
  match hrun:run with
  | .final _ h =>
    RegularDerivation.eps
      q'
      (by
        simp [last, toNFA] at hlast
        cases hlast with
        | inl h =>
          have := congrArg Subtype.val h
          simp [h_q] at this
        | inr h =>
          have ⟨p, ⟨_, _⟩, hp_q⟩ := h
          have hp_q := congrArg Subtype.val hp_q
          simp [h_q, Fintype.wrap] at hp_q
          rw [<- hp_q, <- RegularProduction.eq_eps_from_isEps]
          assumption
          assumption)
      h

  | .step (q₂:=q₂) (a:=a) _ h_q₂ r h =>
    match h_q₂':q₂.val with
    -- derivation step of the form A -> a
    | .inr q₂' =>
      RegularDerivation.alpha (a:=a)
        q'
        (by
          dsimp [toNFA] at h_q₂
          simp_rw [h_q] at h_q₂
          simp [RegularProduction.nextState] at h_q₂
          have ⟨prod, _, h_prod⟩ := h_q₂
          cases h_prod with
          | inl h =>
            have ⟨_, _, _, c⟩ := h
            have := congrArg Subtype.val c
            simp [Fintype.wrap, h_q₂'] at this
          | inr h =>
            cases prod <;> simp [ite_eq_iff] at h
            rw [<- h.1.1, <- h.1.2]
            assumption
        )
        (by
          cases r
          case step h _ => simp [toNFA, h_q₂'] at h
          rw [h, List.cons_eq_cons]
          constructor; rfl
          assumption
        )
    -- derivation step of the form A -> aB
    | .inl q₂' =>
      RegularDerivation.step (a:=a)
      q'
      q₂'
      (by
        dsimp [toNFA] at h_q₂
        simp_rw [h_q] at h_q₂
        simp [RegularProduction.nextState] at h_q₂
        have ⟨prod, left, h_prod⟩ := h_q₂
        cases h_prod
        case inr h =>
          have ⟨_, c⟩ := h
          have := congrArg Subtype.val c
          simp [Fintype.wrap, h_q₂'] at this
        case inl h =>
          have ⟨_, _, inner, _⟩ := h
          cases prod <;> simp [ite_eq_iff] at inner
          case cons right _ _ =>
            have ⟨⟨l, r₁⟩, r₂⟩ := inner
            have right := congrArg Subtype.val right
            simp [Fintype.wrap, h_q₂'] at right
            rw [<-l, <-r₁, <-right, <-r₂, Prod.eta _]
            assumption
      )
      h
      (toDerivation r h_q₂' hlast)

def Run.fromDerivation (d: G.RegularDerivation q w):
  G.toNFA.Run ⟨.inl q, Fintype.complete _⟩ w :=
  match d with
  | .eps _ _ h_w => final _ h_w
  | .alpha (a := a) _ _ _ =>
    Run.step (a := a) (M := G.toNFA) (q₂ := { val := Sum.inr ⟨"qₐ", by simp⟩, property := by unfold toNFA; simp; apply Fintype.complete })
      { val := Sum.inl q, property := by unfold toNFA; simp; apply Fintype.complete }
      (by
        unfold toNFA
        simp
        exists RegularProduction.alpha q a
        constructor
        . assumption
        . apply Or.inr
          simp [RegularProduction.nextState]
          rfl
      )
      (Run.final _ rfl)
      (by assumption)
  | .step (a:=a) _ q' _ _ d' =>
    Run.step (a := a) (M := G.toNFA) (q₂ := { val := Sum.inl q', property := by unfold toNFA; simp; apply Fintype.complete })
      { val := Sum.inl q, property := by unfold toNFA; simp; apply Fintype.complete }
      (by
        unfold toNFA
        simp
        exists RegularProduction.cons q (a, q')
        constructor
        . assumption
        . apply Or.inl
          exists q'
          simp [RegularProduction.nextState]
          rfl
      )
      (fromDerivation d')
      (by assumption)

theorem Run.fromDerivation_last_in_final:
  (fromDerivation G d).last ∈ G.toNFA.F := by
  match d with
  | .eps (v:=v) _ _ =>
    simp [fromDerivation, last, toNFA]
    exists .eps v
  | .alpha _ _ _ =>
    simp [last, fromDerivation, Fintype.wrap, toNFA]
  | .step _ _ _ _ _ =>
    simp [fromDerivation, last]
    apply fromDerivation_last_in_final

end NFA

theorem RegularGrammar.toNFA_lang_subs_lang:
  G.toNFA.AcceptedLanguage ⊆ G.GeneratedLanguage := by
  intro w ⟨q₀, h_q₀, r, hr⟩
  constructor
  apply RegularDerivation.toDerivation
  apply NFA.Run.toDerivation
  . dsimp [toNFA] at h_q₀
    simp at h_q₀
    have := congrArg Subtype.val h_q₀
    simp at this
    assumption
  . assumption

theorem RegularGrammar.lang_subs_toNFA_lang:
  G.GeneratedLanguage ⊆ G.toNFA.AcceptedLanguage := by
  intro w ⟨d⟩
  constructor; constructor
  simp [toNFA]; rfl
  constructor
  apply NFA.Run.fromDerivation_last_in_final
  apply RegularDerivation.fromDerivation
  assumption
  rfl

theorem RegularGrammar.lang_eq_toNFA_lang:
  G.GeneratedLanguage = G.toNFA.AcceptedLanguage := by
  apply Set.ext; intro; constructor
  apply RegularGrammar.lang_subs_toNFA_lang
  apply RegularGrammar.toNFA_lang_subs_lang
