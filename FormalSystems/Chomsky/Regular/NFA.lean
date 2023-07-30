import FormalSystems.Chomsky.Regular.RegularGrammar

import Mathlib.Data.Finset.Option

structure NFA (α qs: Type) where
  Z: Finset α
  Q: Finset qs
  δ: (Q × Z) → Finset Q
  Q₀: Finset Q
  F: Finset Q

namespace NFA

inductive Run (M: NFA α qs) : M.Q → Word M.Z → Type
  | final (q: M.Q) (h: w = ε) : M.Run q w
  | step (q₁: M.Q) (q₂: M.δ (q₁, a)) (r: M.Run q₂ w) (h: w' = a :: w) : M.Run q₁ w'

variable {M: NFA α qs}

def Run.last: (r: M.Run q w) → M.Q
  | final q _ => q
  | step _ _ r _ => r.last

def Run.len: (r: M.Run q w) → Nat
  | final _ _ => 0
  | step _ _ r _ => Nat.succ r.len

def GeneratedLanguage (M: NFA α qs) : Language M.Z :=
  fun w => ∃(q₀ : M.Q₀) (run: M.Run q₀ w), run.last ∈ M.F
 
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

namespace NFA

open RegularGrammar

def Run.toDerivation
  (run: G.toNFA.Run q w)
  (h_q: q.val = .inl q')
  (hlast: run.last ∈ G.toNFA.F):
  G.RegularDerivation q' w := by
  match hrun:run with
  | final _ h =>
    apply RegularDerivation.eps; swap
    . assumption
    . simp [last, toNFA] at hlast
      cases hlast
      case inl h =>
        have := congrArg Subtype.val h
        simp [h_q] at this
      case inr h =>
        have ⟨p, ⟨_, _⟩, hp_q⟩ := h
        have hp_q := congrArg Subtype.val hp_q
        simp [h_q, Fintype.wrap] at hp_q
        rw [<- hp_q, <- RegularProduction.eq_eps_from_isEps]
        assumption
        assumption

  | step _ q₂ r h =>
    match h_q₂:q₂.val.val with
    -- derivation step of the form A -> aB
    | .inl q₂' =>
      apply RegularDerivation.step; pick_goal 3
      -- recursively define derivation
      . apply toDerivation; pick_goal 4
        exact r; exact h_q₂
        unfold last at hlast; assumption

      case h_w => assumption

      -- prove that there is a corresponding production rule
      . have p_q₂ := q₂.prop
        dsimp [toNFA] at p_q₂
        simp_rw [h_q] at p_q₂
        simp [RegularProduction.nextState, h_q₂] at p_q₂
        have ⟨prod, left, h_prod⟩ := p_q₂
        cases h_prod
        case inr h =>
          have ⟨_, _, _, c⟩ := h
          have := congrArg Subtype.val c
          simp [Fintype.wrap, h_q₂] at this
        case inl h =>
          have ⟨_, _, inner, _⟩ := h
          cases prod <;> simp [ite_eq_iff] at inner
          case cons right _ _ =>
            have ⟨⟨l, r₁⟩, r₂⟩ := inner
            have right := congrArg Subtype.val right
            simp [Fintype.wrap, h_q₂] at right
            rw [<-l, <-r₁, <-right, <-r₂, Prod.eta _]
            assumption

    -- derivation step of the form A -> a
    | .inr q₂' =>
      apply RegularDerivation.alpha; swap
      -- this is the last step
      . cases r
        case step q₃ _ _ =>
          have contra := q₃.prop
          simp [toNFA, h_q₂] at contra

        rw [h, List.cons_eq_cons]
        constructor; rfl
        assumption

      -- the step is backed by a production rule
      . have p_q₂ := q₂.prop
        dsimp [toNFA] at p_q₂
        simp_rw [h_q] at p_q₂
        simp [RegularProduction.nextState, h_q₂] at p_q₂
        have ⟨prod, _, h_prod⟩ := p_q₂
        cases h_prod
        case inl h =>
          have ⟨_, _, _, c⟩ := h
          have := congrArg Subtype.val c
          simp [Fintype.wrap, h_q₂] at this
        case inr h =>
          have ⟨_, _, inner, _⟩ := h
          cases prod <;> simp [ite_eq_iff] at inner
          rw [<- inner.1.1, <- inner.1.2]
          assumption

end NFA

theorem RegularGrammar.toNFA_lang_subs_lang:
  G.toNFA.GeneratedLanguage ⊆ G.GeneratedLanguage := by
  intro w ⟨q₀, ⟨r, hr⟩⟩
  constructor
  apply RegularDerivation.toDerivation
  apply NFA.Run.toDerivation
  . have h_q₀ := q₀.prop
    dsimp [toNFA] at h_q₀
    simp at h_q₀
    have := congrArg Subtype.val h_q₀
    simp at this
    assumption
  . assumption
