import FormalSystems.Chomsky.Regular.NFA

structure DFA (α qs: Type) where
  Z: Finset α
  Q: Finset qs
  δ: (Q × Z) → Option Q
  q₀: Q
  F: Finset Q

instance : Coe (DFA α qs) (NFA α qs) where
  coe m := { m with
    Q₀ := { m.q₀ }
    δ := Option.toFinset ∘ m.δ
  }

namespace DFA

def toNFA (M: DFA α qs) : NFA α qs := M

def accept_from (M: DFA α qs)  (start: M.Q) (w: Word M.Z) (run: List M.Q) : Prop := 
  M.toNFA.accept_from { start } w run

def GeneratedLanguage (M: DFA α qs) : Language M.Z :=
  fun w => ∃run: List M.Q, M.accept_from M.q₀ w run

theorem generated_lang_eq { M: DFA α qs } : M.GeneratedLanguage = M.toNFA.GeneratedLanguage := by
  unfold GeneratedLanguage; unfold toNFA; unfold NFA.GeneratedLanguage; simp
  apply funext; intro w; unfold accept_from; unfold toNFA; rfl

def transitionToRule (M: DFA α qs) : (M.Q × M.Z) → Option (RegularProduction M.Z M.Q)
  | (q, a) => (.cons q ∘ (a,·)) <$> M.δ (q, a)

variable [DecidableEq α] [DecidableEq qs] (M: DFA α qs)

def toGrammar (M: DFA α qs) : RegularGrammar α qs where
  Z := M.Z
  V := M.Q
  start := M.q₀
  productions := (Finset.eraseNone $ Fintype.elems.image M.transitionToRule) ∪
    M.F.map ⟨ .eps, by intro _ _; simp ⟩

theorem final_state_imp_derivation : start ∈ M.F → [.inl start] (M.toGrammar)⇒ ε := by
  intro _
  have ⟨p, hp⟩ : ∃p: M.toGrammar.productions, p.val = RegularProduction.eps start := by
    constructor
    case w =>
      constructor
      unfold toGrammar; simp
      apply Or.inr
      exists start, start.2
    case h => simp

  have lhs : Production.lhs p.val = [.inl start] := by
    rw [hp]; exact RegularProduction.eps_lhs

  rw [<- lhs]
  exists DerivationStep.fromRule p
  apply RegularProduction.eps_step_result
  exact hp

theorem state_transition_imp_derivation : q₂ ∈ M.δ (q₁, a) →
  [.inl q₁] (M.toGrammar)⇒ [.inr a, .inl q₂] := by
  intro h
  have ⟨p, hp⟩ : ∃p: M.toGrammar.productions, p.val = RegularProduction.cons q₁ (a, q₂) := by
    constructor
    case w =>
      constructor
      unfold toGrammar; simp
      apply Or.inl
      exists q₁, q₁.2, a, a.2
      simp [Fintype.complete]
      unfold transitionToRule
      simp
      exists q₂, q₂.2
    case h => simp

  have lhs : Production.lhs p.val = [.inl q₁] := by
    rw [hp]; exact RegularProduction.eps_lhs

  rw [<- lhs]
  exists DerivationStep.fromRule p
  apply RegularProduction.cons_step_result
  exact hp

theorem run_to_derivation (h: M.accept_from start word run) :
  [.inl start] (M.toGrammar)⇒* (.inr <$> word) := by
  cases h
  case final h₁ h₂ =>
    simp at h₂
    simp_rw [h₂, toNFA] at h₁
    apply Grammar.DerivationRelation.step
    . exact final_state_imp_derivation _ h₁
    . apply Grammar.DerivationRelation.same
  
  case step x w _ _ h₁ h₂ =>
    match hδ:M.δ (x, w) with
    | none =>
      simp [toNFA, hδ] at h₁
      contradiction
    | some _ =>
      simp [toNFA, hδ] at h₁
      simp at h₂ ; rw [← h₂]
      have _ := run_to_derivation h₁
      apply Grammar.DerivationRelation.step
      . exact state_transition_imp_derivation _ hδ 
      . apply Grammar.DerivationRelation.cancel_left_cons
        assumption

theorem lang_subs_grammar_lang :
  M.GeneratedLanguage ⊆ M.toGrammar.GeneratedLanguage := by
  intro w ⟨ _, h ⟩
  exact run_to_derivation M h

end DFA
