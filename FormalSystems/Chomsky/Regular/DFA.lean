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

def Run (M: DFA α qs) := M.toNFA.Run

def GeneratedLanguage (M: DFA α qs) : Language M.Z :=
  fun w => ∃run: M.Run M.q₀ w, run.last ∈ M.F

theorem generated_lang_eq { M: DFA α qs } :
  M.GeneratedLanguage = M.toNFA.GeneratedLanguage := by
  unfold GeneratedLanguage
  unfold toNFA; unfold NFA.GeneratedLanguage
  simp; rfl

def transitionToRule (M: DFA α qs) : (M.Q × M.Z) → Option (RegularProduction M.Z M.Q)
  | (q, a) => (.cons q ∘ (a,·)) <$> M.δ (q, a)

variable [DecidableEq α] [DecidableEq qs] (M: DFA α qs)

def toGrammar (M: DFA α qs) : RegularGrammar α qs where
  Z := M.Z
  V := M.Q
  start := M.q₀
  productions := (Finset.eraseNone $ Fintype.elems.image M.transitionToRule) ∪
    M.F.map ⟨ .eps, by intro _ _; simp ⟩

def final_state_to_derivation_step (state: M.F) : M.toGrammar.DerivationStep [.inl state.val] where
  pre := ε
  suf := ε
  prod := by
    constructor
    dsimp [toGrammar]
    simp
    apply Or.inr
    exists state.val, state.val.property
    constructor
    exact state.property
    rfl

  sound := by
    rfl

theorem final_state_to_derivation_step_rhs (state: M.F) :
  (M.final_state_to_derivation_step state).result = ε := by
  rfl

def state_transition_to_derivation_step (a: M.Z) (q₁ q₂: M.Q) (h: q₂ ∈ M.δ (q₁, a)) :
  M.toGrammar.DerivationStep [.inl q₁] where
  pre := ε
  suf := ε
  prod := by
    constructor
    dsimp [toGrammar]; simp
    apply Or.inl
    exists q₁, q₁.2, a, a.2
    simp [Fintype.complete, transitionToRule]
    exists q₂, q₂.2
  sound := by rfl

theorem state_transition_imp_derivation (h : q₂ ∈ M.δ (q₁, a)) :
  (M.state_transition_to_derivation_step _ _ _ h).result = [.inr a, .inl q₂] := by
  rfl

def Run.toDerivation (run: M.Run start word) (hlast: run.last ∈ M.F):
  { d: M.toGrammar.Derivation (.inr <$> word) // (d.lhs = [.inl start]) } := by
  cases run
  case final =>
    unfold NFA.Run.last at hlast
    simp; rw [<- Word.eps_eq_nil]
    rw [<- M.final_state_to_derivation_step_rhs]; swap
    exact ⟨ start, hlast ⟩
    constructor; swap
    . apply Grammar.Derivation.step
      apply Grammar.Derivation.same
      rfl
    . simp [Grammar.Derivation.lhs, final_state_to_derivation_step_rhs]

  case step a _ qn run' =>
    unfold NFA.Run.last at hlast
    have ⟨ d', hd' ⟩ := DFA.Run.toDerivation run' hlast
    simp [toNFA] at a
    constructor; swap
    apply (d'.augment_left_cons _).prepend
    rw [d'.augment_left_cons_lhs]
    simp_rw [hd']
    apply state_transition_imp_derivation (q₁ := start)
    have ⟨_, p⟩ := qn
    simp [toNFA] at p
    rw [Option.mem_iff]
    exact p
    apply Grammar.Derivation.prepend_lhs

theorem lang_subs_grammar_lang :
  M.GeneratedLanguage ⊆ M.toGrammar.GeneratedLanguage := by
  intro _ ⟨ run, h ⟩
  have ⟨d, _⟩ := run.toDerivation _ h
  exists d

theorem eps_production_imp_final (h: RegularProduction.eps q ∈ M.toGrammar.productions) :
  q ∈ M.F := by
  sorry

/-
  cases h

  case same =>
    match word with
    | .nil => simp at hw

  case step middle l r =>
    have ⟨ step, hstep ⟩ := hw ▸ l
    match hprod:step.prod with
    -- Rules of the form "A -> a" are never used
    | ⟨ .alpha _ _, p ⟩ => simp [toGrammar, transitionToRule] at p

    -- if "q -> ε" is in the grammar, q must be final.
    | ⟨ .eps v , _ ⟩ =>
      -- prove that v = q
      have ⟨ tmp, pre, suf ⟩ := step.lhs_singleton
      simp_rw [hprod] at tmp
      have v_eq_q : [Sum.inl v] = Production.lhs step.prod.val := by
        rw [hprod]; rfl
      rw [hprod, tmp] at v_eq_q
      simp at v_eq_q

      -- prove that word = ε
      have word_eq_eps : (Sum.inr <$> word) = ε := by
        apply Grammar.DerivationRelation.lhs_eps_imp_rhs_eps
        simp [DerivationStep.result, pre, suf, hprod] at hstep
        have hstep := Eq.subst (motive := fun x => x = ε) hstep (by simp; rfl)
        simp at hstep

        rw [<- hstep]
        exact r

      rw [Word.map_eq_eps.mp word_eq_eps]
      exists [q]
      apply NFA.accept_from.final
      . simp
      . simp [toNFA]
        apply eps_production_imp_final
        rw [<- v_eq_q]
        assumption

    -- if "q -> a q'" is in the grammar, then δ(q, a) = q'
    | ⟨ .cons v (a, v'), _ ⟩ =>
      -- prove that v = q
      have ⟨ tmp, pre, suf ⟩ := step.lhs_singleton
      simp_rw [hprod] at tmp
      have v_eq_q : [Sum.inl v] = Production.lhs step.prod.val := by
        rw [hprod]; rfl
      rw [hprod, tmp] at v_eq_q
      simp at v_eq_q

      rw [<- v_eq_q]
      sorry

-/

theorem grammar_lang_subs_lang :
  M.toGrammar.GeneratedLanguage ⊆ M.GeneratedLanguage := by
  intro _ h
  sorry

end DFA
