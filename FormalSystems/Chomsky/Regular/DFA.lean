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

def del_star_curried (M: DFA α qs) : Word M.Z → M.Q → Option M.Q
  | ε, q => q
  | a :: xs, q => M.δ (q, a) >>= M.del_star_curried xs

def del_star (M: DFA α qs) : (M.Q × Word M.Z) → Option M.Q
  | (q, w) => M.del_star_curried w q

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

def Run.toDerivation (run: M.Run start word) (hlast: run.last ∈ M.F):
  M.toGrammar.Derivation [.inl start] (.inr <$> word) := by
  cases run
  case final hend =>
    rw [hend]
    unfold NFA.Run.last at hlast
    simp; rw [<- Word.eps_eq_nil]
    rw [<- M.final_state_to_derivation_step_rhs]; swap
    exact ⟨ start, hlast ⟩
    apply Grammar.Derivation.step
    apply Grammar.Derivation.same
    rfl

  case step a _ qn run' =>
    unfold NFA.Run.last at hlast
    have d' := DFA.Run.toDerivation run' hlast
    apply Grammar.Derivation.step
    apply (d'.augment_left_cons); swap
    apply state_transition_to_derivation_step
    have p := qn.prop
    simp [toNFA] at p
    rw [Option.mem_iff]
    exact p
    rfl

theorem lang_subs_grammar_lang :
  M.GeneratedLanguage ⊆ M.toGrammar.GeneratedLanguage := by
  intro _ ⟨ run, h ⟩
  constructor
  exact run.toDerivation _ h

end DFA
