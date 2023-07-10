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

theorem state_transition_imp_derivation (h : q₂ ∈ M.δ (q₁, a)) :
  (M.state_transition_to_derivation_step _ _ _ h).result = [.inr a, .inl q₂] := by
  rfl

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
    simp [toNFA] at a
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

def derivation_to_run
  (d: M.toGrammar.Derivation w)
  (hl: d.lhs = [.inl M.q₀])
  (hr: w = (.inr <$> w') * Word.mk [.inl q]):
  { r: M.Run M.q₀ w' // r.last = q } := by
  cases d
  case same =>
    unfold Grammar.Derivation.lhs at hl
    rw [hr, Word.mul_eq_cons, Word.eps_eq_nil] at hl
    simp [Word.mk, HMul.hMul, Mul.mul, List.nil_eq_append] at hl
    rw [List.map_eq_nil, <- Word.eps_eq_nil] at hl
    rw [List.cons_eq_cons] at hl; simp at hl
    have ⟨_, _⟩ := hl
    constructor; swap
    apply NFA.Run.final
    assumption
    unfold NFA.Run.last
    apply Eq.symm
    assumption
  
  case step xs x res =>
    unfold Grammar.Derivation.lhs at hl
    rw [hr] at res
    unfold Grammar.DerivationStep.result at res
    --have rt := RegularGrammar.regularity_theorem xs hl
    constructor; swap
    cases w'
    case val.nil => sorry --contradiction
    case val.cons a as =>
      apply NFA.Run.step
      induction as with
      | nil => apply NFA.Run.final; rfl
      | cons _ _ ih =>
        apply NFA.Run.step
        apply ih

    sorry

structure SplitDerivation (w: Word _) (lhs: Word _) where
  qf: M.F
  d: M.toGrammar.Derivation (.inr <$> w * Word.mk [.inl qf.val])
  lh_prop: d.lhs = lhs

def decompose_final_derivation_step
  (d: M.toGrammar.Derivation (Sum.inr <$> w)) (hd: d.lhs = [.inl start]):
  M.SplitDerivation w d.lhs := by
  cases d

  case same =>
    apply False.elim
    simp [Grammar.Derivation.lhs] at hd
    have : .inl start ∈ List.map Sum.inr w
    rw [hd]
    apply List.mem_cons.mpr
    apply Or.inl; rfl
    apply Exists.elim $ List.mem_map.mp this
    intro _ ⟨_, _⟩
    contradiction
  
  case step _ step sound =>
    unfold Grammar.DerivationStep.result at sound
    match hprod:step.prod.val with
    | .alpha _ _ =>
      have c := step.prod.prop
      simp [toGrammar, hprod, transitionToRule] at c

    | .cons _ (a, v) =>
      rw [hprod, RegularProduction.rhs_eq_rhs] at sound
      simp [RegularProduction.rhs] at sound
      sorry

    | .eps qf =>
      have s1 : Production.rhs step.prod.val = ε := by rw [hprod]; rfl
      simp [s1] at sound
      simp [toGrammar] at qf
      have prod_incl := step.prod.prop
      simp [toGrammar, hprod, transitionToRule] at prod_incl
      constructor; swap
      . exists qf
      swap
      . have step_lhs := step.sound
        simp at step_lhs
        sorry
      . sorry

theorem grammar_lang_subs_lang :
  M.toGrammar.GeneratedLanguage ⊆ M.GeneratedLanguage := by
  intro _ ⟨ derivation , derivation_prop ⟩
  have ⟨q, d, p⟩ := decompose_final_derivation_step _ derivation derivation_prop
  have ⟨run, rp⟩ := M.derivation_to_run d (by rw [p, derivation_prop]; simp [toGrammar]) rfl
  apply Exists.intro; swap
  . exact run
  . rw [rp]; exact q.prop

end DFA
