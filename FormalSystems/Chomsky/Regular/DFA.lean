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

def AcceptedLanguage (M: DFA α qs) : Language M.Z :=
  fun w => ∃run: M.Run M.q₀ w, run.last ∈ M.F

theorem accepted_lang_eq { M: DFA α qs } :
  M.AcceptedLanguage = M.toNFA.AcceptedLanguage := by
  unfold AcceptedLanguage
  unfold toNFA; unfold NFA.AcceptedLanguage
  simp; rfl

theorem last_state_eq_del_star_curried
  {M: DFA α qs} {w: Word M.Z} {q: M.toNFA.Q}
  (r: M.toNFA.Run q w):
  M.del_star_curried w q = .some r.last := by
  cases r
  case final h =>
    simp_rw [h, del_star_curried, NFA.Run.last]
  case step r' incl w_cast =>
    unfold NFA.Run.last
    rw [w_cast]
    unfold del_star_curried
    simp_rw [toNFA, Function.comp_apply] at incl
    rw [Option.mem_toFinset, Option.mem_iff] at incl
    rw [incl, Option.bind_eq_bind, Option.some_bind]
    apply last_state_eq_del_star_curried

theorem last_state_eq_del_star
  {M: DFA α qs} {w: Word M.Z} {q: M.toNFA.Q}
  (r: M.toNFA.Run q w):
  M.del_star (q, w) = .some r.last := by
  simp [del_star]
  apply last_state_eq_del_star_curried

def constrRun
  {M: DFA α qs} (w: Word M.Z) (q: M.Q):
  Option (M.toNFA.Run q w) :=
  match w with
  | ε => some $ .final _ rfl
  | x :: xs =>
      Option.pbind (M.δ (q, x)) $ fun q' hq' => do
        let r' <- constrRun xs q'
        .some $ NFA.Run.step (M := M.toNFA) q
          (by { simp [toNFA]; exact hq'}) r' rfl

theorem del_star_curried_isSome_iff_constrRun_isSome
  {M: DFA α qs} {w: Word M.Z} {q: M.Q}:
  Option.isSome (M.del_star_curried w q) ↔ Option.isSome (constrRun w q) :=
  match w with
  | ε => Iff.of_eq rfl
  | x :: xs => open Option in by
    cases' hq': M.δ ⟨q, x⟩ with q'
    -- both are none
    . simp [del_star_curried, hq', Option.bind_eq_bind]
      unfold constrRun
      rw [pbind_eq_none]
      assumption; intros; assumption
    -- both are some
    . conv =>
        right; rw [isSome_iff_exists]; congr
        intro; unfold constrRun; rw [pbind_eq_some]
      constructor
      -- isSome del_star => isSome constrRun
      . intro h
        rw [del_star_curried, bind_eq_bind, hq', some_bind] at h
        have ⟨r', hr'⟩ := Option.isSome_iff_exists.mp $
          del_star_curried_isSome_iff_constrRun_isSome.mp h
        refine' .intro (.step _ _ r' rfl) ⟨q', hq', _⟩
        simp [toNFA]; assumption
        simp [bind_eq_some]; assumption
      -- isSome del_star <= isSome constrRun
      . intro ⟨r, q', HQ', h⟩
        simp [del_star_curried, bind_eq_bind, hq']
        apply del_star_curried_isSome_iff_constrRun_isSome.mpr
        rw [isSome_iff_exists]; simp [hq'] at HQ'; rw [HQ']
        simp [bind_eq_some] at h; have ⟨r', _, _⟩ := h
        exists r'

theorem del_star_isSome_iff_constrRun_isSome
  {M: DFA α qs} {w: Word M.Z} {q: M.Q}:
  Option.isSome (M.del_star (q, w)) ↔ Option.isSome (constrRun w q) := by
  unfold del_star
  rw [del_star_curried_isSome_iff_constrRun_isSome]

theorem in_language_iff_del_star_final
  {M: DFA α qs} {w: Word M.Z}:
  w ∈ M.AcceptedLanguage ↔ ∃qf ∈ M.del_star (M.q₀, w), qf ∈ M.F := by
  constructor
  . intro ⟨r, hr⟩
    refine' .intro r.last ⟨_, hr⟩
    exact last_state_eq_del_star _
  . intro ⟨qf, hdel, hf⟩
    let r := constrRun w M.q₀
    have : r.isSome :=
      del_star_isSome_iff_constrRun_isSome.mp
        (Option.isSome_iff_exists.mpr ⟨qf, hdel⟩)
    exists r.get this
    simp [last_state_eq_del_star (r.get this)] at hdel
    rw [hdel]; assumption


def transitionToRule (M: DFA α qs) : (M.Q × M.Z) → Option (RegularProduction M.Z M.Q)
  | (q, a) => (.cons q ∘ (a,·)) <$> M.δ (q, a)

variable [DecidableEq α] [DecidableEq qs] (M: DFA α qs)

def toGrammar (M: DFA α qs) : RegularGrammar α qs where
  Z := M.Z
  V := M.Q
  start := M.q₀
  productions := (Finset.eraseNone $ Fintype.elems.image M.transitionToRule) ∪
    M.F.map ⟨ .eps, by intro _ _; simp ⟩

def final_state_to_derivation_step (state: M.Q) (_: state ∈ M.F): M.toGrammar.DerivationStep [.inl state] where
  pre := ε
  suf := ε
  prod := {
    val := RegularProduction.eps state
    property := by
      unfold toGrammar
      simp
      apply Or.inr
      assumption
  }
  sound := by rfl

def state_transition_to_derivation_step (a: M.Z) (q₁ q₂: M.Q) (h: q₂ ∈ M.δ (q₁, a)) :
  M.toGrammar.DerivationStep [.inl q₁] where
  pre := ε
  suf := ε
  prod := {
    val := RegularProduction.cons q₁ (a, q₂)
    property := by
      unfold toGrammar
      simp
      exists q₁, q₁.2, a, a.2
      simp
      constructor
      . apply Fintype.complete
      . simp [transitionToRule]
        simp at h
        exact h
  }
  sound := by rfl

def Run.toDerivation (run: M.Run start word) (hlast: run.last ∈ M.F):
  M.toGrammar.Derivation [.inl start] (.inr <$> word) :=
  match run with
  | NFA.Run.final q hend =>
    Grammar.Derivation.step
      (M.final_state_to_derivation_step q hlast)
      (Grammar.Derivation.same rfl)
      (by simp [Grammar.DerivationStep.result, hend, final_state_to_derivation_step]; rfl)
  | @NFA.Run.step _ _ _ q₂ a _ _ q qn run' h_w =>
    let step := M.state_transition_to_derivation_step a q q₂ (by unfold toNFA at qn; simp at qn; rw [qn]; simp)
    let d' := DFA.Run.toDerivation run' hlast
    let augmented := @Grammar.Derivation.augment_left_cons _ _ _ _ M.toGrammar (Sum.inr { val := a.val, property := by unfold toGrammar; unfold toNFA at a; simp }) _ _ d'

    @Grammar.Derivation.step _ _ _ _ M.toGrammar _ [(Sum.inr { val := a.val, property := by unfold toGrammar; unfold toNFA at a; simp }), Sum.inl q₂] _
      (step)
      (cast (by simp [h_w]) augmented)
      (by rfl)

theorem lang_subs_toGrammar_lang :
  M.AcceptedLanguage ⊆ M.toGrammar.GeneratedLanguage := by
  intro _ ⟨ run, h ⟩
  constructor
  exact run.toDerivation _ h

theorem toGrammar_prod_imp_transition
  (h: RegularProduction.cons v (a, v') ∈ M.toGrammar.productions):
  M.δ (v, a) = some v' := by
  simp [toGrammar, transitionToRule] at h
  have ⟨_, _, _, _, _, _, _, _, c1, c2, c3⟩ := h
  rw [<- c1, <- c2, <- c3]
  assumption

def Run.fromDerivation: (d: M.toGrammar.RegularDerivation start word) →
  M.Run start word
  | .eps _ _ h_w => NFA.Run.final _ h_w
  | .alpha _ h _ => by simp [toGrammar, transitionToRule] at h -- contradiction
  | .step v v' h_v h_w d' =>
    NFA.Run.step
      ({ val := v.val, property := by unfold toNFA; unfold toGrammar at v; simp })
      (by apply toGrammar_prod_imp_transition at h_v; simp [toNFA]; exact h_v)
      (fromDerivation d')
      (h_w)

theorem Run.fromDerivation_result {d: M.toGrammar.RegularDerivation s w}:
  (Run.fromDerivation M d).last ∈ M.F := by
  cases d
  case eps h_v h_w =>
    simp [toGrammar, transitionToRule] at h_v
    simp [fromDerivation, NFA.Run.last]
    assumption

  case alpha h_v _ =>
    simp [toGrammar, transitionToRule] at h_v

  case step h_w =>
    simp [fromDerivation, NFA.Run.last]
    apply fromDerivation_result

theorem toGrammar_lang_subs_lang :
  M.toGrammar.GeneratedLanguage ⊆ M.AcceptedLanguage := by
  intro _ h
  apply Nonempty.elim h
  intro d
  constructor
  apply Run.fromDerivation_result
  apply RegularGrammar.RegularDerivation.fromDerivation
  assumption
  rfl

theorem toGrammar_lang_eq_lang :
  M.toGrammar.GeneratedLanguage = M.AcceptedLanguage := by
  apply Set.ext
  intros; constructor
  apply toGrammar_lang_subs_lang
  apply lang_subs_toGrammar_lang

end DFA
