import FormalSystems.Chomsky.Regular.DFA
import FormalSystems.Preliminaries.Fold

def DFA.fromNFA [DecidableEq qs] (M: NFA α qs): DFA α (Finset M.Q) where
  Z := M.Z
  Q := Finset.univ
  q₀ := ⟨ M.Q₀, Fintype.complete _ ⟩
  F := Finset.univ.filter (λs => ∃q ∈ s.val, q ∈ M.F)

  δ := fun (q, a) => .some $
    ⟨ Finset.fold (β:=Finset M.Q) (· ∪ ·) ∅ (λq => M.δ (q, a)) q, by simp ⟩

variable [DecidableEq qs] { M: NFA α qs }

def DFA.fromNFA.RunFromRestricted { qs: _ }
  (r: (DFA.fromNFA M).Run q w)
  (h: q.val ⊆ qs.val):
  (DFA.fromNFA M).Run qs w :=
  match r with
  | .final _ h => .final qs h
  | .step _ hq' r hw =>
    .step
      qs
      (by unfold toNFA; unfold fromNFA; simp; rfl)
      (RunFromRestricted r (by unfold toNFA at hq'; unfold fromNFA at hq'; simp at hq'; simp [hq']; apply Finset.fold_union_subs; exact h))
      hw

theorem DFA.fromNFA.RunFromRestricted_final
  (h: r.last ∈ (DFA.fromNFA M).F):
  (DFA.fromNFA.RunFromRestricted r h').last ∈ (DFA.fromNFA M).F := by
  cases r
  . dsimp [NFA.Run.last, fromNFA] at h
    rw [Finset.mem_filter] at h
    dsimp [RunFromRestricted, NFA.Run.last, fromNFA]
    apply Eq.subst (propext $ Finset.mem_filter.symm) (motive := id); simp
    constructor
    rw [Finset.attach_eq_univ]; dsimp [Finset.univ]
    apply Fintype.complete
    have ⟨_, q, _, _⟩ := h
    exists q; constructor; constructor
    apply Finset.mem_of_subset
    repeat { assumption }
  . dsimp [RunFromRestricted, NFA.Run.last]
    apply RunFromRestricted_final
    dsimp [NFA.Run.last] at h
    assumption

def DFA.fromNFA.NFARunToRun (r: M.Run q w):
  (DFA.fromNFA M).Run ⟨{q}, Fintype.complete _⟩ w :=
  match r with
  | .final _ h => .final _ h
  | .step _ hq' r hw =>
    .step
      _
      (by unfold toNFA; unfold fromNFA; simp; rfl)
      (RunFromRestricted (NFARunToRun r) (by simp; exact hq'))
      hw

theorem DFA.fromNFA.NFARunToRun_final_imp_final { r: M.Run q w} (h: r.last ∈ M.F):
  (NFARunToRun r).last ∈ (DFA.fromNFA M).F := by
  cases r
  . dsimp [fromNFA]
    apply Eq.subst (propext $ Finset.mem_filter.symm) (motive := id); simp
    constructor
    dsimp [Finset.univ]
    apply Fintype.complete
    exists q; simp
    dsimp [NFA.Run.last] at h
    simp [NFARunToRun, NFA.Run.last]
    assumption

  . dsimp [NFARunToRun, NFA.Run.last]
    apply RunFromRestricted_final
    apply NFARunToRun_final_imp_final
    dsimp [NFA.Run.last] at h
    assumption

theorem NFA.lang_subs_DFA_fromNFA_lang:
  M.AcceptedLanguage ⊆ (DFA.fromNFA M).AcceptedLanguage := by
  intro w ⟨_, h_start, run, h_run⟩
  constructor; swap
  apply DFA.fromNFA.RunFromRestricted
  apply DFA.fromNFA.NFARunToRun
  assumption
  simp [DFA.fromNFA]; assumption
  apply DFA.fromNFA.RunFromRestricted_final
  apply DFA.fromNFA.NFARunToRun_final_imp_final
  assumption

theorem DFA.fromNFA_run_imp_run
  { q₀: (DFA.fromNFA M).Q }
  (r: (DFA.fromNFA M).Run q₀ w) (h: r.last ∈ (DFA.fromNFA M).F):
  ∃q ∈ q₀.val, ∃r': M.Run q w, r'.last ∈ M.F := by
  match r with
  | .final _ _ =>
    dsimp [NFA.Run.last, fromNFA] at h
    have ⟨_, qf, _, _⟩ := Finset.mem_filter.mp h
    exists qf; constructor; assumption
    apply Exists.intro; swap
    apply NFA.Run.final _
    assumption
    dsimp [NFA.Run.last]
    assumption
  | .step _ h_step r h_w =>
    have _termination : r.len < (NFA.Run.step q₀ h_step r h_w).len := by
      conv => right; unfold NFA.Run.len
      simp

    dsimp [NFA.Run.last] at h
    dsimp [fromNFA, toNFA] at h_step; simp at h_step
    have ⟨_, h_q₂, r', hr'⟩ := fromNFA_run_imp_run r h
    rw [h_step, Finset.mem_fold_union_iff] at h_q₂
    have ⟨x, _, _⟩ := h_q₂
    exists x; constructor; assumption
    apply Exists.intro; swap
    apply NFA.Run.step
    repeat { assumption }
termination_by r.len

theorem NFA.DFA_fromNFA_lang_subs_lang:
  (DFA.fromNFA M).AcceptedLanguage ⊆ M.AcceptedLanguage := by
  intro w ⟨r, hr⟩
  have ⟨q, hq, r, _⟩ := DFA.fromNFA_run_imp_run r hr
  exists q
  dsimp [DFA.fromNFA] at hq
  constructor; assumption
  exists r

theorem NFA.fromNFA_lang_eq_lang:
  (DFA.fromNFA M).AcceptedLanguage = M.AcceptedLanguage := by
  apply Set.ext; intros; constructor
  apply DFA_fromNFA_lang_subs_lang
  apply lang_subs_DFA_fromNFA_lang

