import FormalSystems.Chomsky.Regular.DFA
import FormalSystems.Preliminaries.Fold

variable [DecidableEq α] [DecidableEq qs] 

def DFA.fromNFA (M: NFA α qs): DFA α (Finset M.Q) where
  Z := M.Z
  Q := Finset.univ
  q₀ := ⟨ M.Q₀, Fintype.complete _ ⟩
  F := Finset.univ.filter (λs => ∃q ∈ s.val, q ∈ M.F)

  δ := fun (q, a) => .some $
    ⟨ Finset.fold (β:=Finset M.Q) (· ∪ ·) ∅ (λq => M.δ (q, a)) q, by simp ⟩

variable [DecidableEq α] [DecidableEq qs] { M: NFA α qs }

def DFA.fromNFA.RunFromRestricted { qs: _ }
  (r: (DFA.fromNFA M).Run q w)
  (h: q.val ⊆ qs.val):
  (DFA.fromNFA M).Run qs w := by
  cases r
  apply NFA.Run.final
  assumption
  case step x _ =>
    apply NFA.Run.step
    dsimp [toNFA, fromNFA]; simp
    rfl
    apply RunFromRestricted
    assumption
    dsimp [toNFA, fromNFA] at x; simp at x
    simp_rw [x]
    apply Finset.fold_union_subs
    repeat { assumption }

theorem DFA.fromNFA.RunFromRestricted_final
  (h: r.last ∈ (DFA.fromNFA M).F):
  (DFA.fromNFA.RunFromRestricted r h').last ∈ (DFA.fromNFA M).F := by
  cases r
  . dsimp [NFA.Run.last, fromNFA] at h
    rw [Finset.mem_filter] at h
    dsimp [RunFromRestricted, NFA.Run.last, fromNFA]
    rw [Finset.mem_filter]
    constructor
    rw [Finset.attach_eq_univ]; dsimp [Finset.univ]
    apply Fintype.complete
    have ⟨_, q, _, _⟩ := h
    exists q; constructor
    apply Finset.mem_of_subset
    repeat { assumption }
  . dsimp [RunFromRestricted, NFA.Run.last]
    apply RunFromRestricted_final
    dsimp [NFA.Run.last] at h
    assumption

def DFA.fromNFA.NFARunToRun (r: M.Run q w):
  (DFA.fromNFA M).Run ⟨{q}, Fintype.complete _⟩ w := by
  cases r
  apply NFA.Run.final
  assumption
  apply NFA.Run.step
  dsimp [fromNFA, toNFA]; simp
  rfl
  apply RunFromRestricted
  apply NFARunToRun
  repeat { simp; assumption }

theorem DFA.fromNFA.NFARunToRun_final_imp_final { r: M.Run q w} (h: r.last ∈ M.F):
  (NFARunToRun r).last ∈ (DFA.fromNFA M).F := by
  cases r
  . dsimp [NFA.Run.last, fromNFA]
    rw [Finset.mem_filter]; constructor
    rw [Finset.attach_eq_univ]; dsimp [Finset.univ]
    apply Fintype.complete
    exists q; simp
    dsimp [NFA.Run.last] at h
    assumption
  
  . dsimp [NFARunToRun, NFA.Run.last]
    apply RunFromRestricted_final
    apply NFARunToRun_final_imp_final
    dsimp [NFA.Run.last] at h
    assumption

theorem NFA.lang_subs_DFA_fromNFA_lang:
  M.GeneratedLanguage ⊆ (DFA.fromNFA M).GeneratedLanguage := by
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
  { r: (DFA.fromNFA M).Run q₀ w } (h: r.last ∈ (DFA.fromNFA M).F):
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
  | .step _ h_step _ _ =>
    dsimp [NFA.Run.last] at h
    dsimp [fromNFA, toNFA] at h_step; simp at h_step
    have ⟨_, h_q₂, r', hr'⟩ := fromNFA_run_imp_run h
    rw [h_step, Finset.mem_fold_union_iff] at h_q₂
    have ⟨x, _, _⟩ := h_q₂
    exists x; constructor; assumption
    apply Exists.intro; swap
    apply NFA.Run.step
    repeat { assumption }

theorem NFA.DFA_fromNFA_lang_subs_lang:
  (DFA.fromNFA M).GeneratedLanguage ⊆ M.GeneratedLanguage := by
  intro w ⟨_, hr⟩
  have ⟨q, hq, r, _⟩ := DFA.fromNFA_run_imp_run hr
  exists q
  dsimp [DFA.fromNFA] at hq
  constructor; assumption
  exists r

theorem NFA.fromNFA_lang_eq_lang:
  (DFA.fromNFA M).GeneratedLanguage = M.GeneratedLanguage := by
  apply Set.ext; intros; constructor
  apply DFA_fromNFA_lang_subs_lang
  apply lang_subs_DFA_fromNFA_lang
