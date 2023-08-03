import FormalSystems.Chomsky.Regular.DFA

variable [DecidableEq α] [DecidableEq qs] 

def DFA.fromNFA (M: NFA α qs): DFA α (Finset M.Q) where
  Z := M.Z
  Q := Finset.univ
  q₀ := ⟨ M.Q₀, Fintype.complete _ ⟩
  F := Finset.univ.filter (λs => ∃q ∈ s.val, q ∈ M.F)

  δ := fun (q, a) => .some $
    ⟨ Finset.fold (β:=Finset M.Q) (· ∪ ·) ∅ (λq => M.δ (q, a)) q, by simp ⟩

variable [DecidableEq α] [DecidableEq qs] { M: NFA α qs }

theorem mem_fold_union_iff [DecidableEq β] { f: α → Finset β }:
  (∃ x ∈ s, e ∈ f x) ↔ e ∈ Finset.fold Union.union ∅ f s := by
  constructor
  . intro ⟨x, h₁, h₂⟩
    have ⟨s, _⟩ := s
    revert s
    apply Quot.ind
    intro l _ h
    simp [Finset.fold, Multiset.fold]
    induction l with
    | nil => contradiction
    | cons _ _ ih =>
      cases h
      . simp; apply Or.inl
        assumption
      . simp; apply Or.inr
        apply ih
        assumption
        apply And.right ∘ Multiset.nodup_cons.mp
        assumption
  
  . cases s
    case mk s' _ =>
      revert s'
      apply Quot.ind
      intro l _ h
      simp [Finset.fold] at h
      induction l with
      | nil => contradiction
      | cons x _ ih => 
        simp at h
        cases h
        exists x; simp; assumption
        have := ih (by apply And.right ∘ Multiset.nodup_cons.mp; assumption)
        have ⟨x, _, _⟩ := this (by assumption)
        exists x
        constructor
        simp; apply Or.inr; assumption
        assumption

theorem fold_union_subs [DecidableEq β] { f: α → Finset β } { qa qb: Finset α } (h: qa ⊆ qb):
  Finset.fold (β:=Finset β) (· ∪ ·) ∅ f qa ⊆ Finset.fold (· ∪ ·) ∅ f qb := by
  apply Finset.subset_iff.mpr
  intro _ h
  apply mem_fold_union_iff.mp
  have ⟨x, _, _⟩ := mem_fold_union_iff.mpr h
  exists x; constructor
  apply Finset.mem_of_subset
  repeat { assumption }

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
    apply fold_union_subs
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
