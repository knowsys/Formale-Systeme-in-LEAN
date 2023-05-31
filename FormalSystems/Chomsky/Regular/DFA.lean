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

def toGrammar [DecidableEq α] [DecidableEq qs] (M: DFA α qs) : RegularGrammar α qs where
  Z := M.Z
  V := M.Q
  start := M.q₀
  productions := (Finset.eraseNone $ Fintype.elems.image M.transitionToRule) ∪
    M.F.map ⟨ .eps, by intro _ _; simp ⟩

end DFA
