import FormalSystems.Chomsky.Regular.DFA

structure TotalDFA (α: Type) (qs: Type) extends DFA α qs where
  totality: ∀q, ∀a, Option.isSome $ δ (q, a)

namespace TotalDFA

def δ' (M: TotalDFA α qs): M.Q × M.Z → M.Q := fun ⟨q, a⟩ =>
  Option.get (M.δ (q, a)) (M.totality q a)

theorem total_del_eq (M: TotalDFA α qs):
  ∀q, ∀a, M.δ (q, a) = some (M.δ' (q, a)) := fun _ _ =>
    Option.eq_some_iff_get_eq.mpr ⟨_, rfl⟩

def del_star_curried' (M: TotalDFA α qs): Word (M.Z) → M.Q → M.Q
  | ε => id
  | x :: xs => M.del_star_curried' xs ∘ M.δ' ∘ (·,x)

theorem total_del_star_eq (M: TotalDFA α qs):
  ∀q, ∀w, M.del_star_curried w q = some (M.del_star_curried' w q) := by
  intro q w; cases w; rfl
  unfold DFA.del_star_curried del_star_curried'
  rw [total_del_eq, Option.bind_eq_bind, Option.some_bind]
  apply total_del_star_eq
