import FormalSystems.Chomsky.Regular.DFA

structure TotalDFA (α: Type) (qs: Type) extends DFA α qs where
  totality: ∀q, ∀a, Option.isSome $ δ (q, a)

namespace TotalDFA

def δ' (M: TotalDFA α qs): M.Q × M.Z → M.Q := fun ⟨q, a⟩ =>
  Option.get (M.δ (q, a)) (M.totality q a)

theorem total_del_eq (M: TotalDFA α qs):
  ∀q, ∀a, M.δ (q, a) = some (M.δ' (q, a)) := fun _ _ =>
    Option.eq_some_iff_get_eq.mpr ⟨_, rfl⟩

def del_star' (M: TotalDFA α qs): M.Q × Word (M.Z) → M.Q
  | (q, ε) => q
  | (q, x :: xs) => M.del_star' (M.δ' (q, x), xs)
termination_by _ p => p.2.length

theorem total_del_star_eq {M: TotalDFA α qs} {q: _} {w: _}:
  M.del_star (q, w) = some (M.del_star' (q, w)) := by
  simp [DFA.del_star]
  induction w generalizing q
  case nil => rfl
  case cons _ _ ih =>
    simp [del_star', DFA.del_star_curried]
    rw [total_del_eq, Option.bind_eq_bind, Option.some_bind]
    apply ih

theorem in_language_iff_del_star_final
  {M: TotalDFA α qs} {w: Word M.Z}:
  w ∈ M.GeneratedLanguage ↔ M.del_star' (M.q₀, w) ∈ M.F := by
  rw [DFA.in_language_iff_del_star_final, total_del_star_eq]
  simp
