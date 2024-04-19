import FormalSystems.Chomsky.Regular.DFA
import Mathlib.Data.Fintype.Option

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
termination_by p => p.2.length

theorem total_del_star_eq {M: TotalDFA α qs} {q: _} {w: _}:
  M.del_star (q, w) = some (M.del_star' (q, w)) := by
  simp [DFA.del_star]
  induction w generalizing q
  case nil => rfl
  case cons _ _ ih =>
    unfold DFA.del_star_curried
    rw [total_del_eq] 
    apply ih

theorem in_language_iff_del_star_final
  {M: TotalDFA α qs} {w: Word M.Z}:
  w ∈ M.AcceptedLanguage ↔ M.del_star' (M.q₀, w) ∈ M.F := by
  rw [DFA.in_language_iff_del_star_final, total_del_star_eq]
  simp

end TotalDFA

def DFA.toTotalDFA (M: DFA α qs): TotalDFA α (Option M.Q) where
  Z := M.Z
  Q := Finset.univ
  q₀ := ⟨.some M.q₀, by simp⟩
  F := M.F.map ⟨ fun q => ⟨.some q, by simp⟩, fun _ _ => by simp⟩

  δ | (⟨.none, _⟩, _) => some ⟨.none, by simp⟩
    | (⟨.some q, _⟩, a) =>
      match M.δ (q, a) with
      | none => some ⟨.none, by simp⟩
      | some q' => some ⟨.some q', by simp⟩

  totality := fun ⟨q, _⟩ a => by
    cases q; rfl
    simp
    cases M.δ _
    repeat { trivial }

variable { M: DFA α qs }

theorem totalDFA_del_eq_del {q: _} {a: _}:
  M.δ (q, a) = M.toTotalDFA.δ' (⟨some q, Fintype.complete _⟩, a) := by
  simp [TotalDFA.δ']
  cases hd: M.δ _ <;> simp [DFA.toTotalDFA, hd]

theorem totalDFA_del_star_none:
  (M.toTotalDFA.del_star' (⟨none, Fintype.complete _⟩, w)).val = none := by
  induction' w with x xs ih
  rfl
  simp [TotalDFA.del_star']
  have : M.toTotalDFA.δ' (⟨none, Fintype.complete _⟩, x) = ⟨none, Fintype.complete _⟩ := rfl
  rw [this]
  apply ih

theorem totalDFA_del_star_eq {q: _} {w: _}:
  M.del_star (q, w) = M.toTotalDFA.del_star' (⟨some q, Fintype.complete _⟩, w) := by
  simp [DFA.del_star]
  induction w generalizing q
  case nil => rfl
  case cons _ xs ih =>
    simp [DFA.del_star_curried, Option.bind_eq_bind, TotalDFA.del_star']
    cases' hd: M.δ _ with q'
    . rw [totalDFA_del_eq_del] at hd
      let q' : M.toTotalDFA.Q := ⟨ none, Fintype.complete _ ⟩
      have : q'.val = none := rfl
      rw [<-this] at hd
      simp [Subtype.eq hd]
      rw [totalDFA_del_star_none]
    . rw [Option.some_bind]
      rw [totalDFA_del_eq_del] at hd
      let q' : M.toTotalDFA.Q := ⟨ some q', Fintype.complete _ ⟩
      have : q'.val = some _ := rfl
      rw [<-this] at hd
      rw [Subtype.eq hd]
      apply ih

theorem Subtype.eq_iff {p: α -> Prop} { x y: Subtype p }:
  x = y ↔ x.val = y.val := ⟨fun h => by rw [h], Subtype.eq⟩

theorem totalDFA_lang_eq:
  M.AcceptedLanguage = M.toTotalDFA.AcceptedLanguage := by
  apply Set.ext; intro w
  rw [DFA.in_language_iff_del_star_final]
  -- w is of type Word M.Z, but the theorem expects Word M.toTotalDFA.Z
  let w': Word M.toTotalDFA.Z := w
  have w_cast : w = w' := rfl
  rw [w_cast, TotalDFA.in_language_iff_del_star_final]
  conv =>
    right; congr;
    -- expand definition of toTotalDFA.q₀
    right; simp [DFA.toTotalDFA]; rfl
    -- expand definition of toTotalDFA.F
    simp [DFA.toTotalDFA]

  rw [Finset.mem_map]
  conv =>
    right; congr; intro;
    simp [Subtype.eq_iff, <-totalDFA_del_star_eq];
    rw [And.comm];

  constructor <;> intro ⟨x, l, r⟩ <;> exists x
  . simp [r, Option.mem_iff.mp l]; rfl
  . simp [l, r]; exact l.symm
