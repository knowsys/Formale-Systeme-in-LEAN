/-!
Fintype related definitions and results.
-/


/--
Fintype is used to express that a type is finite by requiring a list that contains all elements of this type. (inspired by mathlib)
-/
class Fintype (α : Type u) where
  elems : List α
  complete : ∀ a : α, a ∈ elems

/--
Subtype of α containing elements of l
-/
def subtype_of_list (l : List α) := { x : α // x ∈ l }

/-- A subtype of α created from the list l is finite. -/
instance {l : List α} : Fintype (subtype_of_list l) where
  elems := l.attach
  complete := by
    intro a
    rcases a with ⟨p, v⟩
    simp only [List.attach, subtype_of_list, List.attachWith]
    grind

/-- If α is finite then Option α is finite as well. -/
instance [T : Fintype α] : Fintype (Option α) where
  elems := T.elems.map (some · ) ++ [.none]
  complete := by
    intro a
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    have some_mem (b : α) : some b ∈ T.elems.map (some · ) ++ [.none] := by
      simp only [List.mem_append, List.mem_map, Option.some.injEq, exists_eq_right, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false]
      exact T.complete b
    by_cases hq : a = none
    . apply Or.inr; exact hq
    . rw [← Ne.eq_1, Option.ne_none_iff_exists] at hq
      rcases hq with ⟨r, r_eq⟩
      apply Or.inl
      exists r
      constructor
      . exact T.complete r
      . exact r_eq
