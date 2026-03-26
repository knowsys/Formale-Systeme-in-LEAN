import FormaleSystemeInLean.Fintype

def Set (α : Type u) := α -> Prop

-- The following type class instances are just allowing us to use some basic notation like ∅, ∈ or ∪ with the right definitions..
instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False

instance : Membership α (Set α) where
  mem S a := S a

instance : Union (Set α) where
  union A B := fun e => e ∈ A ∨ e ∈ B

instance : Inter (Set α) where
  inter A B := fun e => e ∈ A ∧ e ∈ B

instance : HasSubset (Set α) where
  Subset A B := ∀ e, e ∈ A -> e ∈ B

instance : HasSSubset (Set α) where
  SSubset A B := A ⊆ B ∧ ¬ B ⊆ A

instance : SDiff (Set α) where
  sdiff A B := fun e => e ∈ A ∧ ¬(e ∈ B)

def List.toSet (l : List α) : Set α := fun e => e ∈ l

namespace Set

def powerset (α : Type u) (S : Set α) := fun x => x ⊆ S

def map (f : α → β) (S : Set α) [Fintype α] : Set β :=
  fun b => ∃ (a : α), a ∈ S ∧ f a = b

-- Set extensionality: Two sets are equal if they contain the same elements. This is not something we define but we can prove it!
theorem ext (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) -> X = Y := by
  intro h; apply funext; intro e; apply propext; specialize h e; exact h


theorem inter_commutative (X Y : Set α) : X ∩ Y = Y ∩ X := by
  apply Set.ext
  intro e
  constructor
  . intro e_mem
    constructor
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_y
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_x
  . intro e_mem
    constructor
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_y
    . rcases e_mem with ⟨e_x, e_y⟩
      exact e_x

theorem union_commutative (X Y : Set α) : X ∪ Y = Y ∪ X := by
  apply Set.ext
  intro e
  constructor
  . intro e_mem
    apply Or.elim e_mem
    . intro e_mem_x
      apply Or.inr
      exact e_mem_x
    . intro e_mem_y
      apply Or.inl
      exact e_mem_y
  . intro e_mem
    apply Or.elim e_mem
    . intro e_mem_x
      apply Or.inr
      exact e_mem_x
    . intro e_mem_y
      apply Or.inl
      exact e_mem_y

theorem distr_inter_union (X Y Z : Set α) : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  apply Set.ext
  intro x
  constructor
  . intro x_mem
    rcases x_mem with ⟨l, r⟩
    by_cases h : x ∈ Y
    . apply Or.inl
      constructor
      . exact l
      . exact h
    . have x_mem_Z : x ∈ Z := by
        rcases r with inl | inr
        . contradiction
        . exact inr
      apply Or.inr
      constructor
      . exact l
      . exact x_mem_Z
  . intro x_mem
    rcases x_mem with inl | inr
    rcases inl with ⟨x_mem_X, x_mem_Y⟩
    . constructor
      . exact x_mem_X
      . apply Or.inl
        exact x_mem_Y
    . rcases inr with ⟨x_mem_X, x_mem_Z⟩
      constructor
      . exact x_mem_X
      . apply Or.inr
        exact x_mem_Z

theorem distr_union_inter (X Y Z : Set α) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  apply Set.ext
  intro x
  constructor
  . intro x_mem
    by_cases hx : x ∈ X
    . constructor
      . apply Or.inl; exact hx
      . apply Or.inl; exact hx
    . have x_mem_yz : x ∈ Y ∩ Z := by
        rcases x_mem with inl | inr
        . contradiction
        . exact inr
      rcases x_mem_yz with ⟨mem_y, mem_z⟩
      constructor
      . apply Or.inr; exact mem_y
      . apply Or.inr; exact mem_z
  . intro x_mem
    rcases x_mem with ⟨mem_xy, mem_xz⟩
    by_cases hx : x ∈ X
    . apply Or.inl
      exact hx
    . apply Or.inr
      constructor
      . rcases mem_xy with inl | inr
        . contradiction
        . exact inr
      . rcases mem_xz with inl | inr
        . contradiction
        . exact inr

theorem not_empty_contains_element (X : Set α) : X ≠ ∅ -> ∃ e, e ∈ X := by
  intro neq
  apply Classical.byContradiction
  intro contra
  apply neq
  apply Set.ext
  intro e
  simp only [not_exists] at contra
  specialize contra e
  simp only [contra, false_iff]
  simp [Membership.mem, EmptyCollection.emptyCollection]

theorem empty_eq (A : Set α) : (∀ (x : α), ¬x ∈ A) -> A = ∅ := by
  intro h
  apply Set.ext
  intro a
  simp only [EmptyCollection.emptyCollection]
  constructor
  . intro e_mem
    simp only [Membership.mem]
    apply h a
    exact e_mem
  . intro e_mem
    simp only [Membership.mem] at e_mem

theorem empty_iff (A : Set α) : A = ∅ ↔ ∀ a, a ∉ A := by
  constructor
  . intro A_eq
    simp only [EmptyCollection.emptyCollection] at *
    intro a
    intro contra
    simp only [A_eq, Membership.mem] at contra
  . intro h
    apply Set.ext
    intro e
    simp only [EmptyCollection.emptyCollection]
    constructor
    . intro e_mem
      simp only [Membership.mem]
      apply h e
      exact e_mem
    . intro e_mem
      simp only [Membership.mem] at e_mem

-- "not_empty_contains_element" but for boolean inequality
theorem ne_empty_contains_element (B : Set α) [DecidableEq (Set α)] : B != ∅ -> ∃ a, a ∈ B := by
  intro neq
  apply Classical.byContradiction
  intro contra
  rw [not_exists] at contra
  have aux := Set.empty_eq B contra
  rw [aux] at neq
  simp only [bne_self_eq_false, Bool.false_eq_true] at neq

theorem empty_set_if_empty_type (T : Fintype α) (S : Set α) : T.elems = [] → S = ∅ := by
  intro h
  apply Classical.byContradiction
  intro contra
  have exists_elem : ∃ a, a ∈ S := by
    rw [← Ne.eq_1] at contra
    apply Set.not_empty_contains_element
    exact contra
  rcases exists_elem with ⟨a, a_mem⟩
  have aux := T.complete
  specialize aux a
  rw [h] at aux
  contradiction

theorem complete_set_iff [Fintype α] (S : Set α) : (S = fun _ => True) ↔ ∀ (x : α), x ∈ S := by
constructor
. intro eq
  intro x
  rw [eq]
  simp only [Membership.mem]
. intro h
  apply Set.ext
  intro x
  constructor
  . intro x_mem
    simp only [Membership.mem]
  . intro x_mem
    grind

theorem complete_set_eq_fintype_elems (T : Fintype α) : T.elems.toSet = fun _ => True := by
  apply Set.ext
  intro x
  constructor
  . intro x_mem
    trivial
  . intro x_mem
    have x_mem_elems := T.complete x
    simp only [List.toSet, Membership.mem]
    exact x_mem_elems

theorem exists_not_mem_if_ne_complete_set (T : Fintype α) (S : Set α) : (S ≠ fun _ => True) → ∃ a, a ∉ S := by
  intro ne
  rw [Ne.eq_1] at ne
  apply Classical.byContradiction
  intro contra
  simp at contra
  have aux := complete_set_iff S
  have S_eq := aux.mpr contra
  contradiction

theorem ssubset_of_complete_set (T : Fintype α) (S : Set α) : (S ≠ fun _ => True) → S ⊂ (fun _ => True) := by
intro ne
constructor
. intro a a_mem
  trivial
. intro h
  have aux := exists_not_mem_if_ne_complete_set T S ne
  rcases aux with ⟨x, x_nmem⟩
  let complete_set : Set α := (fun a => True)
  have x_mem : x ∈ complete_set := by
    unfold complete_set
    simp only [Membership.mem]
  have x_mem_S : x ∈ S := h x x_mem
  contradiction

theorem mem_iff : ∀ {α} {S : Set α} x, x ∈ S ↔ S x := by simp [Membership.mem]

end Set

