import Logic

def Set (α : Type _) := α -> Prop

instance : Membership α (Set α) where
  mem x s := s x

def subset {S : Type -> Type} [Membership α (S α)] (X Y : S α) : Prop 
  := ∀ e : α, e ∈ X → e ∈ Y
infixr:50 " ⊆ " => subset

class SetAlgebra (S : Type -> Type) (α : Type) [Membership α (S α)] where
  setext { X Y : S α } (h: ∀(x: α), x ∈ X ↔ x ∈ Y): X = Y

  union : S α -> S α -> S α
  union_prop : ∀(X Y : S α), ∀(x : α), x ∈ (union X Y) ↔ x ∈ X ∨ x ∈ Y

  intersection : S α -> S α -> S α
  intersection_prop : ∀(X Y : S α), ∀(x : α), x ∈ (intersection X Y) ↔ x ∈ X ∧ x ∈ Y

  diff : S α -> S α -> S α
  diff_prop : ∀(X Y : S α), ∀(x : α), x ∈ (diff X Y) ↔ x ∈ X ∧ ¬ (x ∈ Y)

  empty : S α
  empty_prop : ∀(x : α), ¬(x ∈ empty)

notation (priority := high) "∅" => SetAlgebra.empty
infixr:65 " ∪ " => SetAlgebra.union
infixr:80 " ∩ " => SetAlgebra.intersection

instance : SetAlgebra Set α where
  setext h := funext (λx => propext (h x))

  union X Y := fun x => x ∈ X ∨ x ∈ Y
  union_prop := by simp [Membership.mem]

  intersection X Y := fun x => x ∈ X ∧ x ∈ Y
  intersection_prop := by simp [Membership.mem]
  
  diff X Y := fun x => x ∈ X ∧ ¬ (x ∈ Y)
  diff_prop := by simp [Membership.mem]

  empty := fun _ => False
  empty_prop := by simp [Membership.mem]

theorem inters_indem [Membership α (S α)] [SetAlgebra S α] (X : S α) 
: X ∩ X = X := by
  apply SetAlgebra.setext
  intro x
  constructor
  . simp [SetAlgebra.intersection_prop]
    intro h
    exact h
  . intro h
    rw [SetAlgebra.intersection_prop]
    exact ⟨h,h⟩ 

theorem inters_empty [Membership α (S α)] [SetAlgebra S α] (X : S α)
: X ∩ ∅ = ∅ := by 
  apply SetAlgebra.setext
  intro x
  constructor
  . rw [SetAlgebra.intersection_prop]
    exact (·.right)
  . intro h
    apply False.elim
    exact SetAlgebra.empty_prop x h

theorem inters_comm [Membership α (S α)] [SetAlgebra S α] (X : S α)
: X ∩ Y = Y ∩ X := by 
  apply SetAlgebra.setext 
  simp [SetAlgebra.intersection_prop, And.comm]

theorem union_comm [Membership α (S α)] [SetAlgebra S α] (X : S α)
: X ∪ Y = Y ∪ X := by
  apply SetAlgebra.setext
  simp [SetAlgebra.union_prop, Or.comm]

theorem union_dist_intersection [Membership α (S α)] [SetAlgebra S α] (X Y Z : S α)
: X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  apply SetAlgebra.setext
  simp [SetAlgebra.union_prop, SetAlgebra.intersection_prop, Or.distrib_and]

theorem intersection_dist_union [Membership α (S α)] [SetAlgebra S α] (X Y Z : S α)
: X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  apply SetAlgebra.setext
  simp [SetAlgebra.intersection_prop, SetAlgebra.union_prop, And.distrib_or]

namespace Set

def complement {α : Type u} (X : Set α) : Set α := fun w => ¬(w ∈ X)

theorem morgan_union (X Y : Set α) 
  : complement (X ∪ Y) = (complement X ∩ complement Y) := by
  apply SetAlgebra.setext
  intro w
  exact Or.morgan

theorem morgan_inters (X Y : Set α) 
  : complement (X ∩ Y) = (complement X ∪ complement Y) := by
  apply SetAlgebra.setext
  intro w
  exact And.morgan

end Set