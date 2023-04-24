
instance listEquiv [Membership α (List α)] : Setoid (List α) where
  r (a b : List α) := (∀(x : α), x ∈ a ↔ x ∈ b)
  iseqv := {
    refl := fun _ _ => Iff.rfl
    symm := fun h x => Iff.symm (h x) 
    trans := fun h1 h2 x => Iff.trans (h1 x) (h2 x)
  }

def FinSet (α : Type _) := Quotient (@listEquiv α _)

theorem list_equiv_preserves_membership 
: ∀(x : α), (a b : List α) → listEquiv.r a b → (x ∈ a) = (x ∈ b) := by
  intro x a b
  intro h
  apply propext
  exact h x

instance : Membership α (FinSet α) where
  mem x := Quotient.lift (List.Mem x) (list_equiv_preserves_membership x)
 