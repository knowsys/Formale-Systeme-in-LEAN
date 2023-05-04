import Set

instance listEquiv [Membership α (List α)] : Setoid (List α) where
  r (a b : List α) := (∀(x : α), x ∈ a ↔ x ∈ b)
  iseqv := {
    refl := fun _ _ => Iff.rfl
    symm := fun h x => Iff.symm (h x) 
    trans := fun h1 h2 x => Iff.trans (h1 x) (h2 x)
  }

@[simp] def FinSet (α : Type _) := Quotient (@listEquiv α _)

theorem list_equiv_preserves_membership 
: ∀(x : α), (a b : List α) → listEquiv.r a b → (x ∈ a) = (x ∈ b) := by
  intro x a b
  intro h
  apply propext
  exact h x

theorem list_concat_mem_impl_mem {x : α} {a b : List α} (h1: l = a ++ b) (h: x ∈ l)
  : x ∈ a ∨ x ∈ b := by
  induction h with
  | head x _ =>
    cases a with
    | nil =>
      rw [List.nil_append] at h1
      apply Or.inr
      rw [<- h1]
      simp [Membership.mem, List.Mem.head]
    | cons a _ => sorry
  | tail _ _ => sorry

theorem list_concat_preserves_membership
: ∀(x : α), ∀(a b : List α), x ∈ (a ++ b) ↔ (x ∈ a) ∨ (x ∈ b) := by
  intro x a b
  apply Iff.intro
  . apply list_concat_mem_impl_mem; rfl
  . intro h ; cases h
    case mpr.inl h => exact List.mem_append_of_mem_left _ h
    case mpr.inr h => exact List.mem_append_of_mem_right _ h

instance FinSet.mem_inst : Membership α (FinSet α) where
  mem x := Quotient.lift (List.Mem x) (list_equiv_preserves_membership x)

theorem FinSet.whatever { X Y : FinSet α } 
  (ha : Quotient.mk listEquiv a = X) 
  (hb : Quotient.mk listEquiv b = Y) 
  (h: x ∈ X ↔ x ∈ Y)
  : x ∈ a ↔ x ∈ b
  := by sorry

def FinSet.union (X Y : FinSet α) : FinSet α :=
  have proof (a₁ b₁ a₂ b₂ : List α) (eqa : a₁ ≈ a₂) (eqb : b₁ ≈ b₂) :
    Quotient.mk' (a₁ ++ b₁) = Quotient.mk' (a₂ ++ b₂) := by
    sorry
  Quotient.liftOn₂ X Y (fun x y => Quotient.mk' (x ++ y)) proof

def List.intersection : (a b : List α) → List α
  | nil, _ => nil
  | _, nil => nil
  | cons a xs, cons a ys => a :: (List.intersection xs ys)


def FinSet.intersection (X Y : FinSet α) : FinSet α :=
  have proof (a₁ b₁ a₂ b₂ : List α) (eqa : a₁ ≈ a₂) (eqb : b₁ ≈ b₂) :
    Quotient.mk' (a₁ ++ b₁) = Quotient.mk' (a₂ ++ b₂) := by
    sorry
  Quotient.liftOn₂ X Y (fun x y => Quotient.mk' ()) proof



instance : SetAlgebra FinSet α where
  empty := Quotient.mk listEquiv []
  empty_prop := by
    intro x h
    cases h

  setext := by
    intro X Y h
    simp at X Y
    have ⟨_, h1⟩ := Quotient.exists_rep X
    have ⟨_, h2⟩ := Quotient.exists_rep Y
    rw [<- h1, <- h2]
    apply Quotient.sound
    simp [HasEquiv.Equiv, Setoid.r]
    intro x
    exact FinSet.whatever h1 h2 (h x)

  union := FinSet.union
  union_prop := sorry

  

