structure Identity { α : Type _ } (id: α) (op: α -> α -> α) where
  left: ∀x, op id x = x
  right: ∀x, op x id = x
  deriving Repr

def Associative { α : Type _ } (op: α -> α -> α) : Prop := 
  ∀ u v w, op (op u v) w = op u (op v w)

class Monoid (α : Type _) where
  mident : α
  mconcat : α -> α -> α
  identity : Identity mident mconcat
  assoc : Associative mconcat

infixr:70 " ∘ₘ " => Monoid.mconcat

instance : Monoid (List α) where
  mident := List.nil
  mconcat := List.append
  identity := {
    left := by simp
    right := by simp
  }
  assoc := List.append_assoc

