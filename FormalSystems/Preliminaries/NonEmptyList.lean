/--Define the non-empty lists as a type.-/
class NonEmptyList (α : Type u) extends (List α) where
  nonEmpty : α.length > 0
