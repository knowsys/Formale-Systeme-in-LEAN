import FormalSystems.Preliminaries.FinDenumerable

class Alphabet (α : Type u) extends FinDenumerable α, Inhabited α

theorem Alphabet.card_pos [alphabet : Alphabet α] : alphabet.card > 0 := by
  apply Finset.card_pos.mpr
  exists alphabet.default
  exact alphabet.complete alphabet.default

