import FormalSystems.Preliminaries.FinDenumerable

/--Class: An alphabet is finite (`.elems`and all elements included in`.elems`),
  denumerable (`encode`and`decode`functions), all encodings (returned by`encode`)
  are `< Alphabet.cardinality`, and inhabited (existance of a`default`element).-/
class Alphabet (α : Type u) extends FinDenumerable α, Inhabited α

/--Theorem: Since alphabets are non-empty their cardinality is greater than zero.-/
theorem Alphabet.card_pos [alphabet : Alphabet α] : alphabet.card > 0 := by
  apply Finset.card_pos.mpr --A cardinality is >0 iff set is nonempty, Iff.mpr = right→left
  -- Goal now is: Prove alphabet is Nonempty.
  exists alphabet.default -- exists thanks to alphabet being inhabited
  -- We now know there is a default element, now show it is in the alphabet
  exact alphabet.complete alphabet.default
