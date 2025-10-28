import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.ModEq

import FormaleSystemeInLean.Preliminaries.Alphabet
--================================================================================
-- File: Word
/-  Containts Word definition, ε, Word.len, Word.concat and multiple
    Word related theorems.
-/
--================================================================================

/--A Word, input for automatons. Depends on an Alphabet α.
  Based on the Type List.-/
def Word (α : Type u) := List α

/--Words are lists and can thus be coerced.-/
instance (_ : Word α): Coe (Word α) (List α) where
  coe word := word

/--Construct a word from a list.-/
def Word.mk (w: List α) : Word α := w

/--Words are (Cancel-) Monoids. Enables `mul`,`mul_assoc`,
  `one`,`one_mul`,`mul_one`,`mul_left_cancel` and `mul_right_cancel`.-/
instance Word.monoid: CancelMonoid (Word α) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_left_cancel u v w := List.append_cancel_left
  mul_right_cancel u v w := List.append_cancel_right

/--Theorem: The concatenation (`*`) of two words`w`and`v`can be denoted with`x::xs`
  if and only if the first word`w`is empty and`v`is`x::xs`or`x`is the first
  letter of`w`and`xs`is the rest plus`v`.-/
theorem Word.mul_eq_cons { w v : Word α } :
  w * v = x :: xs ↔ w = [] ∧ v = x :: xs ∨ ∃ (w': Word _), w = x :: w' ∧ xs = w' * v :=
  List.append_eq_cons_iff

/--Theorem: If any two words are the same, any of their prefixes are also the same.-/
def Word.mul_right_cancel {w₁ w₂ t : Word α} (h : w₁ * t = w₂ * t) : w₁ = w₂ :=
  List.append_cancel_right h

/--Theorem: If any two words are the same, any of their suffixes are also the same.-/
def Word.mul_left_cancel {w₁ w₂ t : Word α} (h : t * w₁ = t * w₂) : w₁ = w₂ :=
  List.append_cancel_left h

/--Return a version of the natural numbers restricted to numbers less than`N`,
  provided`N`is greater 0.-/
def Nat.fin_mod (n : ℕ) (h: N > 0) : Fin N := ⟨ n % N, Nat.mod_lt n h ⟩

/--Turns a natural number encoding into its Word. Encoding is multiplication based.-/
def Word.decode [inst: Alphabet α]: (n : ℕ) → Word α
  -- Can use Alphabet.decode_fin because Alphabet is a FinDenumerable
  | Nat.zero => []
  | Nat.succ n => inst.decode_fin (Nat.fin_mod n Alphabet.card_pos) :: Word.decode (n / inst.card)
termination_by n => n
decreasing_by
  apply Nat.lt_of_le_of_lt
  exact Nat.div_le_self n inst.card
  simp

/--Turns a Word into its natural number encoding. Encoding is multiplication based.-/
def Word.encode [inst: Alphabet α]: (w : Word α) → ℕ
  | [] => 0
  | x :: xs => Nat.succ $ Word.encode xs * inst.card + inst.encode x

/--Theorem:`decode`is the left inverse operation of`encode`.-/
@[simp] theorem Word.encodek [inst: Alphabet α] :
  ∀(w: Word α), decode (encode w) = w
  | [] => by simp [encode, decode]
  | x::xs => by
    have ih := encodek xs
    simp [encode, decode, Nat.fin_mod, FinDenumerable.decode_fin]
    simp [Nat.mod_eq_of_lt $ inst.encode_lt_card x]
    simp [Nat.add_div inst.card_pos, Nat.div_eq_of_lt $ inst.encode_lt_card x]
    rw [<- ite_not _]; simp [Nat.not_le_of_lt _, Nat.mod_lt _ inst.card_pos, ih]

/--Theorem:`encode`is the left inverse operation of`decode`.-/
@[simp] theorem Word.decodenk [inst: Alphabet α] :
  ∀(n : ℕ), encode (decode n : Word α) = n
  | 0 => by simp [encode, decode]
  | Nat.succ n => by
    have ih := @decodenk α _ (n / inst.card)
    simp [decode, FinDenumerable.decode_fin]
    simp [encode]
    simp [ih, FinDenumerable.decode_fin_eq_option_get]
    rw [<- inst.encode_fin_eq_encode _, inst.decodenk]
    simp [Nat.fin_mod, Nat.mul_comm, Nat.div_add_mod n inst.card]
termination_by n => n
decreasing_by
  apply Nat.lt_of_le_of_lt
  exact Nat.div_le_self n inst.card
  simp

/--Alphabet is a Denumerable. Relevant operations:`encode`,`decode`,`encodek`,`decode_inv`.-/
instance [Alphabet α] : Denumerable (Word α) where
  encode := Word.encode
  decode := some ∘ Word.decode
  encodek := by simp
  decode_inv := by simp

/--The empty word. Defined as`1`.-/
@[match_pattern] def Word.epsilon : Word α := 1

/--Match ε to Word.epsilon-/
notation (priority := high) "ε" => Word.epsilon

/--Theorem: `ε`and`[]`are the same.-/
theorem Word.eps_eq_nil : (ε : Word α) = ([] : Word _) := by rfl

/--Theorem: Appending ε doesn't change the word.-/
@[simp] theorem Word.cons_eps : w :: ε = [w] := by simp; rfl

/--Theorem: Concatenating ε doesn't change the word.-/
@[simp] theorem Word.mul_eps : w * ε = w := by simp; rfl

/--Theorem: Concatenating ε doesn't change the word.-/
@[simp] theorem Word.eps_mul : ε * w = w := by simp; rfl

/--Theorem: The concatenation of two words is ε if and only if both words are ε.-/
theorem Word.mul_eq_eps { w v : Word α } : w * v = ε ↔ w = ε ∧ v = ε :=
  List.append_eq_nil_iff

/--Return the length of a word. -/
def Word.len (w: Word α) : Nat := List.length w

/--Theorem: A word has length 0 if and only if it is ε.-/
theorem Word.eps_len_0 : Word.len w = 0 ↔ w = ε := by
  rw [Word.len, Word.eps_eq_nil, List.length_eq_zero_iff]

/--Theorem: The addition of the lengths of two words is the length of their product.-/
theorem Word.length_mul_eq_add { w v : Word α } : Word.len (w * v) = Word.len w + Word.len v := by
  unfold Word.len
  unfold_projs
  simp

/--Return the proposition, that all elements of a specific word are in a
  specific set.-/
def Word.AllElementsOfWordInSet: (w: Word α) → (S: Set α) → Prop
  | a::as, S => a ∈ S ∧ Word.AllElementsOfWordInSet as S
  | _, _ => True

/--Allow ∈ notation for words.-/
instance : Membership α (Word α) := List.instMembership

/--Allow map to run over Words.-/
instance : Functor Word := List.instFunctor

/--Equality is decidable for Words.-/
instance [DecidableEq α] : DecidableEq (Word α) := List.hasDecEq

/--Get the ith character of the word w, provided`i < w.length`.-/
def Word.get (w: Word α) (i: Fin w.length) : α := List.get w i

/--Allow for index notation: `word[i]`-/
instance : GetElem (Word α) ℕ α (λw i ↦ i < w.length) where
  getElem w i h := List.get w ⟨ i, h ⟩

/--Theorem: Characterwise function application does not care about word concatenation.-/
@[simp] theorem Word.map_append (f : α → β) :
  ∀ (u v : Word _), f <$> (u * v) = (f <$> u) * (f <$> v) := fun _ _ =>
  List.map_append

/--Theorem: A symbol is in the concatenation of two words if and only if it is in one of the words.-/
theorem Word.mem_mul_iff_or (a b : Word α) (elem : α) : elem ∈ a * b ↔ elem ∈ a ∨ elem ∈ b := by
  unfold_projs
  exact List.mem_append

/--Construct a longer word from a list of words.-/
def Word.concatListOfWords (list : List (Word X)) : Word X :=
  Fin.foldr list.length (fun n w => list[n] * w) ε

--#eval (Word.concatListOfWords [Word.mk ['a'], Word.mk ['b'], Word.mk ['e']])
--#eval Word.mk ['a'] * Word.mk ['d'] * Word.mk ['D','d']

-- This section illustrates how we can define and use alphabets.

/--Define a finite set of symbols.-/
def alphabetSymbolList : Finset Char := List.toFinset ['a','b','c','1','2','3','4']
/--Defining an Alphabet is not neccessary and is basically
  just proving, that the alphabet is finite, denumerable and
  non-empty. Because Alphabet is defined as a class, anything that
  is finite, denumerable and non-empty is automatically considered
  an alphabet.-/

def abcList : List (Word alphabetSymbolList) := [Word.mk [⟨ 'a' , by decide
  ⟩] , Word.mk [⟨ 'b' , by decide ⟩], Word.mk [⟨ 'c', by decide⟩ ]]
def numberList : List (Word alphabetSymbolList) := [Word.mk [⟨'1', by decide⟩], Word.mk [⟨'2', by decide⟩], Word.mk [⟨'3', by decide⟩], Word.mk [⟨'4', by decide⟩]]

--#eval (Word.concat2ListsOfWordsAlternating abcList numberList (by decide) (by decide))
--#eval Word.mk ['a'] * Word.mk ['d'] * Word.mk ['D','d']
