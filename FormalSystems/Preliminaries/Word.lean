import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.ModEq

import FormalSystems.Preliminaries.Alphabet
--================================================================================
-- File: Word
/-  Containts Word definition, ε, Word.len, Word.concat and multiple
    Word related theorems.
-/
--================================================================================

/--A Word, input for automatons. Depends on an Alphabet α.
  Based on the Type List.-/
def Word (α : Type u) := List α

/--Word equality is decidable using the List equality.-/
instance {α : Type u} [DecidableEq α] : DecidableEq (Word α) := List.hasDecEq

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
  List.append_eq_cons

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
  simp [InvImage]
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
    simp [<- Nat.mod_add_mod, Nat.mod_eq_of_lt $ inst.encode_lt_card x]
    simp [Nat.add_div inst.card_pos, Nat.div_eq_of_lt $ inst.encode_lt_card x]
    simp [Nat.mul_div_cancel (encode xs) inst.card_pos]
    rw [<- ite_not _]; simp [Nat.not_le_of_lt _, Nat.mod_lt _ inst.card_pos, ih]

/--Theorem:`encode`is the left inverse operation of`decode`.-/
@[simp] theorem Word.decodenk [inst: Alphabet α] :
  ∀(n : ℕ), encode (decode n : Word α) = n
  | 0 => by simp [encode, decode]
  | Nat.succ n => by
    have ih := @decodenk α _ (n / inst.card)
    simp [decode, FinDenumerable.decode_fin]
    simp [encode, inst.decode_fin_is_some (Nat.fin_mod _ _)]
    simp [ih, FinDenumerable.decode_fin_eq_option_get]
    rw [<- inst.encode_fin_eq_encode _, inst.decodenk]
    simp [Nat.fin_mod, Nat.mul_comm, Nat.div_add_mod n inst.card]
termination_by n => n
decreasing_by
  simp [InvImage]
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

/--Theorem: Appending ε doesn't change the word.-/
@[simp] theorem Word.eps_append : List.append w ε = w := by simp [Word.eps_eq_nil, List.append_nil]

/--Theorem: Appending ε doesn't change the word.-/
@[simp] theorem Word.append_eps : List.append ε w = w := by simp [Word.eps_eq_nil, List.append_nil]

/--Theorem: For words, appending and multiplying are equivalent operations.-/
theorem Word.append_eq_mul {w v : Word α}: List.append w v = w * v := by
  induction w
  case nil =>
    simp ; rw [← Word.epsilon, Word.eps_eq_nil]
  case cons head tail h_ih =>
    rw [List.append, h_ih]; rfl

/--Theorem: For words, appending and multiplying are equivalent operations.-/
theorem Word.mul_eq_append {w v : Word α}: w * v = List.append w v := by exact Word.append_eq_mul

/--Theorem: The concatenation of two words is ε if and only if both words are ε.-/
theorem Word.mul_eq_eps { w v : Word α } : w * v = ε ↔ w = ε ∧ v = ε :=
  List.append_eq_nil

/--Return the length of a word.
    TODO: Note, that all usage of Word.len could probably
    have been done with List.length, since coercion between
    the two types is trivial. This would have saved us from
    proving all the theorems below, as they have mostly
    been proven for List.length. Maybe replace this definition
    with List.length in the future.-/
def Word.len: (w:Word α) → Nat
  | [] => 0
  | (_::xs) => 1 + Word.len (xs)

/--Theorem: A word has length 0 if and only if it is ε.-/
@[simp]
theorem Word.eps_len_0 : Word.len w = 0 ↔ w = ε := by
  rw [Word.eps_eq_nil]
  apply Iff.intro
  case mp =>
    intro h_len_0
    cases w
    case nil =>
      rfl
    case cons _ _ =>
      rw [Word.len] at h_len_0
      rw [Nat.add_eq_zero] at h_len_0
      absurd h_len_0.left
      simp
  case mpr =>
    intro h_nil
    simp [h_nil, Word.len]

/--Theorem: A word has length 0 if and only if it is [].-/
@[simp]
theorem Word.nil_len_0 : Word.len w = 0 ↔ w = [] := by
  simp [Word.eps_eq_nil]

/--Theorem: The addition of the lengths of two words is the length of their product.-/
theorem Word.length_mul_eq_add { w v : Word α } : Word.len (w * v) = Word.len w + Word.len v := by
  induction w
  case nil =>
    simp [Word.len, ← Word.eps_eq_nil]
  case cons head tail ind_hyp =>
    rw [Word.mul_eq_append]
    have h_rw : List.append (head :: tail) v = head :: (List.append tail v) := by simp
    rw [h_rw, Word.len, Word.len]
    rw [Word.mul_eq_append] at ind_hyp
    rw [ind_hyp, add_assoc]

/--Theorem: Word construction respects list a :: xs construction as expected.-/
@[simp]
theorem Word.mk_cons {word : Word α} : (∃ (head : α) (tail : List α), word = Word.mk (head :: tail))
  →
  (∃ (head : α) (tail : List α), word = mk (head :: tail) ∧ Word.mk (head :: tail) = Word.mk [head] * Word.mk tail) := by
  tauto

/--Theorem: Word.len and List.length align.-/
@[simp]
theorem Word.mk_from_list_len {list : List α} : Word.len (Word.mk list) = list.length := by
  induction list
  case nil =>
    simp [Word.len]
  case cons head tail ind_hyp =>
    have h_mk_cons : Word.mk (head :: tail) = Word.mk [head] * Word.mk tail := by tauto
    rw [h_mk_cons, Word.length_mul_eq_add, List.length, ind_hyp]
    have h_1 : len (Word.mk [head]) = 1 := by tauto
    rw [h_1, add_comm]

/--Theorem: The addition of the lengths of two words is the length of their product.-/
theorem Word.length_add_eq_mul { w v : Word α } : Word.len w + Word.len v = Word.len (w * v) := by exact (@Word.length_mul_eq_add _ w v).symm

/--Return the proposition, that all elements of a specific word are in a
  specific set.-/
def Word.AllElementsOfWordInSet: (w: Word α) → (S: Set α) → Prop
  | a::as, S => a ∈ S ∧ Word.AllElementsOfWordInSet as S
  | _, _ => True

/--Allow ∈ notation for words.-/
instance : Membership α (Word α) := List.instMembershipList

/--Allow map to run over Words.-/
instance : Functor Word := List.instFunctorList

/--Equality is decidable for Words.-/
instance [DecidableEq α] : DecidableEq (Word α) := List.hasDecEq

/--Get the ith character of the word w, provided`i < w.length`.-/
def Word.get (w: Word α) (i: Fin w.length) : α := List.get w i

/--Allow for index notation: `word[i]`-/
instance : GetElem (Word α) ℕ α (λw i ↦ i < w.length) where
  getElem w i h := List.get w ⟨ i, h ⟩

/--Theorem: Characterwise function application does not care about word concatenation.-/
@[simp] theorem Word.map_append (f : α → β) :
  ∀ (u v : Word _), f <$> (u * v) = (f <$> u) * (f <$> v) :=
  List.map_append f

/--Theorem: If a symbol is an element of a word tail, it is also an element of
  head :: tail.-/
theorem Word.mem_imp_cons (elem head : α) (tail : Word α) : elem ∈ tail → elem ∈ head :: tail := by
  tauto

/--Theorem: A symbol is in a word if it is either its head or in its tail.-/
@[simp]
theorem Word.mem_cons_iff_or (elem head : α) (tail : Word α) : elem ∈ head :: tail ↔ elem = head ∨ elem ∈ tail := by
  simp

/--Theorem: A symbol is in the concatenation of two words if and only if it is in one of the words.-/
theorem Word.mem_mul_iff_or (a b : Word α) (elem : α) : elem ∈ a * b ↔ elem ∈ a ∨ elem ∈ b := by
  apply Iff.intro
  case mp =>
    intro h_left
    induction a
    case nil =>
      rw [eps_eq_nil.symm, eps_mul] at h_left
      apply Or.inr
      exact h_left
    case cons head tail ind_hyp =>
      by_cases h_eq : elem = head
      case pos =>
        apply Or.inl
        rw [h_eq]
        tauto
      case neg =>
        rw [mem_cons_iff_or, or_iff_right h_eq]
        rw [Word.mul_eq_append] at h_left
        simp [List.cons_append head tail b] at h_left
        rw [Word.mem_cons_iff_or] at h_left
        rw [or_iff_right h_eq] at h_left
        apply ind_hyp at h_left
        exact h_left
  case mpr =>
    intro h_right
    cases h_right
    case inl h_inl =>
      induction a
      case nil =>
        rw [List.mem_nil_iff elem] at h_inl
        contradiction
      case cons head tail ind_hyp =>
        rw [mem_cons_iff_or] at h_inl
        cases h_inl
        case inl h_inl =>
          rw [Word.mul_eq_append]
          simp [List.cons_append]
          rw [mem_cons_iff_or]
          apply Or.inl
          exact h_inl
        case inr h_inr =>
          apply ind_hyp at h_inr
          rw [Word.mul_eq_append]
          simp [List.cons_append]
          rw [mem_cons_iff_or]
          apply Or.inr
          exact h_inr
    case inr h_inr =>
      induction a
      case nil =>
        rw [eps_eq_nil.symm, eps_mul]
        exact h_inr
      case cons head tail ind_hyp =>
        rw [mul_eq_append]
        simp [List.cons_append]
        rw [mem_cons_iff_or]
        apply Or.inr
        exact ind_hyp

/--Theorem: The List.length and the Word.len functions behave the same for all words.-/
theorem Word.list_length_eq_word_len (word : Word α) : List.length word = Word.len word := by
  induction word
  case nil =>
    simp [Word.len]
  case cons _ _ ind_hyp =>
    simp [List.length_cons, Word.len, ind_hyp, Nat.succ_eq_add_one, add_comm]

/--Construct a longer word from a list of words.-/
def Word.concatListOfWords (list : List (Word X)) : Word X :=
  Fin.foldr list.length (fun n w => list[n] * w) ε

--#eval (Word.concatListOfWords [Word.mk ['a'], Word.mk ['b'], Word.mk ['e']])
--#eval Word.mk ['a'] * Word.mk ['d'] * Word.mk ['D','d']

/--Construct the word `w = B[0]A[0]B[1]A[1]...A[N]B[N+1]`.

  Requires As length to be one less than Bs length and B to be non-empty.-/
def Word.concat2ListsOfWordsAlternating (A : List (Word X)) (B : List (Word X)) (proof_length : A.length + 1 = B.length) (proof_B_nonempty : B.length > 0): (Word X) :=
  have _ : List.length B - 1 < List.length B := by exact Nat.pred_lt_self proof_B_nonempty
  Fin.foldr A.length (fun n w =>
  have _ : n < B.length := by rw [← proof_length] ; exact lt_trans n.isLt (Nat.lt_succ_self A.length)
  B[n] * A[n] * w)
  B[B.length-1]

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
