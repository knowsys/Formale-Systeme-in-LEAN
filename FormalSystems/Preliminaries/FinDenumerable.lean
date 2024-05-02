import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Countable

/--Class: Finite and denumerable types. Are finite and encodable:

  Encodable (i.e. constructively countable): can put elements inside
  with`encode : α → ℕ`and out with`decode : ℕ → α`.

  Fintype: is finite: has a finset`elems`attribute and a proof that all elements of
  this type are in`elems`.

  Additionally require that all encodings return numbers less than a cardinality.
  Can get this proposition:`encode_lt_card`.-/
class FinDenumerable (α : Type u) extends Fintype α, Encodable α where
  encode_lt_card: ∀(a : α), encode a < card
  -- the attribute that seperates FinDenumerable from just Fintype + Encodable?

/--`FinDenumerable.enocde_fin a`returns
an element of the canonical set with the same cardinality as`FinDenumerable`.-/
def FinDenumerable.encode_fin [inst: FinDenumerable α] (a : α) : Fin inst.card :=
  ⟨ inst.encode a, inst.encode_lt_card a ⟩
  -- apply Fin.mk on: encoding as ℕ of a + proof that all encodings of a are < card of inst

/-- Theorem:`encode`and`encode_fin`return the same thing.-/
theorem FinDenumerable.encode_fin_eq_encode [inst: FinDenumerable α] :
  ∀(a : α), encode_fin a = inst.encode a := by simp [encode_fin]

-- ↑ is coercion (type upcast?)

/-- Theorem:`encode_fin`is injective (see`Function.Injective`).-/
theorem FinDenumerable.encode_fin_injective [inst: FinDenumerable α] : Function.Injective inst.encode_fin := by
  intro x y; simp [Fin.ext_iff, encode_fin]

/--An embedding function from a finite, denumerable type`α`to a Finset of size`inst.cardinality`.

  Embedding: a structure that is contained within another structure,
  both instances of some structure type, e.g. groups (here finite sets).
  Show this by giving an injective embedding function from the embedded
  to the embedding struct. s.t. the function is "structure preserving".-/
def FinDenumerable.encode_embedding [inst: FinDenumerable α] : α ↪ Fin inst.card :=
  ⟨ encode_fin, encode_fin_injective ⟩
  -- Function.Embedding.mk : (toFun : α → β) (inj' : Function.Injective toFun) : α ↪ β

/--A proof that`encode_fin`is bijective. Note: Why is this not a theorem?-/
def FinDenumerable.encode_fin_bijective [inst: FinDenumerable α] : Function.Bijective inst.encode_fin := by
  apply (Fintype.bijective_iff_injective_and_card encode_fin).2
  simp; exact encode_fin_injective

/--Theorem: Every`n`in a finite set of the same cardinality as`inst` can be encoded
into a number`a`that can be decoded back into`n`.-/
theorem FinDenumerable.decode_partial_inv [inst: FinDenumerable α] (n : Fin inst.card):
  ∃a ∈ inst.decode n, inst.encode a = n := by
  have ⟨ a, pa, _ ⟩  := encode_fin_bijective.existsUnique n
  exists a; simp [Fin.ext_iff, encode_fin] at pa;
  simp [pa]; simp [<- pa]

/--Theorem: Decoding an element`n`of a finite set gets you something.-/
theorem FinDenumerable.decode_fin_is_some [inst: FinDenumerable α] (n : Fin inst.card):
  (inst.decode n.1).isSome := by
  apply Option.isSome_iff_exists.2
  apply (decode_partial_inv n).imp
  intro _ h
  exact h.1

/--Get the decoding of an element`n`in a finite set of correct cardinality.
  The decoding has type `α`.-/
def FinDenumerable.decode_fin [inst: FinDenumerable α] (n : Fin inst.card) : α :=
  Option.get (inst.decode n.1) (decode_fin_is_some n)

/--Theorem:`decode_fin`effectively does the same as`Option.get`.-/
theorem FinDenumerable.decode_fin_eq_option_get [inst: FinDenumerable α] (n : Fin inst.card) :
  Option.get (inst.decode n.1) (decode_fin_is_some n) = decode_fin n := by simp [decode_fin]

/--Theorem: Every`n`in a finite set of correct cardinality is an encoding of
  some element`a`of FinDenumerable.-/
def FinDenumerable.fin_preimage_exists [inst: FinDenumerable α] (n: Fin inst.card) :
  ∃a, inst.encode a = n := by
  apply (inst.decode_partial_inv n).imp
  intro _ h; exact h.2

/--Theorem:`decode`and`decode₂`return the same values.(`decode₂`is a failsafe version of`decode`.)-/
theorem FinDenumerable.fin_decode_eq_decode₂ [inst: FinDenumerable α] (n : Fin inst.card) :
  inst.decode n = inst.decode₂ n := by
  rw [← Option.some_get (decode_fin_is_some n)]
  apply Eq.symm
  rw [Encodable.decode₂_is_partial_inv]
  have ⟨ _, h ⟩ := fin_preimage_exists n
  simp [<- h]

/--Theorem:`decode_fin`is injective.-/
theorem FinDenumerable.decode_fin_inj [inst: FinDenumerable α] {n m : Fin inst.card}
  (h₁: a = FinDenumerable.decode_fin n)
  (h₂: b = FinDenumerable.decode_fin m) :
  a = b ↔ n = m := by
  have ⟨ _, p₁ ⟩ := fin_preimage_exists n
  simp [FinDenumerable.decode_fin, <- p₁] at h₁
  have ⟨ _, p₂ ⟩ := fin_preimage_exists m
  simp [FinDenumerable.decode_fin, <- p₂] at h₂
  rw [h₁, h₂, Fin.ext_iff, ← p₁, ← p₂]
  apply Iff.symm; apply Encodable.encode_inj

/--Theorem:`decode_fin`is injective.-/
theorem FinDenumerable.decode_fin_injective [inst: FinDenumerable α] :
  Function.Injective (@FinDenumerable.decode_fin _ inst) :=
  fun a b => (FinDenumerable.decode_fin_inj
    (@rfl α $ @decode_fin _ inst a)
    (@rfl α $ @decode_fin _ inst b)).1

/--An embedding function based on`decode`.-/
def FinDenumerable.decode_embedding [inst: FinDenumerable α] : Fin inst.card ↪ α :=
  ⟨ decode_fin, decode_fin_injective ⟩

/--Theorem:`decode`is a left inverse of`encode`.`decode encode = id`.-/
theorem FinDenumerable.encodek_fin_left_inverse [FinDenumerable α] :
  Function.LeftInverse (@decode_fin α _) encode_fin := by
  intro _; simp [encode_fin, decode_fin]

/--Theorem:`encode`is a left inverse of`decode`.`encode decode = id`.-/
theorem FinDenumerable.decodenk [inst: FinDenumerable α] :
  ∀(n : Fin inst.card), encode_fin (decode_fin n) = n := by
  simp [encode_fin, Fin.ext_iff, decode_fin]; intro n
  have ⟨ a, ph ⟩ := fin_preimage_exists n
  simp [<- ph]

/--Theorem:`encode_fin`has a range of exactly the finite set with the cardinality of`inst`.-/
theorem FinDenumerable.encode_fin_range [inst: FinDenumerable α] :
  ↑(Set.range inst.encode_fin) ≃ Fin inst.card := by
  rw [Function.Surjective.range_eq _]
  exact Equiv.Set.univ (Fin (Fintype.card α))
  exact encode_fin_bijective.surjective

/--Theorem: The finite denumerable set based on type`α`has exactly the same
  size as`α`. (`α ≃ β`is the type of functions from`α → β`with a two-sided inverse.)-/
theorem FinDenumerable.equiv_fin [inst: FinDenumerable α] : α ≃ Fin inst.card := by
  have tmp := Equiv.ofLeftInverse encode_fin (fun _ => inst.decode_fin) (fun _ => encodek_fin_left_inverse)
  apply Equiv.trans tmp encode_fin_range
