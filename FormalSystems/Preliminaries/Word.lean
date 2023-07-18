import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.ModEq

import FormalSystems.Preliminaries.Alphabet

def Word (α : Type u) := List α

instance Word.monoid: CancelMonoid (Word α) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_left_cancel u v w := List.append_left_cancel
  mul_right_cancel u v w := List.append_right_cancel

theorem Word.mul_eq_cons { w v : Word α } :
  w * v = x :: xs ↔ w = [] ∧ v = x :: xs ∨ ∃ (w': Word _), w = x :: w' ∧ xs = w' * v :=
  List.append_eq_cons

def Word.mul_right_cancel {w₁ w₂ t : Word α} (h : w₁ * t = w₂ * t) : w₁ = w₂ :=
  List.append_right_cancel h

def Word.mul_left_cancel {w₁ w₂ t : Word α} (h : t * w₁ = t * w₂) : w₁ = w₂ :=
  List.append_left_cancel h

def Nat.fin_mod (n : ℕ) (h: N > 0) : Fin N := ⟨ n % N, Nat.mod_lt n h ⟩

def Word.decode [inst: Alphabet α]: (n : ℕ) → Word α
  | Nat.zero => []
  | Nat.succ n => inst.decode_fin (Nat.fin_mod n Alphabet.card_pos) :: Word.decode (n / inst.card)
termination_by Word.decode n => n
decreasing_by Word.decode =>
  simp [InvImage]
  apply Nat.lt_of_le_of_lt
  exact Nat.div_le_self n inst.card
  simp

def Word.encode [inst: Alphabet α]: (w : Word α) → ℕ
  | [] => 0
  | x :: xs => Nat.succ $ Word.encode xs * inst.card + inst.encode x

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
termination_by Word.decodenk n => n
decreasing_by Word.decodenk =>
  simp [InvImage]
  apply Nat.lt_of_le_of_lt
  exact Nat.div_le_self n inst.card
  simp

instance [Alphabet α] : Denumerable (Word α) where
  encode := Word.encode
  decode := some ∘ Word.decode
  encodek := by simp
  decode_inv := by simp

@[match_pattern] def Word.epsilon : Word α := 1
notation (priority := high) "ε" => Word.epsilon

theorem Word.eps_eq_nil : (ε : Word α) = ([] : Word _) := by rfl

@[simp] theorem Word.cons_eps : w :: ε = [w] := by simp; rfl

@[simp] theorem Word.mul_eps : w * ε = w := by simp; rfl

@[simp] theorem Word.eps_mul : ε * w = w := by simp; rfl

def Word.len: (w:Word α) → Nat
  | [] => 0
  | (_::xs) => 1 + Word.len (xs)

def Word.AllElementsOfWordInSet: (w: Word α) → (S: Set α) → Prop
  | a::as, S => a ∈ S ∧ Word.AllElementsOfWordInSet as S
  | _, _ => True

instance : Membership α (Word α) := List.instMembershipList

instance : Functor Word := List.instFunctorList

instance [DecidableEq α] : DecidableEq (Word α) := List.hasDecEq

def Word.get (w: Word α) (i: Fin w.length) : α := List.get w i

instance : GetElem (Word α) ℕ α (λw i ↦ i < w.length) where
  getElem w i h := List.get w ⟨ i, h ⟩

@[simp] theorem Word.map_append (f : α → β) : 
  ∀ (u v : Word _), f <$> (u * v) = (f <$> u) * (f <$> v) := 
  List.map_append f