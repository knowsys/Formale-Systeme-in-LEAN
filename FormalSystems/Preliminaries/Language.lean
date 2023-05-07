import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Order.Kleene
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Lattice
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Function.Basic

----------------------------------ALPHABETS--------------------------------------
class FinDenumerable (α : Type u) extends Fintype α, Encodable α where
  encode_lt_card: ∀(a : α), encode a < card 

def FinDenumerable.encode_fin [inst: FinDenumerable α] (a : α) : Fin inst.card := 
  ⟨ inst.encode a, inst.encode_lt_card a ⟩

theorem FinDenumerable.encode_fin_injective [inst: FinDenumerable α] : Function.Injective (@encode_fin _ inst) := by
  intro x y; simp [Fin.eq_iff_veq, encode_fin]

def FinDenumerable.encode_embedding [inst: FinDenumerable α] : α ↪ Fin inst.card :=
  ⟨ encode_fin, encode_fin_injective ⟩

def FinDenumerable.encode_fin_bijective [inst: FinDenumerable α] : Function.Bijective (@encode_fin _ inst) := by
  apply (Fintype.bijective_iff_injective_and_card encode_fin).2
  simp; exact encode_fin_injective

theorem FinDenumerable.decode_partial_inv [inst: FinDenumerable α] (n : Fin inst.card): 
  ∃a ∈ inst.decode n, inst.encode a = n := by
  have ⟨ a, pa, _ ⟩  := encode_fin_bijective.existsUnique n
  exists a; simp [Fin.eq_iff_veq, encode_fin] at pa;
  simp [pa]; simp [<- pa]

theorem FinDenumerable.decode_fin_is_some [inst: FinDenumerable α] (n : Fin inst.card): 
  (inst.decode n.1).isSome := by
  apply Option.isSome_iff_exists.2
  apply (decode_partial_inv n).imp
  intro _ h
  exact h.1

def FinDenumerable.decode_fin [inst: FinDenumerable α] (n : Fin inst.card) : α :=
  Option.get (inst.decode n.1) (decode_fin_is_some n)

def FinDenumerable.fin_preimage_exists [inst: FinDenumerable α] (n: Fin inst.card) :
  ∃a, inst.encode a = n := by
  apply (inst.decode_partial_inv n).imp
  intro _ h; exact h.2

theorem FinDenumerable.fin_decode_eq_decode₂ [inst: FinDenumerable α] (n : Fin inst.card) :
  inst.decode n = inst.decode₂ n := by
  rw [← Option.some_get (decode_fin_is_some n)]
  apply Eq.symm
  rw [Encodable.decode₂_is_partial_inv]
  have ⟨ _, h ⟩ := fin_preimage_exists n
  simp [<- h]

theorem FinDenumerable.decode_fin_inj [inst: FinDenumerable α] {n m : Fin inst.card}
  (h₁: a = FinDenumerable.decode_fin n)
  (h₂: b = FinDenumerable.decode_fin m) :
  a = b ↔ n = m := by
  have ⟨ _, p₁ ⟩ := fin_preimage_exists n  
  simp [FinDenumerable.decode_fin, <- p₁] at h₁
  have ⟨ _, p₂ ⟩ := fin_preimage_exists m  
  simp [FinDenumerable.decode_fin, <- p₂] at h₂
  rw [h₁, h₂, Fin.eq_iff_veq, ← p₁, ← p₂]
  apply Iff.symm; apply Encodable.encode_inj

theorem FinDenumerable.decode_fin_injective [inst: FinDenumerable α] :
  Function.Injective (@FinDenumerable.decode_fin _ inst) :=
  fun a b => (FinDenumerable.decode_fin_inj 
    (@rfl α $ @decode_fin _ inst a)
    (@rfl α $ @decode_fin _ inst b)).1

def FinDenumerable.decode_embedding [inst: FinDenumerable α] : Fin inst.card ↪ α :=
  ⟨ decode_fin, decode_fin_injective ⟩

theorem FinDenumerable.encodek_fin_left_inverse [FinDenumerable α] :
  Function.LeftInverse (@decode_fin α _) encode_fin := by
  intro _; simp [encode_fin, decode_fin]

theorem FinDenumerable.encode_fin_range [inst: FinDenumerable α] :
  Set.range inst.encode_fin = Fin inst.card := by
  rw [Function.Surjective.range_eq _]
  rw [Set.univ]
  sorry
  exact encode_fin_bijective.surjective

def FinDenumerable.equiv_fin [inst: FinDenumerable α] : α ≃ Fin inst.card := by
  have tmp := Equiv.ofLeftInverse encode_fin (fun _ => inst.decode_fin) (fun _ => encodek_fin_left_inverse)
  rw [encode_fin_range] at tmp
  exact tmp

class Alphabet (α : Type u) extends FinDenumerable α, Inhabited α

theorem Alphabet.card_pos [alphabet : Alphabet α] : alphabet.card > 0 := by
  apply Finset.card_pos.mpr
  exists alphabet.default
  exact alphabet.complete alphabet.default

----------------------------------WORDS------------------------------------------
def Word (α : Type u) := List α

instance Word.monoid: CancelMonoid (Word α) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_left_cancel u v w := List.append_left_cancel
  mul_right_cancel u v w := List.append_right_cancel

def Word.mul_right_cancel {w₁ w₂ t : Word α} (h : w₁ * t = w₂ * t) : w₁ = w₂ :=
  List.append_right_cancel h

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
  | x :: xs => Word.encode xs * inst.card + 1 + inst.encode x

instance [Encodable α] : Denumerable (Word α) where
  encode := List.encodable.encode
  decode := List.encodable.decode
  encodek := List.encodable.encodek

def Word.epsilon : Word α := 1
notation (priority := high) "ε" => Word.epsilon

def Word.len: (w:Word α) → Nat
  | [] => 0
  | (_::xs) => 1 + Word.len (xs)

def Word.AllElementsOfWordInSet: (w: Word α) → (S: Set α) → Prop
  | a::as, S => a ∈ S ∧ Word.AllElementsOfWordInSet as S
  | _, _ => True

----------------------------------LANGUAGES---------------------------------------

def Language (α : Type u) := Set (Word α)

namespace Language

instance : Membership (Word α) (Language α) where
  mem x L := L x

instance : Insert (Word α) (Language α) where
  insert := Set.insert

instance : Singleton (Word α) (Language α) where
  singleton := Set.singleton

instance : HasSubset (Language α) where
  Subset := Set.Subset

def isSingleton (L : Language α) : Prop
  := ∃w, w ∈ L ∧ ∀v, v ∈ L → v = w

def concat (X Y : Language α) : Language α := 
  fun w : Word α => ∃ u v : Word α, u ∈ X ∧ v ∈ Y ∧ w = u * v
infixl:70 " ∘ₗ " => Language.concat

theorem concat_assoc (X Y Z : Language α): (X ∘ₗ Y) ∘ₗ Z = X ∘ₗ (Y ∘ₗ Z) := by
  apply Set.ext
  intro x
  constructor
  . intro
    | ⟨u, v, ⟨u1, u2, pu1, pu2, pu⟩, pv, px⟩ =>
      rw [pu, Word.monoid.mul_assoc u1 u2 v] at px
      exact ⟨ u1, u2 * v, pu1, ⟨u2, v, pu2, pv, rfl⟩, px ⟩

  . intro
    | ⟨u, v, pu, ⟨v1, v2, pv1, pv2, pv⟩, px⟩ =>
      rw [pv, <- Word.monoid.mul_assoc u v1 v2] at px
      exact ⟨ u * v1, v2, ⟨u, v1, pu, pv1, rfl⟩, pv2, px ⟩

def epsilon : Language α :=
  fun w => w = ε

def empty : Language α :=
  fun _ => False

instance : EmptyCollection (Language α) where
  emptyCollection := Language.empty

instance : Union (Language α) where
  union := Set.union

theorem mul_eps (L : Language α): L ∘ₗ Language.epsilon = L := by
  apply funext
  intro w
  apply propext
  constructor
  . rw [Language.concat]
    intro ⟨u,v, h1, h2, h3⟩
    simp [Language.epsilon, Membership.mem] at h2
    simp [h3, h2, Word.epsilon]
    exact h1
  . intro h ; simp [Language.concat]
    exists w ; simp [Membership.mem, h]
    simp [Language.epsilon] ; rfl

theorem eps_mul (L : Language α): Language.epsilon ∘ₗ L = L := by
  apply funext
  intro w
  apply propext
  constructor
  . rw [Language.concat]
    intro ⟨u,v, h1, h2, h3⟩
    simp [Language.epsilon, Membership.mem] at h1
    simp [h3, h1, Word.epsilon]
    exact h2
  . intro h
    simp [Language.concat]
    exists ε ; simp [Language.epsilon, Membership.mem]
    exists w

theorem mul_empty (L : Language α) : L ∘ₗ ∅ = ∅ := by
  apply Set.ext
  intro w 
  constructor
  . intro n
    match n with 
    | ⟨_,_,_,h,_⟩ =>
      apply False.elim h
  . intro n 
    apply False.elim n

theorem empty_mul (L : Language α) : ∅ ∘ₗ L = ∅ := by
  apply Set.ext
  intro w 
  constructor
  . intro n
    match n with 
    | ⟨_,_,h,_,_⟩ =>
      apply False.elim h
  . intro n 
    apply False.elim n

theorem concat_dist_union_r (L1 L2 L3 : Language α)
  : (L1 ∪ L2) ∘ₗ L3 = (L1 ∘ₗ L3) ∪ (L2 ∘ₗ L3) := by
  apply Set.ext 
  intro w 
  constructor 
  . intro 
    | ⟨u,v,h1,h2,h3⟩ => 
      cases h1 with 
      | inl hl => apply Or.inl; exists u; exists v 
      | inr hr => apply Or.inr; exists u; exists v
  . intro
    | Or.inl hl => cases hl with | intro u pu => cases pu with | intro v pv =>
        match pv with
        | ⟨h1, h2, h3⟩ => exists u, v; exact ⟨Or.inl h1, h2, h3⟩
    | Or.inr hr => cases hr with | intro u pu => cases pu with | intro v pv =>
        match pv with
        | ⟨h1, h2, h3⟩ => exists u, v; exact ⟨Or.inr h1, h2, h3⟩

theorem concat_dist_union_l (L1 L2 L3 : Language α)
  : L1 ∘ₗ (L2 ∪ L3) = (L1 ∘ₗ L2) ∪ (L1 ∘ₗ L3) := by
  apply Set.ext
  intro w
  constructor
  . intro 
    | ⟨u,v,h1,h2,h3⟩ =>
      cases h2 with 
      | inl hl => apply Or.inl; exists u; exists v 
      | inr hr => apply Or.inr; exists u; exists v
  . intro 
    | Or.inl hl => cases hl with | intro u pu => cases pu with | intro v pv =>
        match pv with
        | ⟨h1, h2, h3⟩ => exists u, v; exact ⟨h1, Or.inl h2, h3⟩
    | Or.inr hr => cases hr with | intro u pu => cases pu with | intro v pv =>
        match pv with
        | ⟨h1, h2, h3⟩ => exists u, v; exact ⟨h1, Or.inr h2, h3⟩

instance : Semiring (Language α) where
  mul := Language.concat
  mul_assoc := Language.concat_assoc
  
  one := Language.epsilon
  mul_one := Language.mul_eps
  one_mul := Language.eps_mul

  add := Set.union
  add_assoc := Set.union_assoc
  add_comm := Set.union_comm

  zero := ∅
  zero_mul := Language.empty_mul
  mul_zero := Language.mul_empty
  zero_add := Set.empty_union
  add_zero := Set.union_empty

  right_distrib := Language.concat_dist_union_r
  left_distrib := Language.concat_dist_union_l

def kstar (X : Language α) : Language α :=
  fun w: Word α => ∃ n : Nat, w ∈ X^n

def plus (X: Language α) : Language α :=
  fun w: Word α => 
    ∃ n:Nat, ¬ (n = 0) ∧ w ∈ X^n

postfix:1024 "⁺" => Language.plus

instance : KStar (Language α) where
  kstar := Language.kstar

postfix:1024 "∗" => KStar.kstar

def compl (L : Language α) := Set.compl L
notation:70 L:70 "ᶜ" => Language.compl L

def univ : Language α := Set.univ

theorem kleene_eq_plus_eps [Alphabet α] {L: Language α} 
: L⁺ ∪ {ε} = L∗ := by
  apply Set.ext
  intro w
  constructor
  . intro
    | Or.inl h =>
      cases h with
      | intro n r =>
        exists n 
        exact r.right 
    | Or.inr e => exists 0
  . simp [Language.kstar]
    intro
    | Exists.intro nn r => 
      cases nn with 
      | succ m => 
        apply Or.inl 
        simp [Language.plus]
        exists (Nat.succ m)
        exact ⟨Nat.succ_ne_zero m, r⟩ 
      | zero => 
        apply Or.inr
        exact r

end Language

namespace Alphabet

protected def Sigma : Language α :=
  fun w: Word α =>
    match w with
    | _::[] => True
    | _ => False

scoped[Alphabet] notation:41 "Σ" => Alphabet.Sigma

theorem Sigma.kleene_contains_all : ∀(w : Word α), w ∈ (Σ)∗
  | [] => by exists 0
  | x::xs => by
    have ⟨n, hn⟩ := Sigma.kleene_contains_all xs
    exists n + 1; exists [x]; exists xs

theorem Sigma.kleene_eq_univ : @Language.univ α = (Σ)∗ := by
  apply Set.ext
  intro w
  constructor
  . intros; exact Sigma.kleene_contains_all w
  . intros; simp [Language.univ, Set.mem_univ]

theorem Sigma.maximal_language : ∀(L : Language α), L ⊆ (Σ)∗ := by
  intro _ w _
  exact Sigma.kleene_contains_all w

end Alphabet