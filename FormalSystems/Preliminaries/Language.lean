import Mathlib.Data.Fintype.Basic

----------------------------------ALPHABETS--------------------------------------
class Alphabet (α : Type u) extends Fintype α, Inhabited α

----------------------------------WORDS------------------------------------------
def Word (α : Type u) := List α

instance Word.monoid_instance: Monoid (Word α) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := List.nil
  one_mul := List.nil_append
  mul_one := List.append_nil

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

instance Language.mem_instance: Membership (Word α) (Language α) where
  mem x L := L x

def Language.concat (X Y : Language α) : Language α := 
  fun w : Word α => ∃ u v : Word α, u ∈ X ∧ v ∈ Y ∧ w = u * v
infixl:70 " ∘ₗ " => Language.concat

theorem Language.concat_assoc (X Y Z : Language α): (X ∘ₗ Y) ∘ₗ Z = X ∘ₗ (Y ∘ₗ Z) := by
  apply Set.ext
  intro x
  constructor
  . intro
    | ⟨u, v, pu, pv, px⟩ =>
      match pu with
      | ⟨u1, u2, pu1, pu2, pu⟩ =>
        rw [pu, Word.monoid_instance.mul_assoc u1 u2 v] at px
        exact ⟨ u1, u2 * v, pu1, ⟨u2, v, pu2, pv, rfl⟩, px ⟩

  . intro
    | ⟨u, v, pu, pv, px⟩ =>
      match pv with
      | ⟨v1, v2, pv1, pv2, pv⟩ =>
        rw [pv, <- Word.monoid_instance.mul_assoc u v1 v2] at px
        exact ⟨ u * v1, v2, ⟨u, v1, pu, pv1, rfl⟩, pv2, px ⟩

def Language.epsilon : Language α :=
  fun w => w = ε

def Language.empty : Language α :=
  fun _ => False

instance : EmptyCollection (Language α) where
  emptyCollection := Language.empty

instance : Union (Language α) where
  union := Set.union

theorem Language.mul_eps (L : Language α): L ∘ₗ Language.epsilon = L := by
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
    exists ε ; simp [Language.epsilon, Membership.mem, Word.epsilon]

theorem Language.eps_mul (L : Language α): Language.epsilon ∘ₗ L = L := by
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

theorem Language.mul_empty (L : Language α) : L ∘ₗ ∅ = ∅ := by
  apply Set.ext
  intro w 
  constructor
  . intro n
    match n with 
    | ⟨_,_,_,h,_⟩ =>
      apply False.elim h
  . intro n 
    apply False.elim n

theorem Language.empty_mul (L : Language α) : ∅ ∘ₗ L = ∅ := by
  apply Set.ext
  intro w 
  constructor
  . intro n
    match n with 
    | ⟨_,_,h,_,_⟩ =>
      apply False.elim h
  . intro n 
    apply False.elim n

theorem Language.concat_dist_union_r (L1 L2 L3 : Language α) : (L1 ∪ L2) ∘ₗ L3 = (L1 ∘ₗ L3) ∪ (L2 ∘ₗ L3) := by
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

theorem Language.concat_dist_union_l (L1 L2 L3 : Language α) : L1 ∘ₗ (L2 ∪ L3) = (L1 ∘ₗ L2) ∪ (L1 ∘ₗ L3) := by
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

instance Language.semiring: Semiring (Language α) where
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

def Language.kleene [Alphabet α] (X : Language α) : Language α :=
  fun w: Word α => ∃ n : Nat, w ∈ X^n

def Language.plus [Alphabet α] (X: Language α) : Language α :=
  fun w: Word α => 
    ∃ n:Nat, ¬ (n = 0) ∧ w ∈ X^n

def Sigma.language [Alphabet α] : Language α := 
  fun w: Word α =>
    match w with
    | _::[] => True
    | _ => False

def Sigma.kleene [Alphabet α] : Language α :=
  fun _: Word α => True

def Language.complement (L : Language α) := fun x => x ∉ L

theorem Language.kleene_eq_plus_eps [Alphabet α] {L: Language α} 
: Language.plus L ∪ Language.epsilon = Language.kleene L := by 
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
  . simp [Language.kleene]
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
