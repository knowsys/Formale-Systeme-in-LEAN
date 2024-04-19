import Mathlib.Algebra.Order.Kleene
import Mathlib.Algebra.Group.NatPowAssoc

import FormalSystems.Preliminaries.Word

import Mathlib.Data.Fintype.Lattice
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

instance : CompleteBooleanAlgebra (Language α) :=
  Pi.instCompleteBooleanAlgebra

instance : Inter (Language α) where
  inter := Set.inter

instance : Union (Language α) where
  union := Set.union

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
    assumption

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

instance : Zero (Language α) where 
  zero := ∅

instance : Add (Language α) where 
  add := Set.union

instance : Semiring (Language α) where
  mul := Language.concat
  mul_assoc := Language.concat_assoc

  one := Language.epsilon
  mul_one := Language.mul_eps
  one_mul := Language.eps_mul

  add_assoc := Set.union_assoc
  add_comm := Set.union_comm

  zero_mul := Language.empty_mul
  mul_zero := Language.mul_empty
  zero_add := Set.empty_union
  add_zero := Set.union_empty

  right_distrib := Language.concat_dist_union_r
  left_distrib := Language.concat_dist_union_l

  nsmul := nsmulRec

def kstar (X : Language α) : Language α :=
  fun w: Word α => ∃ n : Nat, w ∈ X^n

def plus (X: Language α) : Language α :=
  fun w: Word α =>
    ∃ n:Nat, ¬ (n = 0) ∧ w ∈ X^n

postfix:1024 "⁺" => Language.plus

instance : KStar (Language α) where
  kstar := Language.kstar

postfix:1024 "∗" => KStar.kstar

instance : Complement (Language α) where
  complement := Set.compl

notation:70 L:70 "ᶜ" => Language.complement L

def univ : Language α := Set.univ

theorem kleene_eq_plus_eps {L: Language α}
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
  . simp [KStar.kstar]
    intro
    | Exists.intro nn r =>
      cases nn with
      | succ m =>
        apply Or.inl
        unfold Language.plus
        exists (Nat.succ m)
        exact ⟨Nat.succ_ne_zero m, r⟩
      | zero =>
        apply Or.inr
        exact r

protected def Sigma : Language α :=
  fun w: Word α =>
    match w with
    | _::[] => True
    | _ => False

scoped[Language] notation:41 "Σ" => Language.Sigma

theorem Sigma.kleene_contains_all : ∀(w : Word α), w ∈ (Σ)∗
  | [] => by exists 0
  | x::xs => by
    have ⟨n, hn⟩ := Sigma.kleene_contains_all xs
    exists (1 + n)
    simp [pow_add]
    exists [x]
    exists xs

theorem Sigma.kleene_eq_univ : @Language.univ α = (Σ)∗ := by
  apply Set.ext
  intro w
  constructor
  . intros; exact Sigma.kleene_contains_all w
  . intros; simp [Language.univ, Set.mem_univ]

theorem Sigma.maximal_language : ∀(L : Language α), L ⊆ (Σ)∗ := by
  intro _ w _
  exact Sigma.kleene_contains_all w

end Language
