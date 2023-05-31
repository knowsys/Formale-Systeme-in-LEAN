import FormalSystems.Chomsky.ContextFree.ContextFreeGrammar

import Mathlib.Data.Finset.Basic

inductive RegularProduction (Z: Finset α) (V: Finset nt) where
  | eps (lhs: V)
  | alpha (lhs: V) (rhs: Z)
  | cons (lhs: V) (rhs: Z × V)
  deriving DecidableEq

def RegularProduction.lhs : RegularProduction Z V → V
  | eps l => l
  | alpha l _ => l
  | cons l _ => l

def RegularProduction.rhs : RegularProduction Z V → Word (V ⊕ Z)
  | eps _ => ε
  | alpha _ a => [.inr a]
  | cons _ ⟨ a, A ⟩ => [.inr a, .inl A]

def RegularProduction.isEps : RegularProduction Z V → Prop
  | eps _ => True
  | _ => False

instance { α nt: Type } { Z: Finset α } { V: Finset nt } :
  DecidablePred (@RegularProduction.isEps α Z nt V) := fun x =>
  match x with
  | RegularProduction.eps _ => Decidable.isTrue trivial
  | RegularProduction.alpha _ _ => Decidable.isFalse (λh => h)
  | RegularProduction.cons _ _ => Decidable.isFalse (λh => h)

instance : Coe (RegularProduction Z V) (ContextFreeProduction Z V) where
  coe p := {
    lhs := p.lhs,
    rhs := p.rhs,
  }

def RegularProduction.toContextFree : RegularProduction Z V ↪ ContextFreeProduction Z V where
  toFun := Coe.coe
  inj' p₁ p₂ := by 
    simp [Coe.coe]
    intro hl hr
    match p₁ with
    | eps _ => 
      match p₂ with
      | eps _ => simp [lhs] at hl; rw [hl]
    | alpha _ _ =>
      match p₂ with
      | alpha _ _ => 
        simp [lhs] at hl; simp [rhs] at hr
        rw [List.cons_eq_cons] at hr; simp at hr
        simp [hl, hr]
    | cons _ ⟨ _, _ ⟩ =>
      match p₂ with
      | cons _ _ =>
        simp [lhs] at hl; simp [rhs] at hr
        rw [List.cons_eq_cons] at hr; simp at hr
        simp [hl, hr]

def RegularProduction.toProduction : RegularProduction Z V ↪ GenericProduction Z V :=
  toContextFree.trans ContextFreeProduction.toProduction

instance : Production α nt RegularProduction :=
  Production.fromEmbedding $ fun _ _ => RegularProduction.toProduction

def RegularGrammar (α nt: Type) := @Grammar α nt RegularProduction _

instance : Coe (RegularGrammar α nt) (ContextFreeGrammar α nt) where
  coe g := { g with
    productions := g.productions.map RegularProduction.toContextFree
  }

instance : Coe (RegularGrammar α nt) (@Grammar α nt GenericProduction _) where
  coe g := { g with
    productions := g.productions.map RegularProduction.toProduction
  }
