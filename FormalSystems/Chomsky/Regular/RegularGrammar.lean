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

@[simp] theorem RegularProduction.rhs_eq_rhs { p: RegularProduction Z V } :
  Production.rhs p = p.rhs := by rfl

@[simp] theorem RegularProduction.lhs_eq_lhs { p: RegularProduction Z V } :
  Production.lhs p = [Sum.inl p.lhs] := by rfl

instance : Production.ContextFree α nt RegularProduction where
  lhs_var := RegularProduction.lhs
  lhs_condition p := by rfl

def RegularGrammar (α nt: Type) := @Grammar α nt RegularProduction _

instance : Coe (RegularGrammar α nt) (ContextFreeGrammar α nt) where
  coe g := { g with
    productions := g.productions.map RegularProduction.toContextFree
  }

instance : Coe (RegularGrammar α nt) (@Grammar α nt GenericProduction _) where
  coe g := { g with
    productions := g.productions.map RegularProduction.toProduction
  }

namespace RegularGrammar

open Grammar
variable { G: RegularGrammar α nt }

inductive NonTerminatedDerivation (G: RegularGrammar α nt): G.V → Word G.Z → Type
  | start (h: w = ε) : G.NonTerminatedDerivation v w
  | cons (h: .cons v (a, v') ∈ G.productions) (d': G.NonTerminatedDerivation v' w) (_: w' = a :: w): G.NonTerminatedDerivation v w'

def NonTerminatedDerivation.end (d: NonTerminatedDerivation G v w) : G.V :=
  match d with
  | start _ => v
  | cons _ d _ => d.end

def DerivationStep.deconstruct { w: Word _ } { w': Word G.Z } (step: G.DerivationStep w) (h: step.result = (Sum.inr <$> w') * Word.mk [Sum.inl v]):
  { r: G.V × (Word G.Z × G.Z) // .cons r.1 (r.2.2, v) ∈ G.productions ∧ w' = r.2.1 * Word.mk [r.2.2] ∧ w = Sum.inr <$> r.2.1 * Word.mk [Sum.inl r.1] } := by
  sorry

def NonTerminatedDerivation.fromDerivation (d: G.Derivation lhs rhs) (h_rhs: rhs = Sum.inr <$> w * Word.mk [.inl v']) (s: { v: G.V // lhs = [.inl v]})
  : G.NonTerminatedDerivation v' w := by
  cases d
  
  case same =>
    apply start
    have ⟨_, p⟩ := s
    rw [h_rhs, Word.mul_eq_cons] at p
    cases p
    case inr _ h =>
      apply False.elim
      apply h.elim; intro _ ⟨_, h'⟩
      let h' := h'.symm
      rw [<- Word.eps_eq_nil, Word.mul_eq_eps] at h'
      simp [Word.mk, Word.eps_eq_nil] at h'
    case inl h =>
      have ⟨h, _⟩ := h
      rw [Word.map_eq_eps] at h
      assumption

  case step step sound _ =>
    have ⟨v, h1⟩ := s
    sorry

inductive RegularDerivation (G: RegularGrammar α nt): Word G.Z → Type
  | eps (left: G.NonTerminatedDerivation v w) (h: .eps left.end ∈ G.productions) : G.RegularDerivation w
  | alpha (left: G.NonTerminatedDerivation v w) (h: .alpha left.end a ∈ G.productions) (_: w' = w * Word.mk [a]): G.RegularDerivation w'

end RegularGrammar