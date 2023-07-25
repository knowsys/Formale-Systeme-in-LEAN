import FormalSystems.Chomsky.ContextFree.ContextFreeGrammar

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Lex

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

def RegularProduction.getRhs (p: RegularProduction Z V) : Option Z × Option V :=
  match p with
  | cons _ ⟨a, X⟩ => (.some a, .some X)
  | alpha _ a => (.some a, .none)
  | eps _ => (.none, .none)

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

instance : Production.ContextFree α nt RegularProduction where
  lhs p := p.lhs
  lhs_eq_lhs _ := by rfl

theorem RegularProduction.rhs_eq_deconstr_rhs (p: RegularProduction Z V):
  Production.rhs p =
    Word.mk (Sum.inr <$> p.getRhs.1.toList) *
    Word.mk (Sum.inl <$> p.getRhs.2.toList) := by
  cases p <;> rfl

theorem RegularProduction.lhs_eq_production_lhs { p: RegularProduction Z V }:
  Production.lhs p = [.inl p.lhs] := by rfl

def RegularGrammar (α nt: Type) := @Grammar α nt RegularProduction _

instance : Coe (RegularGrammar α nt) (ContextFreeGrammar α nt) where
  coe g := { g with
    productions := g.productions.map RegularProduction.toContextFree
  }

instance : Coe (RegularGrammar α nt) (@Grammar α nt GenericProduction _) where
  coe g := { g with
    productions := g.productions.map RegularProduction.toProduction
  }

variable { G: RegularGrammar α nt } { p: G.productions } { v v': G.V }

open Grammar

theorem RegularProduction.eps_step_result:
  p.val = RegularProduction.eps v → (DerivationStep.fromRule p).result = ε := by
  intro h; simp [DerivationStep.fromRule, DerivationStep.result, h]; rfl

theorem RegularProduction.cons_step_result:
  p.val = .cons v (w, b) → (DerivationStep.fromRule p).result = [.inr w, .inl b] := by
  intro h; simp [DerivationStep.fromRule, DerivationStep.result, h]; rfl

namespace RegularGrammar

inductive RegularDerivation (G: RegularGrammar α nt): (v: G.V) → (w: Word G.Z) → Type
| eps (v: _) (h_v: .eps v ∈ G.productions) (h_w: w = ε):
  G.RegularDerivation v w
| alpha (v: _) (h_v: .alpha v a ∈ G.productions) (h_w: w = [a]):
  G.RegularDerivation v w
| step (v v': _) (h: .cons v (a, v') ∈ G.productions) (h_w: w = (a :: w')):
  G.RegularDerivation v' w' → G.RegularDerivation v w

mutual

def RegularDerivation.fromDerivation
  (derivation: G.Derivation [.inl X] w')
  (h: Sum.inr <$> w = w'):
  G.RegularDerivation X w := by
  match derivation with
  | .same h_same =>
    cases w <;> simp [<- h_same] at h
    rw [List.cons_eq_cons] at h
    have ⟨_, _⟩ := h
    contradiction

  | .step s d' hd =>
    apply fromStep
    repeat assumption

def RegularDerivation.fromStep
  (step: G.DerivationStep [.inl X])
  (derivation: G.Derivation u w')
  (h_u: step.result = u)
  (h_w: Sum.inr <$> w = w'):
  G.RegularDerivation X w := by
  have ⟨left, pre, suf⟩ := step.lhs_singleton
  unfold DerivationStep.result at h_u
  match hp:step.prod.val with
  | .eps _ =>
    apply RegularDerivation.eps

    . rw [hp,
        RegularProduction.lhs_eq_production_lhs,
        List.cons_eq_cons]
        at left
      simp [RegularProduction.lhs] at left
      rw [<- left, <- hp]
      exact step.prod.prop

    . simp [hp, RegularProduction.rhs_eq_deconstr_rhs,
        Word.mk, <- Word.eps_eq_nil] at h_u
      simp [<-h_u, pre, suf] at derivation
      cases derivation
      case same h_same =>
        rw [<- h_same, Word.eps_eq_nil, List.map_eq_map, List.map_eq_nil] at h_w
        rw [h_w]
        rfl
      case step s' _ _ =>
        have contra := s'.sound.symm
        simp [Word.mul_eq_eps] at contra
        have _ := contra.1.2
        contradiction

  | .alpha _ a =>
    apply RegularDerivation.alpha

    . rw [hp,
        RegularProduction.lhs_eq_production_lhs,
        List.cons_eq_cons]
        at left
      simp [RegularProduction.lhs] at left
      rw [<- left, <- hp]
      exact step.prod.prop

    . simp [hp, RegularProduction.rhs_eq_deconstr_rhs, Word.mk] at h_u
      simp [<-h_u, pre, suf] at derivation
      cases derivation

      case same h_same =>
        simp [HMul.hMul, Mul.mul] at h_same
        rw [<- h_same] at h_w
        cases w
        contradiction
        simp [List.map_cons] at h_w
        have ⟨h1, h2⟩ := List.cons_eq_cons.mp h_w
        simp [Sum.inr_injective] at h1
        simp [List.map_eq_nil] at h2
        rw [h1, h2]

      case step s' _ _ =>
        apply False.elim
        have contra := s'.sound.symm
        rw [RegularProduction.lhs_eq_production_lhs] at contra
        simp [HMul.hMul, Mul.mul] at contra
        rw [List.append_eq_cons] at contra
        cases contra
        case inl h =>
          have ⟨_, h⟩ := h
          simp at h
        case inr h =>
          have ⟨_, h⟩ := h
          simp at h

  | .cons _ (a, X') =>
    simp [hp, RegularProduction.rhs_eq_deconstr_rhs, pre, suf] at h_u
    simp [Word.mk, HMul.hMul, Mul.mul] at h_u

    apply RegularDerivation.step
    . have : step.prod.val = .cons X (a, X') := by
        rw [Production.prod_ext]; constructor
        assumption; simp [hp]; rfl
      rw [<- this]; exact step.prod.prop

    . apply ContextFreeGrammar.derivation_preserves_prefix derivation
      exact h_u.symm
      exact h_w.symm

    . apply RegularDerivation.fromDerivation
      exact derivation.cancelLeft h_u.symm h_w.symm
      rfl

end

termination_by
  fromDerivation d _ => (d.len, 0)
  fromStep _ d _ _ => (d.len, 1)

decreasing_by
  fromDerivation =>
    simp [InvImage]
    simp [Derivation.len]
    simp_rw [Derivation.cancelLeft_len _]
    apply (Prod.Lex.lt_iff _ _).mpr
    simp

end RegularGrammar