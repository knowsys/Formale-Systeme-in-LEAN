import FormalSystems.Chomsky.ContextFree.ContextFreeGrammar

import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Nat.Cast.Basic

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

inductive RegularDerivation (G: RegularGrammar α nt) : G.V → Word G.Z → Type
| eps (v: G.V) (h: .eps v ∈ G.productions): G.RegularDerivation st ε
| alpha (v: G.V) (a: G.Z) (h: .alpha v a ∈ G.productions): G.RegularDerivation v [a]
| step (v v': G.V) (a: G.Z) (h: .cons v (a, v') ∈ G.productions):
  G.RegularDerivation v' xs → G.RegularDerivation v (a :: xs)

def RegularDerivation.fromDerivation (d: G.Derivation [.inl X] w') (h: Sum.inr <$> w = w'):
  G.RegularDerivation X w := by
  match hd1 : d with
  | .same =>
    cases w <;> simp at h
    rw [List.cons_eq_cons] at h
    have ⟨_, _⟩ := h
    contradiction

  | .step s d' hd =>
    have ⟨_, pre, suf⟩ := s.lhs_singleton
    unfold DerivationStep.result at hd
    match hp:s.prod.val with
    | .eps _ =>
      simp [hp, RegularProduction.rhs_eq_deconstr_rhs, Word.mk, <- Word.eps_eq_nil] at hd
      simp [<-hd, pre, suf] at d'
      cases d'
      . simp at h; rw [Word.eps_eq_nil, List.map_eq_nil] at h
        rw [h]
        apply RegularDerivation.eps
        rw [<- hp]
        exact s.prod.prop
      case step s' _ _ =>
        have contra := s'.sound.symm
        simp [Word.mul_eq_eps] at contra
        have _ := contra.1.2
        contradiction

    | .alpha _ a =>
      simp [hp, RegularProduction.rhs_eq_deconstr_rhs, Word.mk] at hd
      simp [<-hd, pre, suf] at d'
      cases d'
      . simp at h;
        -- Todo: Proof `w = [a]` (using injectivity of Sum.inr),
        -- return [RegularDerivation.alpha]
        sorry
      case step s' _ _ =>
        have contra := s'.sound.symm
        simp [Word.mul_eq_cons] at contra
        apply False.elim
        sorry

    | .cons _ (a, X') =>
      simp [hp, RegularProduction.rhs_eq_deconstr_rhs, pre, suf] at hd
      simp [Word.mk, HMul.hMul, Mul.mul] at hd
      let ⟨_, hw⟩ := d'.cancelLeft hd.symm h.symm
      rw [hw]; apply RegularDerivation.step
      have hp': s.prod.val = .cons X (a, X') := by
        rw [Production.prod_ext]; constructor
        assumption; simp [hp]; rfl
      rw [<- hp']; exact s.prod.prop
      exact RegularDerivation.fromDerivation (d'.cancelLeft hd.symm h.symm).val rfl

termination_by fromDerivation d _ => d.len
decreasing_by fromDerivation =>
  simp [InvImage]
  rw [Grammar.Derivation.cancelLeft_len _]
  simp [Derivation.len]
  apply Nat.lt_succ.mpr
  rfl

end RegularGrammar