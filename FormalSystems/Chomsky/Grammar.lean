import Mathlib.Data.Finset.Basic

import FormalSystems.Preliminaries.Language

structure Production (α: Type _) (V: Finset nt) where
  lhs: Word (V ⊕ α)
  rhs: Word (V ⊕ α)
  lhs_contains_var: ∃v : V, .inl v ∈ lhs

structure Grammar (α: Type _) (nt : Type _) where
  V: Finset nt
  start: V
  productions: Finset (Production α V)

structure DerivationStep (α : Type _) (G: Grammar α nt) (u: Word (G.V ⊕ α)) where
  prod: G.productions
  pre: Word (G.V ⊕ α)
  suf: Word (G.V ⊕ α)
  sound:
    have x := (↑prod : Production α G.V).lhs
    u = pre * x * suf

def DerivationStep.production (step: DerivationStep α G u): Production α G.V :=
  step.prod

def DerivationStep.result (step: DerivationStep α G u) : Word (G.V ⊕ α) :=
  step.pre * step.production.rhs * step.suf

namespace Grammar

def OneStepDerivationRelation { G: Grammar α nt } (u v: Word (G.V ⊕ α)) :=
  ∃(step: DerivationStep _ _ u), step.result = v 

notation:40 u:40 " ᴳ⇒ " v:41 => OneStepDerivationRelation u v

def NStepDerivationRelation { G: Grammar α nt } (u v: Word (G.V ⊕ α)) : ℕ → Prop
  | 0 => u = v
  | Nat.succ n => ∃w, u ᴳ⇒ w ∧ NStepDerivationRelation w v n

def DerivationRelation { G: Grammar α nt } (u v: Word (G.V ⊕ α)) :=
  ∃n, NStepDerivationRelation u v n 

notation:40 u:40 " ᴳ⇒* " v:41 => DerivationRelation u v

def GeneratedLanguage (G: Grammar α nt) : Language α :=
  fun w => [.inl ↑G.start] ᴳ⇒* (.inr <$> w)

end Grammar