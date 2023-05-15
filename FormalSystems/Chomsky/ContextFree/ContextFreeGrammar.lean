import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor

class Production.ContextFree (prod: Production (Z: Finset α) (V: Finset nt)) where
  lhs_var: V
  lhs_eq_lhs_var: prod.lhs = [.inl lhs_var]

structure ContextFreeProduction (Z: Finset α) (V: Finset nt) extends Production Z V where
  lhs_var: V
  lhs_eq_lhs_var: lhs = [.inl lhs_var]

instance : Coe (ContextFreeProduction Z V) (Production Z V) where
  coe cf := cf.toProduction

instance ContextFreeProduction.contextFree (cf: ContextFreeProduction Z V) : Production.ContextFree cf.toProduction where
  lhs_var := cf.lhs_var
  lhs_eq_lhs_var := cf.lhs_eq_lhs_var

structure ContextFreeGrammar (α: Type _) (nt: Type _) extends Grammar α nt where
  context_freedom: ∀(p : productions), p.val.ContextFree

class Grammar.ContextFree (G: Grammar α nt) where
  context_freedom: ∀(p: G.productions), p.val.ContextFree 

instance (G: ContextFreeGrammar α nt) : G.ContextFree where
  context_freedom := G.context_freedom

structure EpsilonFreeContextFreeGrammar (α: Type _) (nt: Type _) extends ContextFreeGrammar α nt where
  rhs_no_start: ∀(p: productions), .inl start ∉ p.val.rhs
  rhs_not_eps: ∀(p: productions), p.val.lhs = [.inl start] ∨ p.val.rhs ≠ ε

def ContextFreeGrammar.toEpsilonFree (G: ContextFreeGrammar α nt): EpsilonFreeContextFreeGrammar α (nt ⊕ Unit) := {
  V := Finset.cons (.inr ()) (G.V.map .inl) (by simp),
  Z := G.Z,
  start := ⟨ .inr (), by simp ⟩,
  productions := sorry,
  context_freedom := sorry,
  rhs_no_start := sorry,
  rhs_not_eps := sorry
}
