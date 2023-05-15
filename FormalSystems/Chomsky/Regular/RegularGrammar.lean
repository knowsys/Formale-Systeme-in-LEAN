import FormalSystems.Chomsky.ContextFree.ContextFreeGrammar

import Mathlib.Data.Finset.Basic

class inductive Production.ContextFree.Regular (prod: Production Z V) [prod.ContextFree] where
  | eps (h: prod.rhs = ε)
  | alpha (rhs: Z) (h: prod.rhs = [.inr rhs])
  | cons (rhs: Z × V) (h: prod.rhs = [.inr rhs.1, .inl rhs.2])

structure RegularGrammar (α: Type _) (nt : Type _) extends ContextFreeGrammar α nt where
  regularity: ∀(p: productions), (context_freedom p).Regular

structure RegularProduction (Z: Finset α) (V: Finset nt) extends ContextFreeProduction Z V where
  regularity: toContextFreeProduction.contextFree.Regular
