import FormalSystems.Chomsky.Grammar

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