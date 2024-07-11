import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Tauto
import FormalSystems.Chomsky.ContextFree.DerivationTree

namespace ContextFreeGrammar

structure Path {G : ContextFreeGrammar α nt} (dt : DerivationTree G) where
  current : G.V ⊕ G.Z
  next : Option (Path dt)

end ContextFreeGrammar
