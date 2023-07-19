import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor

structure ContextFreeProduction (Z: Finset α) (V: Finset nt) where
  lhs: V
  rhs: Word (V ⊕ Z)

instance : Coe (ContextFreeProduction Z V) (GenericProduction Z V) where
  coe p := {
    lhs := [.inl p.lhs],
    rhs := p.rhs,
    lhs_contains_var := ⟨ p.lhs, List.Mem.head _ ⟩
  }

def ContextFreeProduction.toProduction : ContextFreeProduction Z V ↪ GenericProduction Z V where
  toFun := Coe.coe
  inj' := by
    intro p₁ p₂; simp [Coe.coe]; intro h1 h2
    rw [List.cons_eq_cons] at h1; simp at h1
    match p₁ with
    | ⟨l, r⟩ => simp at h1; simp at h2; simp_rw [h1, h2]

instance : Production α nt ContextFreeProduction :=
  Production.fromEmbedding (fun _ _ => ContextFreeProduction.toProduction)

def ContextFreeGrammar (α nt: Type) := @Grammar α nt ContextFreeProduction _

instance : Coe (ContextFreeGrammar α nt) (@Grammar α nt GenericProduction _) where
  coe g := {
    Z := g.Z,
    V := g.V,
    start := g.start,
    productions := g.productions.map ContextFreeProduction.toProduction
  }

class Production.ContextFree (α: Type) (nt: Type) (P: Finset α → Finset nt → Type) [Production α nt P] where
  lhs: P Z V → V
  lhs_eq_lhs: ∀(p: P Z V), Production.lhs p = [Sum.inl $ lhs p]

instance : Production.ContextFree α nt ContextFreeProduction where
  lhs p := p.lhs
  lhs_eq_lhs _ := by rfl

variable [Production α nt P] { G: Grammar P } [Production.ContextFree α nt P]

def Grammar.Derivation.cancelLeft
  { w: Word G.Z } { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (d: G.Derivation lhs rhs) (h_lhs: lhs = (.inr a :: xs)) (h_rhs: rhs = (.inr <$> w)):
  { d: G.Derivation xs (.inr <$> w.tail) // w = a :: w.tail } := by
  sorry

theorem Grammar.Derivation.cancelLeft_len
  { w: Word G.Z } { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (d: G.Derivation lhs rhs) {h_lhs: lhs = (.inr a :: xs)} {h_rhs: rhs = (.inr <$> w)}:
  (d.cancelLeft h_lhs h_rhs).val.len = d.len := by
  sorry
