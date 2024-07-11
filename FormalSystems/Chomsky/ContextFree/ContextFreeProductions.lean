import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Tauto
--=============================================================
-- Section: Context Free Productions
--=============================================================

/--Structure: A context free production over a set of terminal symbols Z and non-terminal symbols V
  has a single variable as its left-hand side (`lhs`) and any string as its right-hand side (`rhs`).-/
structure ContextFreeProduction (Z: Finset α) (V: Finset nt) where
  /--Left-hand side: A single variable.-/
  lhs: V
  /--Right-hand side: Any string.-/
  rhs: Word (V ⊕ Z)

/--Define the equality determinating relation.-/
def ContextFreeProduction.decEq {Z: Finset α} {V: Finset nt} [DecidableEq α] [DecidableEq nt] : (CFP₁ CFP₂ : ContextFreeProduction Z V) → Decidable (Eq CFP₁ CFP₂) :=
  fun (CFP₁ : (ContextFreeProduction Z V)) (CFP₂ : (ContextFreeProduction Z V)) =>
  by
    by_cases CFP₁.lhs = CFP₂.lhs
    case pos h_pos₁ =>
      by_cases CFP₁.rhs = CFP₂.rhs
      case pos h_pos₂ =>
        exact isTrue (by
          have h_CFP₂ : CFP₂ = (ContextFreeProduction.mk CFP₁.lhs CFP₁.rhs) :=
            by rw [h_pos₁, h_pos₂]
          rw [h_CFP₂])
      case neg h_neg₂ =>
        exact isFalse (by
          have h_CFP₁ : CFP₁ = (ContextFreeProduction.mk CFP₁.lhs CFP₁.rhs) := by simp
          have h_CFP₂ : CFP₂ = (ContextFreeProduction.mk CFP₂.lhs CFP₂.rhs) := by simp
          rw [h_CFP₁,h_CFP₂]
          simp
          intro _
          exact h_neg₂
        )
    case neg h_neg₁ =>
      exact isFalse (by
        have h_CFP₁ : CFP₁ = (ContextFreeProduction.mk CFP₁.lhs CFP₁.rhs) := by simp
        have h_CFP₂ : CFP₂ = (ContextFreeProduction.mk CFP₂.lhs CFP₂.rhs) := by simp
        rw [h_CFP₁,h_CFP₂]
        simp
        intro h_lhs
        contradiction)


/--Equality is decidable for PDTs using the decEq function.-/
instance [a : DecidableEq α] [b : DecidableEq nt] : DecidableEq (@ContextFreeProduction α nt Z V) := @ContextFreeProduction.decEq α nt Z V a b

/--Shorthand for goes to ε productions.-/
def ContextFreeProduction.isEps (cfp : (ContextFreeProduction Z V)) : Prop :=
  cfp.rhs = Word.epsilon

/--Coercion (upcast) of context free productions into generic productions.
  Changes necessary: Inserting the single variable into a "string" (actually list).-/
instance : Coe (ContextFreeProduction Z V) (GenericProduction Z V) where
  coe p := {
    lhs := [.inl p.lhs],
    rhs := p.rhs,
    lhs_contains_var := ⟨ p.lhs, List.Mem.head _ ⟩
  }

/--Define an embedding of context free productions into generic productions.-/
def ContextFreeProduction.toProduction : ContextFreeProduction Z V ↪ GenericProduction Z V where
  toFun := Coe.coe  --  Provide function aspect
  inj' := by        --  Prove injectivity
    intro p₁ p₂; simp [Coe.coe]; intro h1 h2
    rw [List.cons_eq_cons] at h1; simp at h1
    match p₁ with
    | ⟨l, r⟩ => simp at h1; simp at h2; simp_rw [h1, h2]

/--Context free productions are instances of productions.-/
instance : Production α nt ContextFreeProduction :=
  -- instance can be proved either with witnesses in "where" or with an embedding
  Production.fromEmbedding (fun _ _ => ContextFreeProduction.toProduction)
  -- works by turning embedding of context free in generic productions more general

/--Class: The class of context free productions is such, that they are a subclass of productions (the class)
  with two new attributes:

  - `lhs_var` - The variable on the left-hand side of the production rule (possibly a function???)

  - `lhs_eq_lhs`  - A lemma that tells us, that the left-hand side of a production (`lhs`)
      is the left-hand side variable (`lhs_vr`) (in string form).-/
class Production.ContextFree (α: Type) (nt: Type) (P: Finset α → Finset nt → Type)
extends Production α nt P where
  lhs_var: P Z V → V
  lhs_eq_lhs: ∀(p: P Z V), lhs p = [Sum.inl $ lhs_var p]

/--The subclass of context free productions (class) is an instance of a context free productions (the structure).
  Show this by defining/proving lhs_var and lhs_eq_lhs _ correctly.-/
instance : Production.ContextFree α nt ContextFreeProduction where
  lhs_var p := p.lhs
  lhs_eq_lhs _ := by rfl

/--Allow for →ₚ₂ notation to construct contex-free productions. Go from a word over V ⊕ Z to another word over V ⊕ Z.
  Still require a proof for variable-existence on the left side right after this rule.

  Note: This notation is also used in `Mathlib.Data.DFinsupp.Basic`. You currently cannot use both modules at the same time.-/
notation:40 v:40 " →ₚ₂ " u:40 => ContextFreeProduction.mk v u
