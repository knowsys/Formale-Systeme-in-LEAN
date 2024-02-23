import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor

/--Structure: A context free production over a set of terminal symbols Z and non-terminal symbols V
  has a single variable as its left-hand side (`lhs`) and any string as its right-hand side (`rhs`).-/
structure ContextFreeProduction (Z: Finset α) (V: Finset nt) where
  /--Left-hand side: A single variable.-/
  lhs: V
  /--Right-hand side: Any string.-/
  rhs: Word (V ⊕ Z)

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

variable [i: Production.ContextFree α nt P] { G: Grammar P }

open Word

/--Theorem: Derivation steps in context free grammars that start in the string
  lhs, with lhs = a : : xs, where a is a terminal symbol,
  have the symbol a as the leftmost symbol of
  the`pre`attribute also.
  -/
theorem ContextFreeGrammar.derivation_step_prefix
  { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (step: G.DerivationStep lhs) (h_lhs: lhs = (.inr a :: xs)):
  step.pre = .inr a :: step.pre.tail := by
  have sound := step.sound
  simp_rw [Production.ContextFree.lhs_eq_lhs step.prod.val, h_lhs] at sound
  match hpre:step.pre with
  | [] =>
    simp_rw [hpre, HMul.hMul, Mul.mul] at sound
    simp at sound
    rw [List.cons_eq_cons] at sound
    let ⟨_, _⟩ := sound
    contradiction

  | x :: pres => 
    simp_rw [hpre, HMul.hMul, Mul.mul] at sound
    simp at sound; rw [List.cons_eq_cons] at sound
    simp [sound.left]

/--Theorem: Given a derivation in a context free grammar of the form

  `a::xs (G)=>* w`,

  where a is a terminal symbol and w is a string of terminal symbols,
  we know that a is the first symbol of w also, i.e.
  `a::xs (G)=>* a::[rest of w]`.-/
theorem ContextFreeGrammar.derivation_preserves_prefix
  { w: Word G.Z } { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (d: G.Derivation lhs rhs) (h_lhs: lhs = (.inr a :: xs)) (h_rhs: rhs = (.inr <$> w)):
  w = a :: w.tail := by
  match d with
  | .same h =>
    rw [<- h, h_lhs] at h_rhs
    cases w
    simp [List.map_nil] at h_rhs
    simp [List.map_cons] at h_rhs
    rw [List.cons_eq_cons] at h_rhs
    have _ := (Sum.inr_injective h_rhs.left).symm
    simp; rw [List.cons_eq_cons]
    simp; assumption

  | .step s d r =>
    unfold Grammar.DerivationStep.result at r
    rw [ContextFreeGrammar.derivation_step_prefix s h_lhs] at r
    simp_rw [HMul.hMul, Mul.mul] at r
    simp at r
    let h_lhs' := r.symm
    exact ContextFreeGrammar.derivation_preserves_prefix d h_lhs' h_rhs

/---/
def Grammar.DerivationStep.cancelLeft
  { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (d: G.DerivationStep lhs) (h_lhs: lhs = (.inr a :: xs)):
  { d': G.DerivationStep xs // d'.result = d.result.tail } where
  val := { d with
    pre := d.pre.tail
    sound := by
      simp
      have hxs : xs = lhs.tail := by simp [h_lhs]
      simp [hxs, HMul.hMul, Mul.mul]
      rw [<- List.tail_append_of_ne_nil]
      congr
      have sound := d.sound
      simp [HMul.hMul, Mul.mul] at sound
      assumption
      rw [ContextFreeGrammar.derivation_step_prefix d h_lhs]
      simp
  }
  property := by
    simp [result, HMul.hMul, Mul.mul]
    rw [<- List.tail_append_of_ne_nil]
    rw [ContextFreeGrammar.derivation_step_prefix d h_lhs]
    simp

open Grammar

def Grammar.Derivation.cancelLeft
  { w: Word G.Z } { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (d: G.Derivation lhs rhs) (h_lhs: lhs = (.inr a :: xs)) (h_rhs: rhs = (.inr <$> w)):
  G.Derivation xs (.inr <$> w.tail) := by
  match d with
  | .same h =>
    apply Derivation.same
    rw [<- h, h_lhs] at h_rhs
    cases w
    contradiction
    simp at h_rhs
    rw [List.cons_eq_cons] at h_rhs
    simp [h_rhs.2]
  | .step s d r =>
    let ⟨s', r'⟩ := s.cancelLeft h_lhs
    rw [r] at r'
    apply Derivation.step (u' := s'.result)
    swap; rfl
    apply d.cancelLeft
    rw [r', <-r]
    simp [DerivationStep.result, HMul.hMul, Mul.mul]
    rw [ContextFreeGrammar.derivation_step_prefix s _]
    simp; rfl; pick_goal 3
    exact h_lhs
    assumption

theorem Grammar.Derivation.cancelLeft_len_same
  { w: Word G.Z } { h_rhs: _ }:
  (cancelLeft (w := w) (.same h) h_lhs h_rhs).len = 0 := by
  simp [cancelLeft]
  unfold len
  rfl

theorem Grammar.Derivation.cancelLeft_len
  (d: G.Derivation lhs rhs):
  (d.cancelLeft h_lhs h_rhs).len = d.len := by
  match d with
  | .same _ => simp [len]
  | .step _ _ _ =>
    simp [len]
    apply cancelLeft_len
