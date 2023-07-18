import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs

import FormalSystems.Preliminaries.Language

variable { α: Type } { nt: Type } { Z: Finset α } { V: Finset nt }

class Production (α: Type) (nt: Type) (P: Finset α → Finset nt → Type) where
  lhs { Z: Finset α } { V: Finset nt } (p: P Z V) : Word (V ⊕ Z)
  rhs { Z: Finset α } { V: Finset nt } (p: P Z V) : Word (V ⊕ Z)
  lhs_contains_var { Z: Finset α } { V: Finset nt } (p: P Z V) : ∃v : V, .inl v ∈ lhs p
  prod_ext { Z: Finset α } { V: Finset nt } (p₁ p₂: P Z V) :
    p₁ = p₂ ↔ lhs p₁ = lhs p₂ ∧ rhs p₁ = rhs p₂

structure GenericProduction (Z: Finset α) (V: Finset nt) where
  lhs: Word (V ⊕ Z)
  rhs: Word (V ⊕ Z)
  lhs_contains_var: ∃v : V, .inl v ∈ lhs

@[simp] theorem GenericProduction.eq_iff_lhs_and_rhs_eq (p₁ p₂ : GenericProduction Z V) :
  p₁ = p₂ ↔ p₁.lhs = p₂.lhs ∧ p₁.rhs = p₂.rhs := by
  constructor
  . intro h; rw [h]; exact ⟨ rfl, rfl ⟩
  . intro ⟨ h₁, h₂ ⟩
    match p₁ with
    | ⟨ l, r, _ ⟩ => simp at h₁; simp at h₂; simp_rw [h₁, h₂]

instance : Production α nt GenericProduction where
  lhs := (·.lhs)
  rhs := (·.rhs)
  lhs_contains_var := (·.lhs_contains_var)
  prod_ext := GenericProduction.eq_iff_lhs_and_rhs_eq

def Production.fromEmbedding (emb: ∀ Z V, ProductionType Z V ↪ GenericProduction Z V) : Production α nt ProductionType where
  lhs := lhs ∘ (emb _ _).toFun
  rhs := rhs ∘ (emb _ _).toFun
  lhs_contains_var p := lhs_contains_var $ (emb _ _).toFun p
  prod_ext p₁ p₂ := by
    constructor
    . intro h; rw [h]; exact ⟨ rfl, rfl ⟩
    . simp; intro hl hr
      apply (emb _ _).inj'; apply (GenericProduction.eq_iff_lhs_and_rhs_eq _ _).mpr
      simp; exact ⟨ hl, hr ⟩

notation:40 v:40 " →ₚ " u:40 => GenericProduction.mk v u

instance [DecidableEq (Z: Finset α)] [DecidableEq (V: Finset nt)] : DecidableEq (GenericProduction Z V) :=
  fun a b => decidable_of_decidable_of_iff (Iff.symm (Production.prod_ext a b))

structure Grammar (Prod: Finset α → Finset nt → Type) [Production α nt Prod] where
  Z: Finset α
  V: Finset nt
  start: V
  productions: Finset (Prod Z V)

namespace Grammar

variable { Prod: Finset α → Finset nt → Type } [Production α nt Prod]

structure DerivationStep (G: Grammar Prod) (u: Word (G.V ⊕ G.Z)) where
  prod: G.productions
  pre: Word (G.V ⊕ G.Z)
  suf: Word (G.V ⊕ G.Z)
  sound:
    have x := Production.lhs prod.val
    u = pre * x * suf

variable { G: Grammar Prod } { u: Word (G.V ⊕ G.Z) }

def DerivationStep.augment_left (step: DerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  DerivationStep G (w * u) :=
  { 
    prod := step.prod, 
    pre := w * step.pre, 
    suf := step.suf, 
    sound := by 
      simp [mul_assoc]
      have t := step.sound
      simp [mul_assoc] at t
      exact t
  }

def DerivationStep.result (step: DerivationStep G u) : Word (G.V ⊕ G.Z) :=
  step.pre * Production.rhs step.prod.val * step.suf

theorem DerivationStep.augment_left_result (step: DerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  (step.augment_left w).result = w * step.result := by
  unfold DerivationStep.result
  unfold augment_left
  simp [mul_assoc]

def DerivationStep.fromRule (p: G.productions) : DerivationStep G (Production.lhs (p.val)) where
  prod := p
  pre := ε
  suf := ε
  sound := by simp [Word.epsilon]

theorem DerivationStep.from_rule_result { p: G.productions } :
  (DerivationStep.fromRule p).result = (Production.rhs (p.val)) := by
  simp [result, DerivationStep.fromRule, Word.epsilon]

inductive Derivation (G: Grammar Prod) : Word (G.V ⊕ G.Z) → Word (G.V ⊕ G.Z) → Type
| same {u: Word (G.V ⊕ G.Z)} : G.Derivation u u
| step
  {u u' v: Word (G.V ⊕ G.Z)}
  (step: G.DerivationStep u)
  (_: Derivation G u' v)
  (sound: step.result = u') :
  Derivation G u v

notation:40 u:40 " (" G:40 ")⇒* " v:41 => (Nonempty $ Derivation G u v)

namespace Derivation

theorem augment_left {u v w: Word _} (d: G.Derivation u v) :
  G.Derivation (w * u) (w * v) := by
  induction d with
  | same => exact same
  | step s _ sound => 
    apply step
    . assumption
    swap
    . exact s.augment_left w
    . rw [<- sound]; exact s.augment_left_result _

def augment_left_cons {u v: Word _} (d: G.Derivation u v) :
  G.Derivation (w :: u) (w :: v) := by
  match d with
  | same => exact same
  | step s d' sound =>
    apply step
    . exact d'.augment_left_cons
    swap
    . exact s.augment_left [w]
    . rw [<- sound]; exact s.augment_left_result _

theorem trans {u v w: Word _} (d1: G.Derivation u v) (d2: G.Derivation v w) : G.Derivation u w := by
  induction d1 with
  | same => exact d2
  | step l _ sound ih => exact step l (ih d2) sound

end Derivation

instance DerivationRelation.preorder (G: Grammar Prod) : Preorder (Word (G.V ⊕ G.Z)) where
  le u v := u (G)⇒* v
  le_refl w := Nonempty.intro Derivation.same
  le_trans _ _ _ := by
    intro ⟨d₁⟩ ⟨d₂⟩
    apply Nonempty.intro
    exact d₁.trans d₂

def GeneratedLanguage (G: Grammar Prod) : Language G.Z :=
  fun w => [.inl ↑G.start] (G)⇒* (.inr <$> w)

def ExampleProductions : List (GenericProduction { 'b', 'z' } { 'A', 'B', 'S', 'Z' }) := [
    -- rule S -> BA
    ([ .inl ⟨ 'S', by simp ⟩ ] →ₚ [ .inl ⟨ 'B', by simp ⟩, .inl ⟨ 'A', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'S', _ ⟩ , List.Mem.head _ ⟩,
    -- rule A -> BA
    ([ .inl ⟨ 'A', by simp ⟩ ] →ₚ [ .inl ⟨ 'B', by simp ⟩, .inl ⟨ 'A', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'A', _ ⟩ , List.Mem.head _ ⟩,
    -- rule A -> ZA
    ([ .inl ⟨ 'A', by simp ⟩ ] →ₚ [ .inl ⟨ 'Z', by simp ⟩, .inl ⟨ 'A', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'A', _ ⟩ , List.Mem.head _ ⟩,
    -- rule A -> ε
    ([ .inl ⟨ 'A', by simp ⟩ ] →ₚ [ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'A', _ ⟩ , List.Mem.head _ ⟩,
    -- rule B -> b
    ([ .inl ⟨ 'B', by simp ⟩ ] →ₚ [ .inr ⟨ 'b', by simp ⟩  ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'B', _ ⟩ , List.Mem.head _ ⟩,
    -- rule X -> z
    ([ .inl ⟨ 'Z', by simp ⟩ ] →ₚ [ .inr ⟨ 'z', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'Z', _ ⟩ , List.Mem.head _ ⟩
]

def ExampleGrammar: @Grammar Char Char GenericProduction _ where
  Z := { 'b', 'z' }
  V := { 'A', 'B', 'S', 'Z' } 
  start := ⟨ 'S', by simp ⟩
  productions := ⟨ ExampleProductions, by simp ⟩ 

theorem ExampleGrammar.productions_eq_ex_productions (p: GenericProduction _ _):
  p ∈ ExampleGrammar.productions ↔ p ∈ ExampleProductions := by
  simp [ExampleGrammar]

def ExampleGrammar.lang: Language ({ 'b', 'z' } : Finset _) := 
  { [⟨ 'b', by simp ⟩] } ∘ₗ { [⟨ 'b', by simp ⟩], [⟨ 'z', by simp ⟩] }∗

theorem ExampleGrammar.gen_lang_subs : ExampleGrammar.GeneratedLanguage ⊆ ExampleGrammar.lang := by
  sorry

theorem ExampleGrammar.gen_lang_supers : ExampleGrammar.lang ⊆ ExampleGrammar.GeneratedLanguage := by
  sorry

theorem ExampleGrammar.gen_lang : ExampleGrammar.GeneratedLanguage = ExampleGrammar.lang := by
  apply Set.eq_of_subset_of_subset
  . exact gen_lang_subs
  . exact gen_lang_supers

end Grammar