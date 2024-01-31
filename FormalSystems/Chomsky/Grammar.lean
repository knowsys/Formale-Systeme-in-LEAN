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


theorem DerivationStep.lhs_singleton (step: DerivationStep G [.inl v]) :
  (Production.lhs step.prod.val) = [.inl v] ∧ step.pre = ε ∧ step.suf = ε := by
  match hpre:step.pre with
  | .cons _ _ =>
    have tmp := Eq.symm $ hpre ▸ step.sound
    simp [mul_assoc, HMul.hMul, Mul.mul, List.cons_append] at tmp
    rw [List.cons_eq_cons] at tmp
    simp_rw [List.append_eq_nil] at tmp
    have tmp := tmp.2.2.1
    have ⟨_, h⟩ := Production.lhs_contains_var step.prod.val
    rw [tmp] at h
    contradiction

  | .nil =>
    have tmp := Eq.symm $ hpre ▸ step.sound
    simp [<- Word.eps_eq_nil, Word.mul_eq_cons] at tmp
    cases tmp

    case inl h =>
      have ⟨_, c⟩ := Production.lhs_contains_var step.prod.val
      have ⟨h, _⟩ := h
      rw [h] at c
      contradiction

    case inr h =>
      have ⟨_, ⟨h₁, h₂⟩ ⟩ := h
      have tmp := Word.mul_eq_eps.mp $ Eq.symm h₂
      have tmp' := tmp.1 ▸ h₁
      simp at tmp'
      constructor
      . assumption
      . constructor; rfl; exact tmp.right

inductive Derivation (G: Grammar Prod) : Word (G.V ⊕ G.Z) → Word (G.V ⊕ G.Z) → Type
| same {u v: Word (G.V ⊕ G.Z)} (h: u = v) : G.Derivation u v
| step
  {u u' v: Word (G.V ⊕ G.Z)}
  (step: G.DerivationStep u)
  (_: Derivation G u' v)
  (sound: step.result = u') :
  Derivation G u v

class DerivationCls (G: Grammar Prod) (t: Type) where
  start: Word (G.V ⊕ G.Z)
  result: Word (G.V ⊕ G.Z)

instance : DerivationCls G (G.Derivation a b) where
  start := a
  result := b

notation:40 u:40 " (" G:40 ")⇒* " v:41 => (Nonempty $ Derivation G u v)

def Derivation.len { u w: Word (G.V ⊕ G.Z) }: G.Derivation u w → Nat
| same _ => 0
| step _ d _ => Nat.succ d.len

namespace Derivation

theorem augment_left {u v w: Word _} (d: G.Derivation u v) :
  G.Derivation (w * u) (w * v) := by
  induction d with
  | same h => apply same; simp [h]
  | step s _ sound =>
    apply step
    . assumption
    swap
    . exact s.augment_left w
    . rw [<- sound]; exact s.augment_left_result _

def augment_left_cons {u v: Word _} (d: G.Derivation u v) :
  G.Derivation (w :: u) (w :: v) := by
  match d with
  | same h => apply same; simp [h]
  | step s d' sound =>
    apply step
    . exact d'.augment_left_cons
    swap
    . exact s.augment_left [w]
    . rw [<- sound]; exact s.augment_left_result _

theorem trans {u v w: Word _} (d1: G.Derivation u v) (d2: G.Derivation v w) : G.Derivation u w := by
  induction d1 with
  | same h => exact h ▸ d2
  | step l _ sound ih => exact step l (ih d2) sound

end Derivation

instance DerivationRelation.preorder (G: Grammar Prod) : Preorder (Word (G.V ⊕ G.Z)) where
  le u v := u (G)⇒* v
  le_refl w := Nonempty.intro $ Derivation.same rfl
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

-- TODO: a proof for ExampleGrammar.GeneratedLanguage = ExampleGrammar.lang
-- see lecture 2, slides 18 - 21

end Grammar
