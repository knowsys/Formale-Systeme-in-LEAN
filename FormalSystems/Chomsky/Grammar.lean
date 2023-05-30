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

variable { Prod: Finset α → Finset nt → Type } [Production α nt Prod]

structure DerivationStep (G: Grammar Prod) (u: Word (G.V ⊕ G.Z)) where
  prod: G.productions
  pre: Word (G.V ⊕ G.Z)
  suf: Word (G.V ⊕ G.Z)
  sound:
    have x := Production.lhs prod.val
    u = pre * x * suf

variable { G: Grammar Prod } { u: Word (G.V ⊕ G.Z) }

def DerivationStep.concat_left (step: DerivationStep G u) (w: Word (G.V ⊕ G.Z)):
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

theorem DerivationStep.concat_left_result (step: DerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  (step.concat_left w).result = w * step.result := by
  unfold DerivationStep.result
  unfold concat_left
  simp [mul_assoc]

namespace Grammar

variable { G: Grammar Prod } { u: Word (G.V ⊕ G.Z) }

def OneStepDerivationRelation (G: Grammar Prod) (u v: Word (G.V ⊕ G.Z)) : Prop :=
  ∃(step: DerivationStep G u), step.result = v 

notation:40 u:40 " (" G:40 ")⇒ " v:41 => OneStepDerivationRelation G u v

theorem OneStepDerivationRelation.cancel_left (w: Word _) (a: (v (G)⇒ u)):
  (w * v) (G)⇒ (w * u) := by
  have ⟨ step, _ ⟩ := a
  exists step.concat_left w
  rw [step.concat_left_result w]
  simp; assumption

def NStepDerivationRelation (G: Grammar Prod) (u v: Word (G.V ⊕ G.Z)) : ℕ → Prop
  | 0 => u = v
  | Nat.succ n => ∃w, u (G)⇒ w ∧ NStepDerivationRelation G w v n

theorem NStepDerivationRelation.cancel_left (w: Word _) (a: NStepDerivationRelation G v u n):
  NStepDerivationRelation G (w * v) (w * u) n := by
  cases n with
  | zero => unfold NStepDerivationRelation at a; rw [a]; rfl
  | succ n' =>
    have ⟨ v', _, _ ⟩ := a
    exists w * v'; constructor
    . apply OneStepDerivationRelation.cancel_left; assumption
    . apply cancel_left; assumption

theorem NStepDerivationRelation.concat (a: NStepDerivationRelation G v u n) (b: NStepDerivationRelation G u w m) :
  NStepDerivationRelation G v w (n+m) := by
  cases n with
  | zero => 
    unfold NStepDerivationRelation at a
    rw [a, Nat.zero_add]; assumption
  | succ n' => 
    unfold NStepDerivationRelation at a
    have ⟨ w', p, q ⟩ := a
    unfold NStepDerivationRelation; rw [Nat.succ_add]; simp
    exists w'; simp [p]
    exact concat q b

def DerivationRelation (G: Grammar Prod) (u v: Word (G.V ⊕ G.Z)) :=
  ∃n, NStepDerivationRelation G u v n 

notation:40 u:40 " (" G:40 ")⇒* " v:41 => DerivationRelation G u v

namespace DerivationRelation

theorem cancel_left (h: v (G)⇒* u) : (w*v) (G)⇒* w*u := by
  have ⟨ n, _ ⟩ := h
  exists n
  apply NStepDerivationRelation.cancel_left
  assumption

theorem trans (h1: v (G)⇒* u) (h2: u (G)⇒* w) : v (G)⇒* w := by
  have ⟨ n1, _ ⟩ := h1; have ⟨ n2, _ ⟩ := h2
  exists n1 + n2
  apply NStepDerivationRelation.concat
  assumption; assumption

theorem concat_right (v: Word _) (h1: S (G)⇒* w * v) (h2: v (G)⇒* u) : S (G)⇒* w * u := by
  apply DerivationRelation.trans
  . assumption
  . apply cancel_left; assumption

theorem refl (w: Word (G.V ⊕ G.Z)) : w (G)⇒* w := by exists 0

/-
instance preorder (G: Grammar Z V Prod) : Preorder (Word (V ⊕ Z)) where
  le u v := u (G)⇒* v
  le_refl w := DerivationRelation.refl w
  le_trans _ _ _ := DerivationRelation.trans
-/

end DerivationRelation

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
  intro w ⟨ step_len, h ⟩
  sorry

theorem ExampleGrammar.gen_lang_supers : ExampleGrammar.lang ⊆ ExampleGrammar.GeneratedLanguage := by
  intro w ⟨ b, bz, hb, hz, wbz ⟩
  have : b = [⟨'b', _ ⟩] := hb
  rw [wbz, this, Set.mem_def, Grammar.GeneratedLanguage, Word.map_append _ _ _]
  apply Grammar.DerivationRelation.concat_right [ .inl ⟨ 'A', by simp ⟩ ]
  . have step: DerivationStep ExampleGrammar [Sum.inl ExampleGrammar.start] := { 
      prod := ⟨ ExampleProductions[0], by simp [ExampleGrammar] ⟩,
      pre := ε, suf := ε,
      sound := by simp [Word.epsilon]
    }
    exists 1; exists Production.rhs step.prod.val; constructor
    . exact ⟨ step, by unfold DerivationStep.result; sorry ⟩
    . unfold NStepDerivationRelation; simp [HMul.hMul, Mul.mul]
      sorry
  . sorry

theorem ExampleGrammar.gen_lang : ExampleGrammar.GeneratedLanguage = ExampleGrammar.lang := by
  apply Set.eq_of_subset_of_subset
  . exact gen_lang_subs
  . exact gen_lang_supers

end Grammar