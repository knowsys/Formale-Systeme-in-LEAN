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

namespace Grammar

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
    rw [mul_assoc, <- Word.cons_eq, Word.cons_mul, List.cons_eq_cons] at tmp
    have ⟨_, tmp⟩ := tmp
    simp_rw [<- Word.eps_eq_nil] at tmp
    have ⟨_, tmp⟩ := Word.mul_eq_eps.mp tmp
    have ⟨tmp, _⟩ := Word.mul_eq_eps.mp tmp
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

inductive Derivation (G: Grammar Prod) : Word (G.V ⊕ G.Z) → Type
| same (u: Word _) : G.Derivation u
| step
  { u: Word _ }
  (steps: G.Derivation w)
  (step: G.DerivationStep w)
  (sound: u = step.result):
  Derivation G u

def Derivation.lhs : Derivation G w → Word (G.V ⊕ G.Z)
| same u => u
| step l _ _ => l.lhs

def DerivationRelation (G: Grammar Prod) (v w: Word (G.V ⊕ G.Z)) : Prop :=
  ∃d: G.Derivation w, d.lhs = v 

notation:40 u:40 " (" G:40 ")⇒* " v:41 => DerivationRelation G u v

namespace Derivation

def compose (b: G.Derivation w) (a: G.Derivation b.lhs) : G.Derivation w :=
  match b with
  | same _ => a
  | step xs x h => step (xs.compose a) x h

theorem compose_lhs { b: G.Derivation w } { a: G.Derivation b.lhs } : lhs (b.compose a) = lhs a := by
  induction b with
  | same _ => unfold compose; rfl
  | step _ _ _ ih => simp [compose, lhs]; rw [ih]

def augment_left_mul {v w: Word _} (d: G.Derivation v) :
  G.Derivation (w * v) := by
  match d with
  | same _ => exact same _
  | step xs x h =>
    rw [h, <- DerivationStep.concat_left_result]
    exact step (xs.augment_left_mul) (x.concat_left w) rfl

def augment_left_cons {u: Word _} (w: _) (d: G.Derivation u) :
  G.Derivation (w :: u) := by
  match d with
  | same _ => exact same _
  | step xs x sound =>
    have ih := xs.augment_left_cons w
    apply step ih (x.concat_left [w])
    rw [sound]
    simp [DerivationStep.concat_left_result]
    rfl

theorem augment_left_cons_lhs (w: _) (d: G.Derivation u) :
  (d.augment_left_cons w).lhs = w :: d.lhs := by
  induction d with
  | same _ => rfl
  | step _ _ =>
    unfold augment_left_cons; simp [lhs]
    assumption

theorem lhs_eps_imp_rhs_eps (d: G.Derivation w) : d.lhs = ε → w = ε := by
  match d with
  | same _ => intro h; unfold lhs at h; assumption
  | step xs x _ =>
    intro h; unfold lhs at h
    have h' := Eq.symm x.sound
    simp_rw [xs.lhs_eps_imp_rhs_eps h] at h'
    simp [Word.mul_eq_eps] at h'
    have ⟨_, y⟩ := Production.lhs_contains_var x.prod.val
    rw [h'.1.2] at y
    contradiction

def prepend (d: G.Derivation w) (s: G.DerivationStep v) (h: s.result = d.lhs):
  G.Derivation w := by
  match d with
  | same _ => 
    exact .step (.same v) s h.symm
  | step xs x _ =>
    apply Grammar.Derivation.step
    unfold lhs at h
    exact xs.prepend s h
    assumption

theorem prepend_lhs { d: G.Derivation w } { s: G.DerivationStep v } { h: _ } :
  (d.prepend s h).lhs = v := by
  induction d with
  | same _ => unfold prepend; rfl
  | step _ _ => sorry

end Derivation

namespace DerivationRelation

theorem trans { u v w: Word _ } (h₁: u (G)⇒* v) (h₂: v (G)⇒* w) : u (G)⇒* w := by
  have ⟨d₂, h₂⟩ := h₂
  have ⟨d₁, h₁⟩ := (Eq.symm h₂) ▸ h₁
  exists d₂.compose d₁
  rw [<- h₁]
  apply Derivation.compose_lhs

theorem refl { u: Word _ } : u (G)⇒* u := by
  exists .same _

instance preorder (G: Grammar Prod) : Preorder (Word (G.V ⊕ G.Z)) where
  le u v := u (G)⇒* v
  le_refl _ := DerivationRelation.refl
  le_trans _ _ _ := DerivationRelation.trans

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
  sorry

theorem ExampleGrammar.gen_lang_supers : ExampleGrammar.lang ⊆ ExampleGrammar.GeneratedLanguage := by
  intro w ⟨ b, bz, hb, hz, wbz ⟩
  have : b = [⟨'b', _ ⟩] := hb
  rw [wbz, this, Set.mem_def, Grammar.GeneratedLanguage, Word.map_append _ _ _]
  sorry

theorem ExampleGrammar.gen_lang : ExampleGrammar.GeneratedLanguage = ExampleGrammar.lang := by
  apply Set.eq_of_subset_of_subset
  . exact gen_lang_subs
  . exact gen_lang_supers

end Grammar