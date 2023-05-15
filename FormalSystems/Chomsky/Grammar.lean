import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs

import FormalSystems.Preliminaries.Language

structure Production (Z: Finset α) (V: Finset nt) where
  lhs: Word (V ⊕ Z)
  rhs: Word (V ⊕ Z)
  lhs_contains_var: ∃v : V, .inl v ∈ lhs

@[simp] theorem Production.eq_iff_lhs_and_rhs_eq (p₁ p₂ : Production Z V) :
  p₁ = p₂ ↔ p₁.lhs = p₂.lhs ∧ p₁.rhs = p₂.rhs := by
  constructor
  . intro h; rw [h]; exact ⟨ rfl, rfl ⟩
  . intro ⟨ h₁, h₂ ⟩
    match p₁ with
    | ⟨ l, r, _ ⟩ => simp at h₁; simp at h₂; simp_rw [h₁, h₂]

notation:40 v:40 " →ₚ " u:40 => Production.mk v u

instance [DecidableEq (Z: Finset α)] [DecidableEq (V: Finset nt)] : DecidableEq (Production Z V) :=
  fun a b => decidable_of_decidable_of_iff (Iff.symm (Production.eq_iff_lhs_and_rhs_eq a b))

structure Grammar (α: Type _) (nt : Type _) where
  V: Finset nt
  Z: Finset α
  start: V
  productions: Finset (Production Z V)

structure DerivationStep (G: Grammar α nt) (u: Word (G.V ⊕ G.Z)) where
  prod: G.productions
  pre: Word (G.V ⊕ G.Z)
  suf: Word (G.V ⊕ G.Z)
  sound:
    have x := (↑prod : Production _ _).lhs
    u = pre * x * suf

def DerivationStep.production (step: DerivationStep G u): Production G.Z G.V :=
  step.prod

def DerivationStep.concat_left (step: DerivationStep G u) (w: Word (G.V ⊕ G.Z)): DerivationStep G (w * u) :=
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
  step.pre * step.production.rhs * step.suf

theorem DerivationStep.concat_left_result (step: DerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  (step.concat_left w).result = w * step.result := by
  unfold DerivationStep.result
  unfold concat_left
  unfold production
  simp [mul_assoc]

namespace Grammar

def empty (V: Finset nt) (Z: Finset α) (start: V) : Grammar α nt :=
  { V := V, Z := Z, start := start, productions := {} }

def OneStepDerivationRelation { G: Grammar α nt } (u v: Word (G.V ⊕ G.Z)) :=
  ∃(step: DerivationStep _ u), step.result = v 

notation:40 u:40 " ᴳ⇒ " v:41 => OneStepDerivationRelation u v

theorem OneStepDerivationRelation.cancel_left (w: Word _) (a: (v ᴳ⇒ u)): (w * v) ᴳ⇒ (w * u) := by
  have ⟨ step, _ ⟩ := a
  exists step.concat_left w
  rw [step.concat_left_result w]
  simp; assumption

def NStepDerivationRelation { G: Grammar α nt } (u v: Word (G.V ⊕ G.Z)) : ℕ → Prop
  | 0 => u = v
  | Nat.succ n => ∃w, u ᴳ⇒ w ∧ NStepDerivationRelation w v n

theorem NStepDerivationRelation.cancel_left (w: Word _) (a: NStepDerivationRelation v u n):
  NStepDerivationRelation (w * v) (w * u) n := by
  cases n with
  | zero => unfold NStepDerivationRelation at a; rw [a]; rfl
  | succ n' =>
    have ⟨ v', _, _ ⟩ := a
    exists w * v'; constructor
    . apply OneStepDerivationRelation.cancel_left; assumption
    . apply cancel_left; assumption

theorem NStepDerivationRelation.concat (a: NStepDerivationRelation v u n) (b: NStepDerivationRelation u w m) :
  NStepDerivationRelation v w (n+m) := by
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

def DerivationRelation { G: Grammar α nt } (u v: Word (G.V ⊕ G.Z)) :=
  ∃n, NStepDerivationRelation u v n 

notation:40 u:40 " ᴳ⇒* " v:41 => DerivationRelation u v

namespace DerivationRelation

theorem cancel_left (h: v ᴳ⇒* u) : w*v ᴳ⇒* w*u := by
  have ⟨ n, _ ⟩ := h
  exists n
  apply NStepDerivationRelation.cancel_left
  assumption

theorem trans (h1: v ᴳ⇒* u) (h2: u ᴳ⇒* w) : v ᴳ⇒* w := by
  have ⟨ n1, _ ⟩ := h1; have ⟨ n2, _ ⟩ := h2
  exists n1 + n2
  apply NStepDerivationRelation.concat
  assumption; assumption

theorem concat_right (v: Word _) (h1: S ᴳ⇒* w * v) (h2: v ᴳ⇒* u) : S ᴳ⇒* w * u := by
  apply DerivationRelation.trans
  . assumption
  . apply cancel_left; assumption

theorem refl {G: Grammar α nt} (w: Word (G.V ⊕ G.Z)) : w ᴳ⇒* w := by exists 0

instance preorder (G: Grammar α nt) : Preorder (Word (G.V ⊕ G.Z)) where
  le u v := u ᴳ⇒* v
  le_refl w := DerivationRelation.refl w
  le_trans _ _ _ h1 h2 := DerivationRelation.trans h1 h2

end DerivationRelation

def GeneratedLanguage (G: Grammar α nt) : Language G.Z :=
  fun w => [.inl ↑G.start] ᴳ⇒* (.inr <$> w)

def ExampleProductions : List (Production { 'b', 'z' } { 'A', 'B', 'S', 'Z' }) := [
    -- rule S -> BA
    ([ .inl ⟨ 'S', _ ⟩ ] →ₚ [ .inl ⟨ 'B', by simp ⟩, .inl ⟨ 'A', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'S', by simp ⟩ , List.Mem.head _ ⟩,
    -- rule A -> BA
    ([ .inl ⟨ 'A', _ ⟩ ] →ₚ [ .inl ⟨ 'B', by simp ⟩, .inl ⟨ 'A', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'A', by simp ⟩ , List.Mem.head _ ⟩,
    -- rule A -> ZA
    ([ .inl ⟨ 'A', _ ⟩ ] →ₚ [ .inl ⟨ 'Z', by simp ⟩, .inl ⟨ 'A', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'A', by simp ⟩ , List.Mem.head _ ⟩,
    -- rule A -> ε
    ([ .inl ⟨ 'A', _ ⟩ ] →ₚ ε)
    -- proof that lhs contains a variable
    ⟨ ⟨ 'A', by simp ⟩ , List.Mem.head _ ⟩,
    -- rule B -> b
    ([ .inl ⟨ 'B', _ ⟩ ] →ₚ [ .inr ⟨ 'b', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'B', by simp ⟩ , List.Mem.head _ ⟩,
    -- rule X -> z
    ([ .inl ⟨ 'Z', _ ⟩ ] →ₚ [ .inr ⟨ 'z', by simp ⟩ ])
    -- proof that lhs contains a variable
    ⟨ ⟨ 'Z', by simp ⟩ , List.Mem.head _ ⟩
]

def ExampleGrammar: Grammar Char Char where
  V := { 'A', 'B', 'S', 'Z' }
  Z := { 'b', 'z' }
  start := ⟨ 'S', by simp ⟩
  productions := ⟨ ExampleProductions , by simp ⟩ 

theorem ExampleGrammar.productions_eq_ex_productions (p: Production _ _):
  p ∈ ExampleGrammar.productions ↔ p ∈ ExampleProductions := by
  sorry

def ExampleGrammar.lang: Language (ExampleGrammar.Z) := 
  { [⟨ 'b', by simp ⟩] } ∘ₗ { [⟨ 'b', by simp ⟩], [⟨ 'z', by simp ⟩] }∗

theorem ExampleGrammar.gen_lang_subs : ExampleGrammar.GeneratedLanguage ⊆ ExampleGrammar.lang := by
  intro w ⟨ step_len, h ⟩
  sorry

theorem ExampleGrammar.gen_lang_supers : ExampleGrammar.lang ⊆ ExampleGrammar.GeneratedLanguage := by
  intro w ⟨ b, bz, hb, hz, wbz ⟩
  have : b = [⟨'b', _ ⟩] := hb
  rw [wbz, this, Set.mem_def, Grammar.GeneratedLanguage, Word.map_append _ _ _]
  apply Grammar.DerivationRelation.concat_right [ .inl ⟨ 'A', by simp ⟩ ]
  . have r := ExampleProductions[0]
    have step: DerivationStep ExampleGrammar [Sum.inl ExampleGrammar.start] := { 
      prod := ⟨ r, (ExampleGrammar.productions_eq_ex_productions _).mpr sorry ⟩,
      pre := ε, suf := ε,
      sound := by simp [Word.epsilon]; sorry
    }
    exists 1; exists r.rhs; constructor
    . exact ⟨ step, sorry ⟩
    . unfold NStepDerivationRelation
      simp []; sorry
  . sorry

theorem ExampleGrammar.gen_lang : ExampleGrammar.GeneratedLanguage = ExampleGrammar.lang := by
  apply Set.eq_of_subset_of_subset
  . exact gen_lang_subs
  . exact gen_lang_supers

end Grammar