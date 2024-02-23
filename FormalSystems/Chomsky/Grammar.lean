import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs

import FormalSystems.Preliminaries.Language

--  Denote commonly used implicit typed variable names:
--  α   - An alphabet+, the type of symbols (terminal and? non-terminal symbols).
--  nt  - The type of non-terminal symbols (variables).
--  Z   - A finite set of symbols.
--  V   - A finite set of non-terminal symbols (variables).
variable { α: Type } { nt: Type } { Z: Finset α } { V: Finset nt }

/--Class: A production rule has

  - lhs               - a left hand side

  - rhs               - a right hand side

  - lhs_contains_var  - the proposition "left hand side contains a variable"

  - prod_ext          - proposition defining when two propositions are equal
                        (when both lhs and rhs are the same)-/
class Production (α: Type) (nt: Type) (P: Finset α → Finset nt → Type) where
  lhs { Z: Finset α } { V: Finset nt } (p: P Z V) : Word (V ⊕ Z) -- disjoint union
  rhs { Z: Finset α } { V: Finset nt } (p: P Z V) : Word (V ⊕ Z)
  /--A proof that the left side contains at least one non-terminal symbol.-/
  lhs_contains_var { Z: Finset α } { V: Finset nt } (p: P Z V) : ∃v : V, .inl v ∈ lhs p
  /--Definition of equality for productions.-/
  prod_ext { Z: Finset α } { V: Finset nt } (p₁ p₂: P Z V) :
    p₁ = p₂ ↔ lhs p₁ = lhs p₂ ∧ rhs p₁ = rhs p₂

/--Structure: A generic production rule structure. Requires a set of terminal symbols and a set of non-terminal symbols (variables).
  The structure has:

  - lhs               - a left hand side

  - rhs               - a right hand side

  - lhs_contains_var  - the proof that "left hand side contains a variable", i.e. is nonempty-/
structure GenericProduction (Z: Finset α) (V: Finset nt) where
  /--The left hand side.-/
  lhs: Word (V ⊕ Z)
  /--The right hand side.-/
  rhs: Word (V ⊕ Z)
  /--A proof that the left side contains at least one non-terminal symbol.-/
  lhs_contains_var: ∃v : V, .inl v ∈ lhs

/--Theorem: Two generic productions are equal if and only if their left- and right-hand side are the same.-/
@[simp] theorem GenericProduction.eq_iff_lhs_and_rhs_eq (p₁ p₂ : GenericProduction Z V) :
  p₁ = p₂ ↔ p₁.lhs = p₂.lhs ∧ p₁.rhs = p₂.rhs := by
  constructor
  . intro h; rw [h]; exact ⟨ rfl, rfl ⟩
  . intro ⟨ h₁, h₂ ⟩
    match p₁ with
    | ⟨ l, r, _ ⟩ => simp at h₁; simp at h₂; simp_rw [h₁, h₂]

/--Production is an instance of Generic Production.-/
instance : Production α nt GenericProduction where
  lhs := (·.lhs)
  rhs := (·.rhs)
  lhs_contains_var := (·.lhs_contains_var)
  prod_ext := GenericProduction.eq_iff_lhs_and_rhs_eq

/--Construct a production from an embedding. The embedding is of ProductionType in GenericProduction.-/
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

/--Allow for →ₚ notation to construct GenericProductions. Go from a word over V ⊕ Z to another word over V ⊕ Z.
  Still require a proof for variable-existence on the left side right after this rule.-/
notation:40 v:40 " →ₚ " u:40 => GenericProduction.mk v u

/--Equality is decidable for GenericProductions.-/
instance [DecidableEq (Z: Finset α)] [DecidableEq (V: Finset nt)] : DecidableEq (GenericProduction Z V) :=
  fun a b => decidable_of_decidable_of_iff (Iff.symm (Production.prod_ext a b))

/--Structure: A Grammar is a structure containing:

  - Z - a finite set of terminal symbols

  - V - a finite set of non-terminal symbols (variables)

  - start - a start symbol from the set of variables

  - productions - a finite set of production rules (type Production)-/
structure Grammar (Prod: Finset α → Finset nt → Type) [Production α nt Prod] where
  /--A finite set of terminal symbols-/
  Z: Finset α
  /--A finite set of non-terminal symbols (variables)-/
  V: Finset nt
  /--The starting symbol.-/
  start: V
  /--The finite set of production rules-/
  productions: Finset (Prod Z V)

namespace Grammar

variable { Prod: Finset α → Finset nt → Type } [Production α nt Prod]

/--Structure: The DerivationStep starting in`u`. Structure has four attributes:

  - `prod` - store the set of production rules that could be used in the derivation step.

  - `pre`,`suf` - `u = pre * x * suf`

  - `sound` - Show the soundness of a derivation step by proving
  the equality`u = pre * x * suf`and showing that x appears on the left side of the
  possible production rules`prod`.-/
structure DerivationStep (G: Grammar Prod) (u: Word (G.V ⊕ G.Z)) where
  /--The set of the grammars productions applicable in this derivation step.-/
  prod: G.productions
  /--The symbols to the left of the non-terminal symbol we produce from.-/
  pre: Word (G.V ⊕ G.Z)
  /--The symbols to the right of the non-terminal symbol we produce from.-/
  suf: Word (G.V ⊕ G.Z)
  /--A proof that the production rules are applicable to the variable
  that is encased in the left side of the derivation step, and of the inclusion
  of this variable.-/
  sound:
    have x := Production.lhs prod.val
    u = pre * x * suf

variable { G: Grammar Prod } { u: Word (G.V ⊕ G.Z) }

/--Construct a derivation step to have been applied to a left-side longer string.-/
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

/--Define one of the possible results of a derivation step as the result of applying
  one of the production rules to the variable within the pre- and suffix.-/
def DerivationStep.result (step: DerivationStep G u) : Word (G.V ⊕ G.Z) :=
  step.pre * Production.rhs step.prod.val * step.suf

/--Theorem: Left-augmenting (adding a word to the left of) the input
  string of a derivation step changes its result as expected.-/
theorem DerivationStep.augment_left_result (step: DerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  (step.augment_left w).result = w * step.result := by
  unfold DerivationStep.result
  unfold augment_left
  simp [mul_assoc]

/--Construct the trivial DerivationStep ε * x * ε ⇒ p(x) from a production rule.-/
def DerivationStep.fromRule (p: G.productions) : DerivationStep G (Production.lhs (p.val)) where
  prod := p
  pre := ε
  suf := ε
  sound := by simp [Word.epsilon]

/--Theorem: The result of a derivation step constructed from a rule is equal to
  the right side of that rule.-/
theorem DerivationStep.from_rule_result { p: G.productions } :
  (DerivationStep.fromRule p).result = (Production.rhs (p.val)) := by
  simp [result, DerivationStep.fromRule, Word.epsilon]

/--Theorem: DerivationSteps that have a single variable as an input
  have empty pre- and suffix.-/
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

/--Inductive definition of derivations u (G)⇒* v in Grammars.

  Either no step was made (constructor:`same`, requires a proof that u = v), or
  we have a recursive definition with at least one step (constructor `step`).-/
inductive Derivation (G: Grammar Prod) : Word (G.V ⊕ G.Z) → Word (G.V ⊕ G.Z) → Type
/--A 0 step derivation. On proof of u=v, return a 0-step derivation from u to v.-/
| same {u v: Word (G.V ⊕ G.Z)} (h: u = v) : G.Derivation u v
/--The recursive step definition of a derivation. Requires:
- `step`  - The derivation step with input u,
- `_`     - A derivation from u' to v (recursive part of the definition),
- `sound` - The proof that`step`yields u'.
-/
| step
  {u u' v: Word (G.V ⊕ G.Z)}
  (step: G.DerivationStep u)
  (_: Derivation G u' v)
  (sound: step.result = u') :
  Derivation G u v

/--The closure of derivations. Has attributes start and result.-/
class DerivationCls (G: Grammar Prod) (t: Type) where
  start: Word (G.V ⊕ G.Z)
  result: Word (G.V ⊕ G.Z)

/--Closures of derivations are derivations with named attributes.-/
instance : DerivationCls G (G.Derivation a b) where
  start := a
  result := b

/-- u (G)⇒* v -notation for derivations. Is the proposition that there
  exists a derivation (∃) from u to v in G.-/
notation:40 u:40 " (" G:40 ")⇒* " v:41 => (Nonempty $ Derivation G u v)

/--The length of a derivation (∈ ℕ).

  Recursive definition based on the constructor
  used to define the derivation:`same`yields a derivation of length 0,`step`
  requires a recursive call of a derivations length.-/
def Derivation.len { u w: Word (G.V ⊕ G.Z) }: G.Derivation u w → Nat
| same _ => 0
| step _ d _ => Nat.succ d.len

namespace Derivation

/--Theorem: It is possible to augment a prefix`w`to the left side of in- and output of a
  valid derivation. We recieve a valid derivation.-/
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

/--Return a derivation where we have added a new prefix`w`to the left sides of in-
  and output of the input derivation.-/
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

/--Theorem: The derivation relation is transitive. This theorem can be used to return
  a transitive derivation.-/
theorem trans {u v w: Word _} (d1: G.Derivation u v) (d2: G.Derivation v w) : G.Derivation u w := by
  induction d1 with
  | same h => exact h ▸ d2
  | step l _ sound ih => exact step l (ih d2) sound

end Derivation

/--The derivation relation is a preorder. Return said preorder as induced by the grammer of the derivation relation.

  (A preorder is a reflexive, transitive relation ≤ with a < b defined in the obvious way.)-/
instance DerivationRelation.preorder (G: Grammar Prod) : Preorder (Word (G.V ⊕ G.Z)) where
  le u v := u (G)⇒* v
  le_refl w := Nonempty.intro $ Derivation.same rfl
  le_trans _ _ _ := by
    intro ⟨d₁⟩ ⟨d₂⟩
    apply Nonempty.intro
    exact d₁.trans d₂

/--The language of a gammar is defined as the set of those words that can be derived
  from the starting symbol.-/
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
  productions := ExampleProductions.toFinset

theorem ExampleGrammar.productions_eq_ex_productions (p: GenericProduction _ _):
  p ∈ ExampleGrammar.productions ↔ p ∈ ExampleProductions := by
  simp [ExampleGrammar]

def ExampleGrammar.lang: Language ({ 'b', 'z' } : Finset _) :=
  { [⟨ 'b', by simp ⟩] } ∘ₗ { [⟨ 'b', by simp ⟩], [⟨ 'z', by simp ⟩] }∗

-- TODO: a proof for ExampleGrammar.GeneratedLanguage = ExampleGrammar.lang
-- see lecture 2, slides 18 - 21

end Grammar
