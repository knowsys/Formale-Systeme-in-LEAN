import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Lex

import FormalSystems.Chomsky.ContextFree.ContextFreeGrammar
--================================================================================
-- File: RegularGrammar
/-  Containts Regular production definition and regular derivation
    definition, as well as muliple coercions, e.g. to
    context-free derivations.
-/
--================================================================================

/--Inductive structure: A regular production has one of three shapes:

  - `V → ε`,

  - `V → Z` or

  - `V → Z × V`,

  where V is the finset of variable/non-terminal and Z of terminal symbols.-/
inductive RegularProduction (Z: Finset α) (V: Finset nt) where
  /--`V → ε`-/
  | eps (lhs: V)
  /--`V → Z`-/
  | alpha (lhs: V) (rhs: Z)
  /--`V → Z × V`-/
  | cons (lhs: V) (rhs: Z × V)
  deriving DecidableEq

/--A regular productions left-hand side.-/
def RegularProduction.lhs : RegularProduction Z V → V
  | eps l => l
  | alpha l _ => l
  | cons l _ => l

/--A regular productions right-hand side.-/
def RegularProduction.rhs : RegularProduction Z V → Word (V ⊕ Z)
  | eps _ => ε
  | alpha _ a => [.inr a]
  | cons _ ⟨ a, A ⟩ => [.inr a, .inl A]

/--The proposition that captures whether a regular production
  goes to ε.-/
def RegularProduction.isEps : RegularProduction Z V → Prop
  | eps _ => True
  | _ => False

/--Get the regular productions right-hand side, but as a tuple
  over Z and V.-/
def RegularProduction.getRhs (p: RegularProduction Z V) : Option Z × Option V :=
  match p with
  | cons _ ⟨a, X⟩ => (.some a, .some X)
  | alpha _ a => (.some a, .none)
  | eps _ => (.none, .none)

/--Prove that .isEps is a decidable predicate.-/
instance { α nt: Type } { Z: Finset α } { V: Finset nt } :
  DecidablePred (@RegularProduction.isEps α Z nt V) := fun x =>
  match x with
  | RegularProduction.eps _ => Decidable.isTrue trivial
  | RegularProduction.alpha _ _ => Decidable.isFalse (λh => h)
  | RegularProduction.cons _ _ => Decidable.isFalse (λh => h)

/--Coerve regular productions in context-free productions.-/
instance : Coe (RegularProduction Z V) (ContextFreeProduction Z V) where
  coe p := {
    lhs := p.lhs,
    rhs := p.rhs,
  }

/--Embed regular productions in context-free productions.-/
def RegularProduction.toContextFree : RegularProduction Z V ↪ ContextFreeProduction Z V where
  toFun := Coe.coe
  inj' p₁ p₂ := by
    simp [Coe.coe]
    intro hl hr
    match p₁ with
    | eps _ =>
      match p₂ with
      | eps _ => simp [lhs] at hl; rw [hl]
    | alpha _ _ =>
      match p₂ with
      | alpha _ _ =>
        simp [lhs] at hl; simp [rhs] at hr
        rw [List.cons_eq_cons] at hr; simp at hr
        simp [hl, hr]
    | cons _ ⟨ _, _ ⟩ =>
      match p₂ with
      | cons _ _ =>
        simp [lhs] at hl; simp [rhs] at hr
        rw [List.cons_eq_cons] at hr; simp at hr
        simp [hl, hr]

/--Coerce regular productions in generic productions.-/
def RegularProduction.toProduction : RegularProduction Z V ↪ GenericProduction Z V :=
  toContextFree.trans ContextFreeProduction.toProduction

/--Regular productions are instances of generic productions.-/
instance : Production α nt RegularProduction :=
  Production.fromEmbedding $ fun _ _ => RegularProduction.toProduction

/--Regular productions are instances of context-free productions.-/
instance : Production.ContextFree α nt RegularProduction where
  lhs_var p := p.lhs
  lhs_eq_lhs _ := by rfl

/--Theorem: .getRhs acts as expected with regard to .rhs-/
theorem RegularProduction.rhs_eq_deconstr_rhs (p: RegularProduction Z V):
  Production.rhs p =
    Word.mk (Sum.inr <$> p.getRhs.1.toList) *
    Word.mk (Sum.inl <$> p.getRhs.2.toList) := by
  cases p <;> rfl

/--Theorem: .lhs acts as expected.-/
theorem RegularProduction.lhs_eq_production_lhs { p: RegularProduction Z V }:
  Production.lhs p = [.inl p.lhs] := by rfl

/--A regular grammar is an instance of a grammar, where the set of productions
  is reduced to those, that are regular.-/
def RegularGrammar (α nt: Type) := @Grammar α nt RegularProduction _

/--Coerce regular grammars in generic grammars.-/
instance : Coe (RegularGrammar α nt) (@Grammar α nt GenericProduction _) where
  coe g := { g with
    productions := g.productions.map RegularProduction.toProduction
  }

variable { G: RegularGrammar α nt } { p: G.productions }

open Grammar

/--Theorem: The result of`V→ε`regular productions is`ε`.-/
theorem RegularProduction.eps_step_result:
  p.val = RegularProduction.eps v → (DerivationStep.fromRule p).result = ε := by
  intro h; simp [DerivationStep.fromRule, DerivationStep.result, h]; rfl

/--Theorem: The result of`V→v*z`regular productions is`v*z`.-/
theorem RegularProduction.cons_step_result:
  p.val = .cons v (w, b) → (DerivationStep.fromRule p).result = [.inr w, .inl b] := by
  intro h; simp [DerivationStep.fromRule, DerivationStep.result, h]; rfl

/--Theorem: .isEps is true implies we have a regular production
  constructed with the .eps constructor.-/
theorem RegularProduction.eq_eps_from_isEps
  { Z: Finset α } { V: Finset nt }
  { p: RegularProduction Z V }:
  p.isEps → p = RegularProduction.eps p.lhs := by
  intro h
  match p with
  | .eps _ => rfl

namespace RegularGrammar

/--Inductive structure: Regular Derivations in G from variables v to
  (fully terminal) words w are constructed using three possible constructors.
  Note: This is defined in such a way, that it must be complete / exhaustive.
  No partial derivation can ever be stored. Note also, that the result
  is fixed in the type. This makes this structure rather clunky and tricky to use.
  It may result in certain operations not being possible: If the result type
  is not known at compile time.

  - `.eps v h_v h_w`

    - from the variable v we go to ε. Requires a proof that the
        production is in the grammar.

   - `.alpha v h_v h_w`

    - from the variable v we go to a symbol that comprises w. Requires a proof that the
        production is in the grammar.

   - `.step v v' h_v h_w`

    - Step constructor. Is a recursive call of the constructor.

    - Requires a .cons production rule to have been applied.

    - v' is generated by said .cons rule.

    - w must have the shape `a :: w'`

    - Finally, provide a RegularDerivation from v' to w'.
-/
inductive RegularDerivation (G: RegularGrammar α nt): (v: G.V) → (w: Word G.Z) → Type
| eps (v: _) (h_v: .eps v ∈ G.productions) (h_w: w = ε):
  G.RegularDerivation v w
| alpha (v: _) (h_v: .alpha v a ∈ G.productions) (h_w: w = [a]):
  G.RegularDerivation v w
  /--step constructor.-/
| step (v v': _) (h: .cons v (a, v') ∈ G.productions) (h_w: w = (a :: w')):
  G.RegularDerivation v' w' → G.RegularDerivation v w

mutual
  def RegularDerivation.fromDerivation
    (derivation: G.Derivation [.inl X] w')
    (h: Sum.inr <$> w = w'):
    G.RegularDerivation X w :=
    match derivation with
    | .same h_same => by
      cases w <;> simp [<- h_same] at h
      rw [List.cons_eq_cons] at h
      have ⟨_, _⟩ := h
      contradiction
    | .step s d' hd =>
      have _termination: Derivation.len d' < Derivation.len (Derivation.step s d' hd) := by simp [Derivation.len]
      fromStep s d' hd h
  termination_by (derivation.len, 0)

  def RegularDerivation.fromStep
    (step: G.DerivationStep [.inl X])
    (derivation: G.Derivation u w')
    (h_u: step.result = u)
    (h_w: Sum.inr <$> w = w'):
    G.RegularDerivation X w :=
    have ⟨left, pre, suf⟩ := step.lhs_singleton
    match hp:step.prod.val with
    | .eps lhs =>
      RegularDerivation.eps
        X
        (by
          rw [hp,
            RegularProduction.lhs_eq_production_lhs,
            List.cons_eq_cons]
            at left
          simp [RegularProduction.lhs] at left
          rw [<- left, <- hp]
          exact step.prod.prop
        )
        (by
          unfold DerivationStep.result at h_u
          simp [hp, RegularProduction.rhs_eq_deconstr_rhs,
            Word.mk, <- Word.eps_eq_nil] at h_u
          simp [<-h_u, pre, suf] at derivation
          cases derivation with
          | same h_same =>
            dsimp [RegularProduction.getRhs] at h_same
            simp [<-h_same, <-Word.eps_eq_nil] at h_w
            rw [Word.eps_eq_nil, List.map_eq_nil] at h_w
            exact h_w
          | step s' _ _ =>
            have contra := s'.sound.symm
            simp [RegularProduction.getRhs, <-Word.eps_eq_nil, List.map] at contra
            simp [Word.mul_eq_eps] at contra
            have _ := contra.1.2
            contradiction
        )
    | .alpha lhs a =>
      RegularDerivation.alpha (a:=a)
        X
        (by
          rw [hp,
            RegularProduction.lhs_eq_production_lhs,
            List.cons_eq_cons]
            at left
          simp [RegularProduction.lhs] at left
          rw [<- left, <- hp]
          exact step.prod.prop
        )
        (by
          unfold DerivationStep.result at h_u
          simp [hp, RegularProduction.rhs_eq_deconstr_rhs, Word.mk] at h_u
          simp [<-h_u, pre, suf] at derivation
          cases derivation with
          | same h_same =>
            simp [HMul.hMul, Mul.mul] at h_same
            rw [<- h_same] at h_w
            cases w
            contradiction
            simp [List.map_cons] at h_w
            have ⟨h1, h2⟩ := List.cons_eq_cons.mp h_w
            simp [Sum.inr_injective] at h1
            simp [List.map_eq_nil, RegularProduction.getRhs] at h2
            rw [h1, h2]
          | step s' _ _ =>
            apply False.elim
            have contra := s'.sound.symm
            rw [RegularProduction.lhs_eq_production_lhs] at contra
            simp [HMul.hMul, Mul.mul, RegularProduction.getRhs] at contra
            rw [List.append_eq_cons] at contra
            cases contra
            case inl h =>
              have ⟨_, h⟩ := h
              simp at h
            case inr h =>
              have ⟨_, h⟩ := h
              simp at h
          )
    | .cons _ (a, X') =>
      RegularDerivation.step
        X
        X'
        (by
          have : step.prod.val = .cons X (a, X') := by
            rw [Production.prod_ext]; constructor
            assumption; simp [hp]; rfl
          rw [<- this]; exact step.prod.prop
        )
        (by
          unfold DerivationStep.result at h_u
          simp [hp, RegularProduction.rhs_eq_deconstr_rhs, pre, suf] at h_u
          simp [Word.mk, HMul.hMul, Mul.mul] at h_u
          apply ContextFreeGrammar.derivation_preserves_prefix derivation
          exact h_u.symm
          exact h_w.symm
        )
        (by
          unfold DerivationStep.result at h_u
          simp [hp, RegularProduction.rhs_eq_deconstr_rhs, pre, suf] at h_u
          simp [Word.mk, HMul.hMul, Mul.mul] at h_u

          apply RegularDerivation.fromDerivation (Grammar.Derivation.cancelLeft derivation h_u.symm h_w.symm)
          rfl
        )
  termination_by (derivation.len, 1)
  decreasing_by
    apply (Prod.Lex.lt_iff _ _).mpr
    try { simp [Derivation.cancelLeft_len] }
end

def RegularDerivation.toDerivation (d: G.RegularDerivation v w):
  G.Derivation [.inl v] (Sum.inr <$> w) :=
  match d with
  | .eps _ h_l h_r =>
    Derivation.step
      {
        pre := ε
        suf := ε
        prod := ⟨_, h_l⟩
        sound := rfl
      }
      (Derivation.same (by simp [h_r]; rfl))
      rfl
  | .alpha _ h_l h_r =>
    Derivation.step
      {
        pre := ε
        suf := ε
        prod := ⟨_, h_l⟩
        sound := rfl
      }
      (Derivation.same (by simp [h_r]; rfl))
      rfl
  | .step (a:=a) _ _ h_l h_r d' =>
    Derivation.step
      {
        pre := ε
        suf := ε
        prod := ⟨_, h_l⟩
        sound := rfl
      }
      (cast (by rw [h_r]; rfl) (d'.toDerivation.augment_left_cons (w:=Sum.inr a)))
      rfl

instance : Coe (@RegularDerivation α nt G v w) (Derivation ↑G (Word.mk [Sum.inl v]) (Sum.inr <$> w)) where
  coe regDerivation := regDerivation.toDerivation

end RegularGrammar
