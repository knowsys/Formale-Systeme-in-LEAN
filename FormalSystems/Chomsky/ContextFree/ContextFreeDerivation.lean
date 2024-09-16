import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor

import FormalSystems.Chomsky.ContextFree.DerivationTree
--================================================================================
-- File: ContextFreeDerivation
/-  Containts context-free derivation definition, some decidability theorems,
    conditions for exhaustiveness / totality and beginning in the root,
    exhaustive context-free derivations and two attempts at coercion:
    from CFDs to derivation trees and vice versa. These currently probably
    cannot succeed and need a lot of work still.
-/
--================================================================================

namespace ContextFreeGrammar

/--Define context free derivations u (G)=>* v inductively.
  Either no step was made (constructor:`same`, requires a proof that u = v), or
  we have a recursive definition with at least one step (constructor `step`)-/
inductive ContextFreeDerivation (G : ContextFreeGrammar α nt) : (Word (G.V ⊕ G.Z)) → (Word (G.V ⊕ G.Z)) → Type
  /--0 step derivations u (G)=>* v-/
  | same {u v : (Word (G.V ⊕ G.Z))} (h : u = v) : ContextFreeDerivation G u v
  /--The recursive step definition of a derivation. Requires:
  - `step`  - The derivation step with input u,
  - `_derivation`     - A derivation from u' to v (recursive part of the definition),
  - `sound` - The proof that`step`yields u'.
  -/
  | step
    {u u' v : Word (G.V ⊕ G.Z)}
    (step : ContextFreeDerivationStep G u)
    (_derivation : ContextFreeDerivation G u' v)
    (sound : step.result = u') :
    ContextFreeDerivation G u v
deriving DecidableEq

/--Define the length of a derivation.-/
def ContextFreeDerivation.length : ContextFreeDerivation G u v -> Nat
| .same _ => 0
| .step _ derivation _ => 1 + derivation.length

--IMPORTANT: theorems are not computable!
/--Define an embedding of context-free derivations in generic derivations.-/
def ContextFreeDerivation.toDerivation : @ContextFreeDerivation α nt G u v -> @Grammar.Derivation α nt GenericProduction _ G u v
| .same h_same =>
  Grammar.Derivation.same h_same
| .step dStep derivation h_sound =>
  Grammar.Derivation.step dStep derivation.toDerivation h_sound

/--Coerce CFDs in generic derivations-/
instance : Coe (@ContextFreeDerivation α nt G u v) (@Grammar.Derivation α nt GenericProduction _ G u v) where
  coe cfDerivation := ContextFreeDerivation.toDerivation cfDerivation

/-- u CF(G)⇒* v -notation for context-free derivations. Is the proposition that there
  exists a derivation (∃) from u to v in G. Eliminate this in a hypothesis by using`cases h_cfd`.-/
notation:40 u:40 " CF(" G:40 ")⇒* " v:41 => (Nonempty $ ContextFreeDerivation G u v)

/--The language of a grammar is defined as the set of those words that can be derived
  using a context-free grammar from the starting symbol.-/
def GeneratedLanguage (G: ContextFreeGrammar α nt) : Language G.Z :=
  fun w => [.inl G.start] CF(G)⇒* (.inr <$> w)

namespace ContextFreeDerivation
  /--Condition specifying wether a derivation is exhaustive:
    It needs to evaluate ALL variables to terminal symbols,
    i.e. have exhaustively applied production rules.-/
  def exhaustiveCondition (_ : ContextFreeDerivation G u v) : Prop :=
    ∀ symbol ∈ v, Sum.isRight symbol

  /--Condition specifying wether a derivation does one or more step,
    i.e. is not a 0-step derivation.-/
  def nonZeroStepCondition (cfd : ContextFreeDerivation G u v) : Prop :=
    (¬ ∃ h_same, cfd = ContextFreeDerivation.same h_same)

  /--Condition specifying wether a derivation begins in either a single variable or a single terminal.-/
  def startsIn1Condition (_ : ContextFreeDerivation G u v) : Prop := (u.len = 1)

  /--Decide wether this cfd is exhaustive.-/
  def decideExhaustive (cfd : ContextFreeDerivation G u v) : Decidable (cfd.exhaustiveCondition) := v.decideIsAllZ

  /--Exhaustiveness is decidable.-/
  instance (cfd : ContextFreeDerivation G u v) : Decidable (cfd.exhaustiveCondition) := cfd.decideExhaustive

  /--Decide wether this cfd satisfies the non-zero step condition.-/
  def decideNonZeroStepCondition (cfd : ContextFreeDerivation G u v) : Decidable (cfd.nonZeroStepCondition) :=
    match cfd with
    | same h_same => isFalse (by simp [nonZeroStepCondition, h_same])
    | step _ _ _ => isTrue (by simp [nonZeroStepCondition])

  /--Non-zero stepness is decidable.-/
  instance (cfd : ContextFreeDerivation G u v) : Decidable (cfd.nonZeroStepCondition) := cfd.decideNonZeroStepCondition

  /--Decide wether this cfd satisfies the starts-in-1 condition.-/
  def decideStartsIn1 (cfd : ContextFreeDerivation G u v) : Decidable (cfd.startsIn1Condition) :=
    match u_len : u.len with
    | 0 => isFalse (by simp [ContextFreeDerivation.startsIn1Condition, u_len])
    | Nat.succ 0 => isTrue (by simp [ContextFreeDerivation.startsIn1Condition, u_len])
    | Nat.succ (Nat.succ n) => isFalse (by simp [ContextFreeDerivation.startsIn1Condition, u_len])

  /--starts in 1 is decidable-/
  instance (cfd : ContextFreeDerivation G u v) : Decidable (cfd.startsIn1Condition) := cfd.decideStartsIn1

  /--Is this context-free derivation exhaustive?:
    It needs to evaluate ALL variables to terminal symbols,
    i.e. have exhaustively applied production rules. (Bool)-/
  def isExhaustive (cfd : ContextFreeDerivation G u v) : Bool := Decidable.decide cfd.exhaustiveCondition

  /--Does this context-free derivation start in a single symbol,
    i.e. a single variable (root) or a single terminal symbol (leaf). (Bool)-/
  def startsIn1 (cfd : ContextFreeDerivation G u v) : Bool := Decidable.decide cfd.startsIn1Condition

  /--Theorem: It is possible to augment a prefix-word`w`to the left side of in- and output of a
    valid derivation. We recieve a valid derivation.-/
  theorem augment_left (d: ContextFreeDerivation G u v) :
    ContextFreeDerivation G (w * u) (w * v) := by
    induction d with
    | same h => apply same; simp [h]
    | step s _ sound =>
      apply step
      . assumption
      swap
      . exact s.augment_left w
      . rw [<- sound]; exact s.augment_left_result _

  /--Theorem: It is possible to augment a prefix-word`w`to the left side of in- and output of a
    valid derivation. We recieve a valid derivation.-/
  def augment_left_mul {u v w: Word _} (d: ContextFreeDerivation G u v) :
    ContextFreeDerivation G (w * u) (w * v) := by
    match d with
    | same h => apply same; simp [h]
    | step s d' sound =>
      apply step
      . exact d'.augment_left_mul
      swap
      . exact s.augment_left w
      . rw [<- sound]; exact s.augment_left_result _

  /--Return a derivation where we have added a new prefix-symbol`w`to the left sides of in-
    and output of the input derivation.-/
  def augment_left_cons {u v: Word _} (d: ContextFreeDerivation G u v) :
    ContextFreeDerivation G (w :: u) (w :: v) := by
    --exact Grammar.Derivation.augment_left_cons d
    match d with
    | same h => apply same; simp [h]
    | step s d' sound =>
      apply step
      . exact d'.augment_left_cons
      swap
      . exact s.augment_left [w]
      . rw [<- sound]; exact s.augment_left_result _


  /--Return a derivation where we have added a new prefix-word`w`to the right sides of in-
    and output of the input derivation.-/
  theorem augment_right (d: ContextFreeDerivation G u v) :
    ContextFreeDerivation G (u * w) (v * w) := by induction d with
    | same h => apply same; simp [h]
    | step s _ sound =>
      apply step
      .assumption
      swap
      . exact s.augment_right w
      rw [<- sound]; exact s.augment_right_result _

  /--Return a derivation where we have added a new prefix-symbol`w`to the right sides of in-
    and output of the input derivation.-/
  def augment_right_mul {u v: Word (G.V ⊕ G.Z)} (d: ContextFreeDerivation G u v) :
    ContextFreeDerivation G (Word.mk (u.append w)) (Word.mk (v.append w)) := by
    match d with
    | .same h => apply ContextFreeDerivation.same; simp [h]
    | .step s d' sound =>
      apply ContextFreeDerivation.step
      . exact d'.augment_right_mul
      swap
      . exact s.augment_right w
      . rw [<- sound]; exact s.augment_right_result _

  /--Return a derivation where we have added a new prefix-symbol`w`to the right sides of in-
    and output of the input derivation.-/
  def augment_right_cons {u v: Word (G.V ⊕ G.Z)} (d: ContextFreeDerivation G u v) :
    ContextFreeDerivation G (Word.mk (u.append w)) (Word.mk (v.append w)) := by
    match d with
    | .same h => apply ContextFreeDerivation.same; simp [h]
    | .step s d' sound =>
      apply ContextFreeDerivation.step
      . exact d'.augment_right_cons
      swap
      . exact s.augment_right w
      . rw [<- sound]; exact s.augment_right_result _

  /--Concatenate two derivations: Such that they are left/right of each other.-/
  def concat
    {G : ContextFreeGrammar α nt} {u₁ u₂ v₁ v₂ : (Word (G.V ⊕ G.Z))}
    (cfd₁ : (@ContextFreeDerivation α nt G u₁ v₁))
    (cfd₂ : (@ContextFreeDerivation α nt G u₂ v₂)) :
    (ContextFreeDerivation G (u₁ * u₂) (v₁ * v₂)) := by
    match cfd₁, cfd₂ with
    | .same h_same₁, .same h_same₂ =>
      exact @ContextFreeDerivation.same α nt G (u₁ * u₂) (v₁ * v₂) (by rw [h_same₁, h_same₂])
    | .same h_same₁, .step _ _ _ =>
      rw [h_same₁.symm]
      apply @ContextFreeDerivation.augment_left_mul α nt G u₂ v₂ u₁ cfd₂
    | .step _ _ _, .same h_same₂ =>
      rw [h_same₂.symm]
      apply @ContextFreeDerivation.augment_right_mul α nt G u₂ u₁ v₁ cfd₁
    | @ContextFreeDerivation.step α nt G _ u' _ step₁ deriv₁ sound₁, .step _ _ _ =>
      apply ContextFreeDerivation.step
      case u' =>
        exact u' * u₂
      case _derivation =>
        apply ContextFreeDerivation.concat deriv₁ cfd₂
      case step =>
        exact step₁.augment_right u₂
      case sound =>
        have step_augmented_result : _ := step₁.augment_right_result u₂
        simp [ContextFreeDerivationStep.result, Grammar.DerivationStep.result] at step_augmented_result
        simp [ContextFreeDerivationStep.result, Grammar.DerivationStep.result, step_augmented_result]
        simp [ContextFreeDerivationStep.result, Grammar.DerivationStep.result] at sound₁
        rw [← sound₁]
end ContextFreeDerivation

/- ! -/
/- !!! -/
/- !!!!! -/
/- TODO: all of the below likely needs to be completely reworked! -/
/- !!!!! -/
/- !!! -/
/- ! -/





/--Structure: Exhaustive contextfree derivations. Attributes:

  - `derivation`  - the underlying context-free derivation

  - `exhaustive`  - a proof for the exhaustiveness of the derivation

  - `startsin1` - a proof that the derivation starts in a single symbol-/
structure ExhaustiveContextFreeDerivation
  (G : ContextFreeGrammar α nt)
  (u v : Word (G.V ⊕ G.Z)) where
  derivation : ContextFreeDerivation G u v
  exhaustive : derivation.exhaustiveCondition
  startsIn1 : derivation.startsIn1Condition
  -- nonZero: isn't necessary: exhaustive means .leaf constructor can be used.
deriving DecidableEq

/--Theorem: Children (i.e. next steps) of exhaustive CFDs are exhaustive.-/
theorem ContextFreeDerivation.exhaustive_imp_child_exhaustive
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (cfd : @ContextFreeDerivation α nt G u v)
  (h_exhaustive : cfd.exhaustiveCondition) :
  ∀ u' : Word ({ x // x ∈ G.V } ⊕ { x // x ∈ G.Z }),
  ∀ step : ContextFreeDerivationStep G u,
  ∀ derivation : ContextFreeDerivation G u' v,
  ∀ sound : _,
  cfd = ContextFreeDerivation.step step derivation sound →
  derivation.exhaustiveCondition := by
    match cfd with
    | same h_same =>
      intro u' step derivation sound
      rw [imp_iff_not_or]
      apply Or.inl
      tauto
    | @step _ _ _ _ u' _ dstep derivation sound =>
      intro u' step derivation sound
      intro h_constructor
      rw [exhaustiveCondition]
      rw [h_constructor, exhaustiveCondition] at h_exhaustive
      exact h_exhaustive

/--Collect the DerivationTree Nodes. Each node in the list
  corresponds to exactly one variable in u and each variable in
  u has a returned DerivationTree node. Cannot be called for 0-step
  derivations.

  Note: This function is too long and doesn't work. If I were to write this function
  again, I would define a new data structure that is returned by this function with
  the following attributes:

    - It stores a word. This word corresponds to u or u', i.e.
      the origin of the derivation. In each recursive call we are given an
      instance of this structure that matches u' and return an instance
      of this structure that matches u

    - It stores a list of DerivationTrees. These derivation trees are
      sub-trees of the final derivation tree. The structure stores those derivation
      trees that correspond to the variables in its word attribute (see above).

    - Each derivation tree from the above list must be associated to exactly one index
      location in the word. Maybe store this association somehow.

    - It stores a corresponding context-free derivation step: if v is the stored
      word, then it stores the derivation step u =>¹ v (single step)

    - It stores some kind of validity proof: For each variable in the stored word there is
      a corresponding derivation tree.

    Now, whenever we perform a recursive step, we need to update the structure
    accordingly. The word is updated. derivation tree elements are removed and added
    the association is updated: left / right shift of indexes depending on
    how the word length has changed and if we were to the right or left.
    Update the validity proofs / follow them from original correctness.-/
def ContextFreeDerivation.collectDerivationTreeNodes
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (cfd : @ContextFreeDerivation α nt G u v)
  (h_exhaustive : cfd.exhaustiveCondition)
  (h_not_same : u ≠ v):
  List (DerivationTree G × Finset.range u.len) := match h_constructor_cfd : cfd with
    | same h_same => by contradiction
    | @step _ _ _ _ u' _ dstep (derivation : ContextFreeDerivation G u' v) sound => by
      let rightSide := dstep.prod.val.rhs
      -- This returns all the nodes corresponding to the variables within the next derivations
      let allChildren : List (DerivationTree G × { x // x ∈ Finset.range (Word.len u') }) :=
        match h_constructor : derivation with
        | same h_same => []
        | @step α nt G _ u'' _ dstep' derivation' sound' => by
          have u'_comp := (ContextFreeDerivationStep.len_u_composition dstep').symm
          have derivation_exhaustive : derivation.exhaustiveCondition := by
            apply @ContextFreeDerivation.exhaustive_imp_child_exhaustive α nt G u v cfd h_exhaustive u' dstep derivation sound (by rw [h_constructor_cfd, h_constructor])
          exact (derivation.collectDerivationTreeNodes derivation_exhaustive (by
            have h_u'_has_var : ∃ symbol ∈ u', Sum.isLeft symbol := by
              have dstep'_var_in_u' : Sum.inl dstep'.prod.val.lhs ∈ u' := by
                have h_dstep'_sound : _ := dstep'.sound
                simp at h_dstep'_sound
                simp [h_dstep'_sound, Word.mem_mul_iff_or]
                apply Or.inl; apply Or.inr; tauto
              exists (Sum.inl dstep'.prod.val.lhs)
            have h_v_has_no_var : ¬ ∃ symbol ∈ v, Sum.isLeft symbol := by
              rw [exhaustiveCondition] at h_exhaustive
              apply not_exists_of_forall_not
              intro symbol
              have h_s_e : _ := h_exhaustive symbol
              rw [Decidable.not_and_iff_or_not_not']
              by_cases symbol ∈ v
              case pos h_pos =>
                apply h_s_e at h_pos
                apply Or.inr
                simp [h_pos]
              case neg h_neg =>
                apply Or.inl
                exact h_neg
            by_contra h_contra
            rw [h_contra] at h_u'_has_var
            contradiction))
      have u_comp := (ContextFreeDerivationStep.len_u_composition dstep).symm
      have var_len_1 : Word.len (Word.mk [@Sum.inl G.V G.Z dstep.prod.val.lhs]) = 1 := by
          simp [Word.len, Word.mk]
      have pre_len_less_u_len : dstep.pre.len < u.len := by
        rw [eq_iff_le_not_lt] at u_comp
        apply And.left at u_comp
        have var_len_1 : Word.len (Word.mk [@Sum.inl G.V G.Z dstep.prod.val.lhs]) = 1 := by
          simp [Word.len, Word.mk]
        rw [var_len_1, add_comm] at u_comp
        rw [← add_assoc] at u_comp
        apply Nat.lt_succ_of_le at u_comp
        apply Nat.lt_of_succ_lt_succ at u_comp
        rw [add_comm] at u_comp
        apply Nat.lt_sub_of_add_lt at u_comp
        exact @Nat.lt_of_lt_of_le (Word.len dstep.pre) (Word.len u - Word.len dstep.suf) (Word.len u) u_comp (by
          exact @Nat.sub_le (Word.len u) (Word.len dstep.suf))
      have u_comp := (ContextFreeDerivationStep.len_u_composition dstep).symm
      have suf_len_less_u_len : dstep.suf.len < u.len := by
        rw [eq_iff_le_not_lt] at u_comp
        apply And.left at u_comp
        rw [var_len_1, add_comm] at u_comp
        rw [← add_assoc] at u_comp
        apply Nat.lt_succ_of_le at u_comp
        apply Nat.lt_of_succ_lt_succ at u_comp
        apply Nat.lt_sub_of_add_lt at u_comp
        exact @Nat.lt_of_lt_of_le (Word.len dstep.suf) (Word.len u - Word.len dstep.pre) (Word.len u) u_comp (by
          exact @Nat.sub_le (Word.len u) (Word.len dstep.pre))
      -- Mark those areas to the outside of our relevant area
      let leftOfVarCount : Finset.range u.len := ⟨ dstep.pre.len, (by
        simp [pre_len_less_u_len])⟩
      let rightOfVarCount : Finset.range u.len := ⟨ dstep.suf.len, (by
        simp [suf_len_less_u_len])⟩
      let rhs_symbol_count : ℕ := dstep.prod.val.rhs.len
      have u'_eq_result : dstep.result = u' := by exact sound

      -- CASE DISTINCTION: ON rhs: is zero or more symbols
      cases h_num_vars_rhs : dstep.prod.val.rhs.len
      case zero =>
        let thisNode : DerivationTree G := DerivationTree.leaf none -- equivalent to ε
        have h_u_vs_u'_len : u'.len + 1 = u.len := by
          rw [u'_eq_result.symm, dstep.len_result_composition, u_comp.symm]
          rw [h_num_vars_rhs, var_len_1]
          simp [add_assoc, add_comm]
        have h_u_vs_u'_len₂ : u'.len ≤ u.len := by
          apply Nat.le_of_eq at h_u_vs_u'_len
          exact Nat.le_of_succ_le h_u_vs_u'_len
        have h_u_vs_u'_len₃ : u'.len < u.len := by
          apply Nat.le_of_eq at h_u_vs_u'_len
          exact Nat.lt_of_succ_le h_u_vs_u'_len
        let returnList : List (DerivationTree G × Finset.range u.len) := []
        -- add those left of var with no changes
        let returnLeft : List (DerivationTree G × Finset.range u.len) := by
            cases h_constructor_pre : dstep.pre
            case nil =>
              exact (@List.nil (DerivationTree G × Finset.range u.len))
            case cons =>
              let leftOfVarCount₂ : Finset.range (u'.len + 1) := ⟨ dstep.pre.len, (by
                simp
                rw [u'_eq_result.symm, dstep.len_result_composition]
                apply Nat.lt_of_succ_le
                rw [Nat.succ_eq_add_one]
                rw [Nat.add_comm (Word.len dstep.pre) (Word.len dstep.prod.val.rhs)]
                rw [Nat.add_assoc (Word.len dstep.prod.val.rhs) (Word.len dstep.pre) (Word.len dstep.suf)]
                rw [Nat.add_comm (Word.len dstep.pre) (Word.len dstep.suf)]
                simp [← Nat.add_assoc] )⟩
              -- foldl f z [a, b, c] = f (f (f z a) b) c
              exact List.foldl (fun prev (DT , index) =>
                let index₂ : Finset.range (u'.len + 1) := ⟨ index, (by
                  simp
                  have h_lt_u := index.2.out
                  simp at h_lt_u
                  apply lt_trans h_lt_u
                  apply Nat.lt_succ_self)⟩
                Decidable.by_cases
                -- Those that have an index smaller than the number of symbols left of var
                -- are at position before the variable area
                (fun h_lt : (index₂ < leftOfVarCount₂) =>
                  List.append prev [(DT , ⟨ index, by
                    apply Finset.mem_range.mpr
                    have h_leq₂ : (index : ℕ) < leftOfVarCount₂ := h_lt
                    apply lt_trans h_leq₂
                    simp [pre_len_less_u_len]⟩)])
                (fun h_ge : (¬ index₂ < leftOfVarCount₂) =>
                  prev) ) (@List.nil (DerivationTree G × Finset.range u.len)) allChildren
        let returnList := returnList ++ returnLeft

        -- index is the one after all left, i.e. var, and we use 0-get indexing
        let index : Finset.range u.len := leftOfVarCount
        -- add thisNode in the middle
        let returnList := returnList ++ [(thisNode , index)]
        -- add those right with shift by number
        -- the number of SYMBOLS that got generated additionally tells us
        -- by how much we need to adjust the variable count index
        -- for those variables to the right of the variable we transformed from
        let shiftBy : ℕ := 1
        let returnRight : List (DerivationTree G × Finset.range u.len) :=
          -- foldl f z [a, b, c] = f (f (f z a) b) c
          List.foldl (fun prev (DT , index) =>
            Decidable.by_cases
            -- Those that have an index to the right of Var
            -- need to be adjusted in their position by shiftBy
            (fun h_lt : (u'.len - rightOfVarCount < index) =>
              List.append prev [(DT , ⟨ index - shiftBy, by
                simp
                rw [h_u_vs_u'_len.symm]
                have h_index_lt_u'_len := index.2.out
                simp at h_index_lt_u'_len
                have h_shiftBy_le_index : shiftBy ≤ index := by
                  simp [shiftBy]
                  by_contra h_not
                  simp at h_not
                  rw [h_not] at h_lt
                  apply Nat.not_lt_zero at h_lt
                  exact h_lt
                rw [← Nat.add_one_sub_one (Word.len u' + 1)]
                rw [Nat.sub_lt_sub_iff_right h_shiftBy_le_index]
                apply Nat.lt_trans h_index_lt_u'_len
                tauto⟩)])
            (fun h_ge : (¬ u'.len - rightOfVarCount < index) =>
              prev)
          )
          (@List.nil (DerivationTree G × Finset.range u.len)) allChildren
        let returnList := returnList ++ returnRight
        exact returnList

      -- or at least one symbol in rhs
      case succ n =>
        have h_rhs_non_empty : 1 ≤ dstep.prod.val.rhs.len := by
          rw [h_num_vars_rhs]
          apply Nat.one_le_iff_ne_zero.mpr
          simp
        have h_u_vs_u'_len : u'.len = u.len + (rhs_symbol_count-1) := by
          have u_comp := (ContextFreeDerivationStep.len_u_composition dstep)
          have result_comp := (dstep.len_result_composition)
          simp [← u'_eq_result, u_comp, result_comp]
          have lhs_len : (Word.mk [@Sum.inl G.V G.Z dstep.prod.val.lhs]).len = 1 := by
            simp [Word.mk, Word.len]
          have rhs_comp : Word.len (dstep.prod.val.rhs) = 1 + (rhs_symbol_count-1) := by
            simp [rhs_symbol_count, lhs_len]
            rw [add_comm, Nat.sub_add_cancel]
            exact h_rhs_non_empty
          rw [rhs_comp]
          rw [lhs_len]
          rw [add_assoc (Word.len dstep.pre + 1) (Word.len dstep.suf) (rhs_symbol_count-1)]
          rw [add_comm (Word.len dstep.suf) (rhs_symbol_count-1)]
          repeat rw [add_assoc]
        -- Only those variable-nodes are children of this node, that result from
        -- this exact derivation step
        have h_u_vs_u'_len₂ : u.len ≤ u'.len := by
          rw [h_u_vs_u'_len]
          simp
        have u_range_subset_u'_range : (Finset.range u.len) ⊆ (Finset.range u'.len) := by
          apply Finset.range_subset.mpr
          exact h_u_vs_u'_len₂
        let leftOfVarCount₂ : Finset.range u'.len := ⟨leftOfVarCount , (by
          simp [Nat.lt_of_lt_of_le pre_len_less_u_len h_u_vs_u'_len₂] )⟩

        let fun_find_allChildren_with_index (index₁ : Finset.range (Word.len u')) (h_index_valid : ∃ location  ∈ allChildren, location.2 = index₁) : (DerivationTree G) :=
          let afunc : List (DerivationTree G × { x // x ∈ Finset.range (Word.len u') }) →
                      (DerivationTree G × { x // x ∈ Finset.range (Word.len u') }) →
                      List (DerivationTree G × { x // x ∈ Finset.range (Word.len u') }) :=
              (fun prev (DT , index₂) =>
              dite (index₁ = index₂)
              (fun h_is : index₁ = index₂ =>
                prev ++ [(DT, index₂)])
              (fun h_is_not : index₁ ≠ index₂ =>
                prev) )
          have afuncDef : afunc =
              (fun prev (DT , index₂) =>
              dite (index₁ = index₂)
              (fun h_is : index₁ = index₂ =>
                prev ++ [(DT, index₂)])
              (fun h_is_not : index₁ ≠ index₂ =>
                prev) ) := by tauto
          let a : _ := List.foldl afunc [] allChildren
          have aDef : a = List.foldl afunc [] allChildren := by simp
          have afunc_monotone : ∀ list₁ list₂ : List _, list₁ ≠ [] → List.foldl afunc list₁ list₂ ≠ [] := by
            intro list₁ list₂
            induction list₁
            case nil =>
              tauto
            case cons head₁ tail₁ ind_hyp₁ =>
              induction list₂
              case nil =>
                tauto
              case cons head₂ tail₂ ind_hyp₂ =>
                intro h_head_tail_neq_nil
                by_cases tail₂ ≠ []
                case pos h_pos₂ =>
                  by_cases tail₁ ≠ []
                  case pos h_pos₁ =>
                    simp [h_pos₁] at ind_hyp₂
                    simp [h_pos₁] at ind_hyp₁

                    rw [List.foldl_cons]

                    simp [afuncDef]
                    by_cases index₁ = head₂.2
                    case pos h_pos_head₂ =>
                      sorry
                    --#check ite_cond_eq_true
                    /-ite_cond_eq_true.{u} {α : Sort u} {c : Prop}
                    {x✝ : Decidable c} (a b : α) (h : c = True) :
                    (if c then a else b) = a-/
                    case neg h_neg_head₂ =>
                      sorry
                  case neg h_neg₁ =>
                    sorry
                case neg h_neg₂ =>

                  sorry
          let b : DerivationTree G × { x // x ∈ Finset.range (Word.len u') } := a[0]'(by
            -- use h_index_valid

            apply Nat.zero_lt_of_ne_zero
            rw [ne_eq (List.length a) 0]
            rw [List.length_eq_zero]
            have proof_condition : List.foldl afunc [] allChildren = [] ↔ ¬ ∃ location ∈ allChildren, location.2 = index₁ := by
              induction allChildren
              case nil =>
                tauto
              case cons head tail ind_hyp =>
                apply Iff.intro
                case mp =>
                  intro h_nil
                  simp
                  rw [not_or]
                  simp at h_nil
                  simp [afuncDef] at h_nil
                  by_cases index₁ = head.2
                  case pos h_is =>
                    simp [h_is, List.foldl] at h_nil
                    absurd h_nil
                    sorry
                  case neg h_isnot =>
                    sorry
                case mpr =>
                  sorry
            rw [proof_condition, not_not]
            exact h_index_valid )
          b.1

        let current_u'_index : Finset.range u'.len := leftOfVarCount₂
        let childrenDT : List (DerivationTree G) :=
          -- foldl f z [a, b, c] = f (f (f z a) b) c
          --let a : List { x // x ∈ Finset.range (Word.len rightSide) } := Fintype.ofFinset (Finset.range (rightSide.len))
          --let b : _ := a.toList
          @List.foldl _ (Fin (rightSide.len)) (fun prev (index : Fin (Word.len rightSide)) =>
            let symbol : _ := Word.get rightSide index
            Decidable.by_cases
            (fun h_var : Sum.isLeft symbol =>
              let child : DerivationTree G :=
                let index₂ : Finset.range (Word.len u') := ⟨index, by
                  have rightSideDef : rightSide = dstep.prod.val.rhs := by tauto
                  simp
                  rw [u'_eq_result.symm, dstep.len_result_composition]
                  rw [add_comm (Word.len dstep.pre) _]
                  rw [add_assoc]

                  apply @Nat.lt_of_lt_of_le index (Word.len dstep.prod.val.rhs) _ (by
                    --rw [rightSideDef] at index
                    --have proof : index < (Word.len dstep.prod.val.rhs) := by
                    apply Nat.lt_of_le_of_ne
                    case h₁ =>
                      apply Finset.mem_range_le
                      simp
                    case h₂ =>
                      by_contra h_not
                      have rhs_not : _ := @Finset.not_mem_range_self (Word.len dstep.prod.val.rhs)
                      nth_rewrite 1 [h_not.symm] at rhs_not
                      have index_range : ↑index ∈ Finset.range (Word.len (dstep.prod.val.rhs)) := by simp
                      apply Not.intro rhs_not index_range) (_ : Word.len rightSide ≤ Word.len dstep.prod.val.rhs + (Word.len dstep.pre + Word.len dstep.suf))
                  rw [rightSideDef]
                  apply Nat.le_add_right ⟩
                fun_find_allChildren_with_index index₂ (by
                  -- TODO require side condition proof
                  sorry)
              prev ++ [child]
              )
            (fun h_terminal : ¬ Sum.isLeft symbol =>

              let symbol₂ := symbol.getRight (by simp at h_terminal; exact h_terminal)
              let child : DerivationTree G := DerivationTree.leaf (some symbol₂)
              prev ++ [child]))
            (@List.nil (DerivationTree G))
            (List.finRange (rightSide.len))


        -- extract the correct NEPDTL
        let children : NEPreDerivationTreeList G := sorry
        -- Construct the relevant parts for this node specifically
        let var := dstep.prod.val.lhs
        let var_as_word : (Word (G.V ⊕ G.Z)) := Word.mk [Sum.inl var]
        let rule : G.productions := dstep.prod
        let h_rule_lhs : rule.1.lhs = var := by simp
        let h_rule_rhs : rule.1.rhs = NEPreDerivationTreeList.levelWord children := sorry
        let childrenValid : children.treeValid := sorry
        let thisNode := DerivationTree.inner var children rule h_rule_lhs h_rule_rhs childrenValid


        let returnList : List (DerivationTree G × Finset.range u.len) := []
        -- add those left of var with no changes
        let returnLeft : List (DerivationTree G × Finset.range u.len) :=
          -- foldl f z [a, b, c] = f (f (f z a) b) c
          List.foldl (fun prev (DT , index) =>
            Decidable.by_cases
            -- Those that have an index smaller than the number of symbols left of var
            -- are at position before the variable area
            (fun h_lt : (index < leftOfVarCount₂) =>
              List.append prev [(DT , ⟨ index, by
                apply Finset.mem_range.mpr
                have h_leq₂ : (index : ℕ) < leftOfVarCount₂ := h_lt
                apply lt_trans h_leq₂
                simp [pre_len_less_u_len]⟩)])
            (fun h_ge : (¬ index < leftOfVarCount₂) =>
              prev)
          )
          (@List.nil (DerivationTree G × Finset.range u.len)) allChildren
        let returnList := returnList ++ returnLeft

        -- index is the one after all left, i.e. var, and we use 0-get indexing
        let index : Finset.range u.len := leftOfVarCount
        -- add thisNode in the middle
        let returnList := returnList ++ [(thisNode , index)]
        -- add those right with shift by number
        -- the number of SYMBOLS that got generated additionally tells us
        -- by how much we need to adjust the variable count index
        -- for those variables to the right of the variable we transformed from
        let shiftBy : Finset.range u'.len := ⟨ rhs_symbol_count - 1 , by
          simp [h_u_vs_u'_len, u_comp.symm]
          simp [Word.mk, Word.len]
        ⟩
        let returnRight : List (DerivationTree G × Finset.range u.len) :=
          -- foldl f z [a, b, c] = f (f (f z a) b) c
          List.foldl (fun prev (DT , index) =>
            Decidable.by_cases
            -- Those that have an index to the right of Var
            -- need to be adjusted in their position by shiftBy
            (fun h_lt : (u'.len - rightOfVarCount < index) =>
              List.append prev [(DT , ⟨ index - shiftBy, by
                simp
                have h_lt₂ : Word.len u + (rhs_symbol_count - 1) - ↑rightOfVarCount < ↑index := by
                  rw [h_u_vs_u'_len.symm]
                  exact h_lt
                have ind_lt_u' : index < u'.len := Finset.mem_range.mp index.2
                have h_rhs_vs_u' : (rhs_symbol_count - 1) ≤ u'.len := by
                  rw [h_u_vs_u'_len]
                  exact Nat.le_add_left _ _
                have h_u'_rhs_vs_u : Word.len u' - (rhs_symbol_count -1) = Word.len u := by
                  exact (@Nat.sub_eq_iff_eq_add (rhs_symbol_count - 1) u'.len u.len h_rhs_vs_u').mpr h_u_vs_u'_len
                rw [h_u'_rhs_vs_u.symm]
                apply Nat.lt_sub_iff_add_lt.mpr
                have h_rhs_lt_index : (rhs_symbol_count - 1) ≤ index := by
                  simp [rightOfVarCount] at h_lt
                  simp [rhs_symbol_count]
                  simp [rhs_symbol_count] at h_rhs_vs_u'
                  --rw [(Nat.sub_add_cancel _)]
                  have h_u'_right_comp : u'.len - rightOfVarCount = Word.len dstep.pre + Word.len dstep.prod.val.rhs := by
                    simp [rightOfVarCount]
                    rw [u'_eq_result.symm, dstep.len_result_composition]
                    simp
                  rw [h_u'_right_comp] at h_lt
                  simp
                  rw [(Nat.succ_eq_add_one _).symm]
                  rw [add_comm] at h_lt
                  apply Nat.lt_sub_of_add_lt at h_lt
                  --apply Nat.le_succ
                  have h_lt₃ : Word.len dstep.prod.val.rhs < index := by
                    apply Nat.le_trans h_lt (_ : index - (Word.len dstep.pre) ≤ index)
                    exact Nat.sub_le _ _
                  apply Nat.lt_succ_of_lt at h_lt₃
                  exact Nat.le_of_lt h_lt₃
                rw [Nat.sub_add_cancel (h_rhs_lt_index)]
                exact ind_lt_u'
                ⟩)])
            (fun h_ge : (¬ u'.len - rightOfVarCount < index) =>
              prev)
          )
          (@List.nil (DerivationTree G × Finset.range u.len)) allChildren
        let returnList := returnList ++ returnRight
        exact returnList


/--Return a derivation tree version of this CFD-/
def ContextFreeDerivation.toDerivationTree
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (cfd : @ContextFreeDerivation α nt G u v)
  (h_exhaustive : cfd.exhaustiveCondition)
  (h_starts_in_1 : cfd.startsIn1Condition) :
  DerivationTree G :=
    match h_constructor : cfd with
    | same h_same => sorry
    | @step _ _ _ _ u' _ dstep derivation sound => by
      exact ((ContextFreeDerivation.collectDerivationTreeNodes cfd h_exhaustive sorry)[0]'sorry).fst

/--Theorem: The toDerivation function provides derivation trees, whose
  results correspond to the CFDs result.-/
theorem ContextFreeDerivation.toDerivationTree_respects_result
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (cfd : @ContextFreeDerivation α nt G u v) :
  ∀ p₁ p₂, DerivationTree.result (cfd.toDerivationTree p₁ p₂) = v.VZtoZ p₁ := by
    sorry

/--Theorem: The toDerivation function provides derivation trees, which
  start in the same symbol the CFD started in.-/
theorem ContextFreeDerivation.toDerivationTree_respects_start
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  [DecidableEq G.V]
  (cfd : @ContextFreeDerivation α nt G u v) (startSymbol : G.V) (h_u_is_startSymbol : u = [Sum.inl startSymbol]):
  ∀ p₁ p₂, ∀ p₃ : (cfd.toDerivationTree p₁ p₂).isTotal, DerivationTree.startingSymbol p₃ = startSymbol := by
    sorry

/--Convert an exhaustive CFD into a derivation tree-/
def ExhaustiveContextFreeDerivation.toDerivationTree
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (ecfd : @ExhaustiveContextFreeDerivation α nt G u v) :
  DerivationTree G :=
    ecfd.derivation.toDerivationTree ecfd.exhaustive ecfd.startsIn1

/-
--I originally considered building the CFD by collecting the production rules
--of the DT. This only works if we assume left- or right-first derivation.
def ExhaustiveContextFreeDerivation.fromProdRuleList
  {G : ContextFreeGrammar α nt}
  (startWord : Word (G.V ⊕ G.Z))
  (endWord : Word (G.V ⊕ G.Z))
  (prodRules : List G.productions) :
  ExhaustiveContextFreeDerivation startWord endWord :=
    sorry
-/

/--Construct an exhaustive CFD from a derivation tree. (The exhaustiveness is given
  us for free due to it being a DT.) This function cannot succeed: I wrote
  CFD.concat for this, but cannot use it due to the result of a CFD being encoded
  in the type. This makes it impossible to concat a number of CFDs where the
  number is unknown at compile time (the number depends on the number of children
  of a derivation tree). Do not attempt to code this function before refactoring
  derivations (definetly context-free, possibly generic and regular also): Move
  the result word to an attribute or add a wrapper type.
-/
def DerivationTree.toExhaustiveContextFreeDerivation
  {G : ContextFreeGrammar α nt}
  [DecidableEq G.V]
  (DT : DerivationTree G) :
  (@ExhaustiveContextFreeDerivation α nt G DT.fromAny (@Word.ZtoVZ _ _ _ _ G DT.result)) :=
    --ExhaustiveContextFreeDerivation.fromProdRuleList DT.fromAny (@Word.ZtoVZ _ _ _ _ G DT.result) DT.collect_prodRules
    match h_constructor : DT.tree with
    | .leaf tw =>
      match tw with
      | none =>
        -- Epsilon: CFD hat das aber nicht als base case!
        sorry
      | some terminalSymbol =>
        { derivation := .same (by
            simp [result, PreDerivationTree.result, h_constructor]
            simp [fromAny, h_constructor]
            rfl),
          exhaustive := (by
            rw [ContextFreeDerivation.exhaustiveCondition]
            rw [result]
            rw [h_constructor]
            rw [PreDerivationTree.result]
            rw [Word.ZtoVZ]
            intro symbol
            intro symbol_mem
            simp at symbol_mem
            rw [List.mem_map] at symbol_mem
            have any : ∀ (a : { x // x ∈ G.Z }),
              a ∈ [terminalSymbol]
              ∧ Sum.inr a = symbol → Sum.isRight symbol = true := by
                intro a a_mem
                cases a
                rw [← a_mem.right]
                simp
            apply Exists.elim symbol_mem any),
          startsIn1 := by
            rw [ContextFreeDerivation.startsIn1Condition]
            simp [fromAny, h_constructor]
            tauto
            }
    | .inner v c r =>
      let children := DT.children
      -- The below is not possible due to the resulting list having to contain
      -- elements with multiple different types: ECFD a b vs ECFD c d
      --let children_derivations : List _ :=
      -- List.map.{u, v} {α : Type u} {β : Type v} (f : α → β) (a✝ : List α) : List β
        --@List.map (DerivationTree G) (ExhaustiveContextFreeDerivation _ _) (fun child => child.toExhaustiveContextFreeDerivation) children
      let step : ContextFreeDerivationStep G DT.fromAny :=
        -- result should be result of current rule
        { prod := r,
          pre := ε,
          suf := ε,
          sound := by
            simp [fromAny, h_constructor]
            have valid := DT.valid;
            rw [h_constructor, PreDerivationTree.treeValid] at valid;
            rw [valid.left]
        }
      -- Konstruiere mithilfe von CFD.concat plus Rekursion
      -- die Ableitung
      -- Problem: Typen passen nicht zusammen d.h. foldl nicht anwendbar
      -- Außerdem: Reihenfolge der Kinder unpraktisch
      let derivation : ContextFreeDerivation G step.result DT.result.ZtoVZ :=
        --Order of children not guaranteed
        sorry
      { derivation :=
          .step
          step
          derivation
          (by simp [step, Grammar.DerivationStep.result, ContextFreeDerivationStep.result, ContextFreeProduction.toProduction])
          ,
        exhaustive := sorry,
        startsIn1 := sorry}

end ContextFreeGrammar
