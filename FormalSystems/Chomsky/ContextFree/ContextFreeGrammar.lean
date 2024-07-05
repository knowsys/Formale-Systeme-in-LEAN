import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Tauto
--import Mathlib.Data.Fold

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

--=============================================================
-- Section: Context Free Grammar and Step
--=============================================================

/--Define Context Free Grammars to have context free production rules.-/
def ContextFreeGrammar (α nt: Type) := @Grammar α nt (ContextFreeProduction) _

variable { CFProd: Finset α → Finset nt → Type } [Production.ContextFree α nt CFProd]

/--Define Context Free Grammars to be Grammars.-/
instance : Coe (ContextFreeGrammar α nt) (@Grammar α nt GenericProduction _) where
  coe g := { g with
    productions := g.productions.map ContextFreeProduction.toProduction
  }

namespace ContextFreeGrammar

/--Structure: The CFDerivationStep starting in`u`. Structure has four attributes:

  - `prod` - store the production rule that were used in the derivation step.

  - `pre`,`suf` - `u = pre * x * suf`

  - `sound` - Show the soundness of a derivation step by proving
  the equality`u = pre * x * suf`and showing that x appears on the left side of the
  production rule`prod`.-/
structure ContextFreeDerivationStep (G : ContextFreeGrammar α nt) (u: Word (G.V ⊕ G.Z)) where
  /--The grammars production applicable in this derivation step.-/
  prod: G.productions
  /--The symbols to the left of the non-terminal symbol we produce from.-/
  pre: Word (G.V ⊕ G.Z)
  /--The symbols to the right of the non-terminal symbol we produce from.-/
  suf: Word (G.V ⊕ G.Z)
  /--A proof that the production rules are applicable to the variable
  that is encased in the left side of the derivation step, and of the inclusion
  of this variable.-/
  sound:
    have x : G.V := ContextFreeProduction.lhs prod.val -- need to ensure correct alphabet : Z+V
    have x_as_word : (Word (G.V ⊕ G.Z)) := [.inl ↑(x)]
    u = pre * x_as_word * suf
  deriving DecidableEq

/--Theorem: A context free derivation step on a word u has a word of length 1 within u (the variable we are deriving from).-/
theorem ContextFreeDerivationStep_has_pre_1_suf_word_as_u (step : ContextFreeDerivationStep G (u : Word (G.V ⊕ G.Z))) : ∃x : Word (G.V ⊕ G.Z), x.len=1 ∧ u = step.pre * x * step.suf := by
  apply Exists.intro
  case w =>
    exact (Word.mk [Sum.inl (↑step.prod : ContextFreeProduction G.Z G.V).lhs])
  case h =>
    apply And.intro
    case left =>
        rfl
    case right =>
      exact step.sound

/--Define a coercion of context free derivation steps into generic derivation steps.-/
instance : Coe (@ContextFreeDerivationStep α nt G u) (@Grammar.DerivationStep α nt GenericProduction _ (↑G) u) where
  coe cfDerivationStep := { cfDerivationStep with
    prod :=
    {
      val := ContextFreeProduction.toProduction cfDerivationStep.prod.val
      property := by simp
    } : @Grammar.DerivationStep α nt GenericProduction _ (↑G : Grammar GenericProduction) u
  }

--Taken directly from Grammar version
/--Construct a derivation step to have been applied to a left-side longer string.-/
def ContextFreeDerivationStep.augment_left (step: ContextFreeDerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  ContextFreeDerivationStep G (w * u) :=
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

--Taken directly from Grammar version
/--Construct a derivation step to have been applied to a right-side longer string.-/
def ContextFreeDerivationStep.augment_right (step: ContextFreeDerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  ContextFreeDerivationStep G (u * w) :=
  {
    prod := step.prod,
    pre := step.pre,
    suf := step.suf * w,
    sound := by
      simp [mul_assoc]
      have t := step.sound
      simp [← mul_assoc] at t
      simp [← mul_assoc]
      exact t
  }

/--Define result of a derivation step as the result of applying
  the production rule to the variable within the pre- and suffix.-/
def ContextFreeDerivationStep.result (step : @ContextFreeDerivationStep α nt G u) : Word (G.V ⊕ G.Z) :=
  @Grammar.DerivationStep.result α nt GenericProduction _ G u step

--Taken directly from Grammar version
/--Theorem: Left-augmenting (adding a word to the left of) the input
  string of a derivation step changes its result as expected.-/
theorem ContextFreeDerivationStep.augment_left_result (step: ContextFreeDerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  (step.augment_left w).result = w * step.result := by
  unfold ContextFreeDerivationStep.result
  unfold Grammar.DerivationStep.result
  unfold augment_left
  simp [mul_assoc]

--Taken directly from Grammar version
/--Theorem: Right-augmenting (adding a word to the left of) the input
  string of a derivation step changes its result as expected.-/
theorem ContextFreeDerivationStep.augment_right_result (step: ContextFreeDerivationStep G u) (w: Word (G.V ⊕ G.Z)):
  (step.augment_right w).result = step.result * w:= by
  unfold ContextFreeDerivationStep.result
  unfold Grammar.DerivationStep.result
  unfold augment_right
  simp [mul_assoc]

/-Theorem: The origin for a derivation steps length is the addition of the lengths of the prefix, variable and sufix.-/
theorem ContextFreeDerivationStep.len_u_composition (step: ContextFreeDerivationStep G u) : u.len = step.pre.len + (Word.mk [@Sum.inl G.V G.Z step.prod.val.lhs]).len + step.suf.len := by
  have sound : _ := step.sound
  simp at sound
  simp [Word.length_add_eq_mul, sound]
  rw [Word.length_mul_eq_add, Word.length_mul_eq_add]
  rfl

/--Theorem: If the right side isn't empty, then length of lhs is less or equal to the rhs of a production rule.-/
theorem ContextFreeProduction.oneElem
  (prod : ContextFreeProduction Z V)
  (h_rhs_non_empty : 1 ≤ prod.rhs.len)
  : (Word.mk [@Sum.inl V Z prod.lhs]).len ≤ prod.rhs.len := by
  simp [Word.mk_from_list_len, List.length]
  exact h_rhs_non_empty

/--Theorem: If the right side isn't empty, then the length of the word weakly increases along derivation steps.-/
theorem ContextFreeDerivationStep.sizeMonotoneIncreasing
  (step: ContextFreeDerivationStep G u)
  (h_rhs_non_empty : 1 ≤ step.prod.val.rhs.len)
  : u.len ≤ step.result.len := by
  rw [ContextFreeDerivationStep.result, step.len_u_composition]
  simp [Word.length_mul_eq_add, Grammar.DerivationStep.result, Word.mk_from_list_len, List.length]
  exact h_rhs_non_empty

/-Theorem: The origin for a derivation steps length is the addition of the lengths of the prefix, variable and sufix.-/
theorem ContextFreeDerivationStep.len_result_composition (step : ContextFreeDerivationStep G u)
  : step.result.len = step.pre.len + step.prod.val.rhs.len + step.suf.len := by
  have sound : _ := step.sound
  simp at sound
  simp [Word.length_add_eq_mul, sound, ContextFreeDerivationStep.result, Grammar.DerivationStep.result]
  rfl

--=============================================================
-- Section: PreDerivationTree and NEPreDerivationTreeList
--=============================================================

--Note: Need to name all type parameters explicitly for coercion to work!

--variable {CFDS : (@ContextFreeDerivationStep α nt G u)}
--#check ((↑CFDS) : @Grammar.DerivationStep α nt GenericProduction _ (↑G) u).result

--Idea: Split everything up into many sub-tasks
mutual
/--Basic structure of a context-free derivation tree without validity-constraints. Values returned by all sub-defined functions are only
  ordered correctly if ordered correctly during definition.-/
inductive PreDerivationTree (G : ContextFreeGrammar α nt)
  | leaf (terminal : WithOne G.Z) : PreDerivationTree G
  | inner (var : G.V) (children : NEPreDerivationTreeList G) (prodRule : (G.productions)) : PreDerivationTree G
--                                                  → (children_non_empty : 0 < List.length (↑children)) -- children is recursively bound => doesn't work
-- We cannot ensure a non-empty children list with parameter as above or subclass (because it is the recursive argument)
-- Thus we define this inductive structure in parallel to ensure non-emptiness
/--Ensure that we have a non-empty list of children with this structure.-/
inductive NEPreDerivationTreeList (G : ContextFreeGrammar α nt)
  | single (PDT : PreDerivationTree G) : NEPreDerivationTreeList G
  | cons (PDT : PreDerivationTree G) (NEPDTL : NEPreDerivationTreeList G) : NEPreDerivationTreeList G
end

mutual

/--Define the equality determinating relation.-/
def PreDerivationTree.decEq {G : ContextFreeGrammar α nt} [eq₁ : DecidableEq α] [eq₂ : DecidableEq nt] : (PDT₁ PDT₂ : PreDerivationTree G) → Decidable (Eq PDT₁ PDT₂)
| .leaf terminal₁ , .leaf terminal₂ =>
  match terminal₁, terminal₂ with
  | none, none =>
    isTrue (by rfl)
  | some terminalSymbol₁, none =>
    isFalse (by simp)
  | none, some terminalSymbol₂ =>
    isFalse (by simp)
  | some terminalSymbol₁, some terminalSymbol₂ =>
    match (eq₁ terminalSymbol₁ terminalSymbol₂) with
      | isTrue h_isTrue => isTrue (by rw [Subtype.val_inj] at h_isTrue; rw [h_isTrue])
      | isFalse h_isFalse => isFalse (by
          apply Not.intro
          intro h_not
          simp at h_not
          rw [Subtype.val_inj] at h_isFalse
          rw [Option.some_inj] at h_not
          contradiction)
| .leaf terminal₁ , .inner _ _ _ =>
  isFalse (by
    apply Not.intro
    intro h_not
    contradiction)
| .inner _ _ _ , .leaf terminal₂ =>
  isFalse (by
    apply Not.intro
    intro h_not
    contradiction)
| .inner var₁ children₁ prodRule₁, .inner var₂ children₂ prodRule₂ =>
  match (prodRule₁.val.decEq prodRule₂.val) with
    | isFalse h_isFalse => isFalse (by simp; intro _ _ ; rw [Subtype.val_inj] at h_isFalse; exact h_isFalse)
    | isTrue h_isTrue_prodRule =>
      match (children₁.decEq children₂) with
        | isFalse h_isFalse => isFalse (by simp; intro _ _; contradiction)
        | isTrue h_isTrue_children =>
          match (decEq var₁ var₂) with
            | isFalse h_isFalse => isFalse (by
              intro h_not;
              --rw [h_isTrue_children, h_isTrue_prodRule] at h_not
              simp [h_isTrue_children, h_isTrue_prodRule, Subtype.val_inj] at h_not
              apply And.left at h_not
              rw [h_not] at h_isFalse
              contradiction)
            | isTrue h_isTrue_var => isTrue (by
              rw [Subtype.val_inj] at h_isTrue_prodRule
              rw [h_isTrue_prodRule, h_isTrue_children, h_isTrue_var])

/--Define the equality determinating relation.-/
def NEPreDerivationTreeList.decEq {G : ContextFreeGrammar α nt} [DecidableEq α] [DecidableEq nt] : (NEPDT₁ NEPDT₂ : NEPreDerivationTreeList G) → Decidable (NEPDT₁ = NEPDT₂)
| .single PDT₁ , .single PDT₂ => match (PDT₁.decEq PDT₂) with
  | isTrue h_isTrue_PDT => isTrue (by rw [h_isTrue_PDT])
  | isFalse h_isFalse_PDT => isFalse (by simp; exact h_isFalse_PDT)
| .single _ , .cons _ _ => isFalse (by
    apply Not.intro
    intro h_not
    contradiction)
| .cons _ _ , .single _ => isFalse (by
    apply Not.intro
    intro h_not
    contradiction)
| .cons PDT₁ NEPDTL₃, .cons PDT₂ NEPDTL₄ =>
  match (PDT₁.decEq PDT₂) with
    | isFalse h_isFalse_PDT => isFalse (by
      simp
      intro h_PDT_equal
      contradiction)
    | isTrue h_isTrue_PDT =>
      match (NEPDTL₃.decEq NEPDTL₄) with
      | isFalse h_isFalse_NEPDTL => isFalse (by
        simp; intro _
        exact h_isFalse_NEPDTL)
      | isTrue h_isTrue_NEPDTL => isTrue (by rw [h_isTrue_PDT, h_isTrue_NEPDTL])

end

/--Equality is decidable for PDTs using the decEq function.-/
instance [DecidableEq α] [DecidableEq nt] : DecidableEq (@PreDerivationTree α nt G) := PreDerivationTree.decEq
/--Equality is decidable for NEPDTLs using the decEq function.-/
instance [DecidableEq α] [DecidableEq nt] : DecidableEq (@NEPreDerivationTreeList α nt G) := NEPreDerivationTreeList.decEq

/--Define syntax for NEPreDerivationTreeLists: `DT[...]`-/
syntax "DT[" term,+ "]" : term
macro_rules
  | `(DT[$x])    => `(NEPreDerivationTreeList.single $x)
  | `(DT[ $x₁, $xs,*]) => `(NEPreDerivationTreeList.cons $x₁ DT[$xs,*])

/--Convert to a List (PreDerivationTree G). Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.asList (NEPDTL : NEPreDerivationTreeList G) : List (PreDerivationTree G) := match NEPDTL with
  | single PDT => [PDT]
  | cons (PDT) (NEPDTL₂) => PDT :: NEPDTL₂.asList

/--Folds a function over a non-empty pre-derivation tree list from the left:
`foldl f z NEPDT(a, b, c) = f (f (f z a) b) c`-/
@[specialize]
def NEPreDerivationTreeList.foldl {G : ContextFreeGrammar α nt} {α : Type u} (f : α → (PreDerivationTree G) → α) : (init : α) → (NEPreDerivationTreeList G) → α
  | a, single PDT => f a PDT
  | a, cons PDT NEPDTL₂ => NEPreDerivationTreeList.foldl f (f a PDT) NEPDTL₂

/--Theorem: The lists constructed with asList are never [].-/
theorem NEPreDerivationTreeList.asList_never_nil (NEPDTL : NEPreDerivationTreeList G) : ¬ NEPDTL.asList = [] := by
  apply Not.intro
  intro h
  cases NEPDTL
  repeat rw [NEPreDerivationTreeList.asList] at h; contradiction

/--Theorem: The lists constructed with asList have non-zero length.-/
theorem NEPreDerivationTreeList.asList_length (NEPDTL : NEPreDerivationTreeList G) : NEPDTL.asList.length > 0 := by
  apply List.length_pos_of_ne_nil NEPDTL.asList_never_nil

mutual
/--Return a list of the context-free node's children. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.nodeList {G : ContextFreeGrammar α nt} (NEPDT : NEPreDerivationTreeList G) : List (PreDerivationTree G) := match (NEPDT : NEPreDerivationTreeList G) with
  | .single PDT => PDT.nodeList
  | .cons PDT NEPDT₂ => PDT.nodeList ++ NEPDT₂.nodeList -- NEPreDerivationTreeList.foldl (fun prev tree => tree.nodeList ++ prev) [PDT] NEPDT
/--Return a list of the context-free node's children. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.nodeList {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) : List (PreDerivationTree G) := match (PDT : PreDerivationTree G) with
  | .leaf _ => [PDT]
  | .inner _ children _ => PDT :: children.nodeList
end

mutual
/--Theorem: The list of nodes returned with nodeList is never empty.-/
theorem NEPreDerivationTreeList.nodeList_never_nil
  {G : ContextFreeGrammar α nt} (NEPDT : NEPreDerivationTreeList G) :
  ¬ NEPDT.nodeList = [] := by
    intro h_not
    cases NEPDT
    case single PDT =>
      rw [NEPreDerivationTreeList.nodeList] at h_not
      --have h_not_contra : _ := by PDT.nodeList_never_nil
      have h_not_not : _ := PDT.nodeList_never_nil
      contradiction
    case cons PDT NEPDT₂ =>
      rw [NEPreDerivationTreeList.nodeList] at h_not
      have h_not_not : _ := List.append_ne_nil_of_left_ne_nil (PDT.nodeList) (NEPDT₂.nodeList) (PDT.nodeList_never_nil)
      contradiction
/--Theorem: The list of nodes returned with nodeList is never empty.-/
theorem PreDerivationTree.nodeList_never_nil
  {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) :
  ¬ PDT.nodeList = [] := by
    intro h_not
    cases PDT
    case leaf _ r =>
      rw [PreDerivationTree.nodeList] at h_not
      contradiction
    case inner _ children rule r =>
      rw [PreDerivationTree.nodeList] at h_not
      have _ : _ := List.cons_ne_nil (PreDerivationTree.inner children rule r) (NEPreDerivationTreeList.nodeList rule)
      contradiction
end

/--Return a (possibly empty) list of this nodes children. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.children {G : ContextFreeGrammar α nt} : (PDT : (PreDerivationTree G)) → List (PreDerivationTree G)
  | leaf _ => []
  | inner _ children _ => children.asList

mutual
/--Get the list of used production rules. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.prodRuleList {G : ContextFreeGrammar α nt} : (PreDerivationTree G) → List (G.productions)
  | .leaf _ => []
  | .inner _ children prodRule => prodRule :: children.prodRuleList
/--Get the list of used production rules. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.prodRuleList {G : ContextFreeGrammar α nt} : (NEPDT : (NEPreDerivationTreeList G)) → List (G.productions)
  | .single PDT => PDT.prodRuleList
  | .cons PDT NEPDT₂ => PDT.prodRuleList ++ NEPDT₂.prodRuleList
end

mutual
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.result {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Word (G.Z)
  | .leaf terminal =>
    match terminal with
    | none =>
      ε
    | some terminalSymbol =>
      Word.mk [terminalSymbol]
  | .inner _ children _ => children.result
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.result {G : ContextFreeGrammar α nt} : (NEPDT : NEPreDerivationTreeList G) → Word (G.Z)
  | .single PDT => PDT.result
  | .cons PDT NEPDT₂ => Word.concatListOfWords [PDT.result , NEPDT₂.result]
end

mutual
/--The intermediate level word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.levelWord {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Word (G.V ⊕ G.Z)
  | .leaf terminal =>
    match terminal with
    | none =>
      ε
    | some terminalSymbol =>
      Word.mk [Sum.inr terminalSymbol]
  | .inner var _ _ => Word.mk [(Sum.inl var)]
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.levelWord {G : ContextFreeGrammar α nt} : (NEPDT : NEPreDerivationTreeList G) → Word (G.V ⊕ G.Z)
  | .single PDT => PDT.levelWord
  | .cons PDT NEPDT₂ => Word.concatListOfWords [PDT.levelWord , NEPDT₂.levelWord]
end

mutual
/--Define the depth of a context-free derivation-tree.-/
def PreDerivationTree.depth {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) -> Nat
  | .leaf _ => 0
  | .inner _ children _ => children.depth + 1
/--Define the depth of a context-free derivation-tree.-/
def NEPreDerivationTreeList.depth {G : ContextFreeGrammar α nt} : (NEPDT : NEPreDerivationTreeList G) -> Nat
  | .single PDT => PDT.depth
  | .cons PDT NEPDT₂ => Nat.max PDT.depth NEPDT₂.depth
end

/--Collect the nodelists of PDTs one by one.-/
def append_nodeLists (prev : List (PreDerivationTree G)) (next : PreDerivationTree G) : (List (PreDerivationTree G)) :=
  prev ++ next.nodeList
/--Theorem: The append_nodeList function interacts with List.foldl in a specific way.-/
@[simp]
theorem append_nodeLists_cons (PDT : PreDerivationTree G) (list₁ list₂ : List (PreDerivationTree G)):
  PDT :: List.foldl append_nodeLists list₁ list₂ = List.foldl append_nodeLists (PDT::list₁) list₂ := by
    cases list₂
    case nil =>
      rw [List.foldl_nil, List.foldl_nil]
    case cons head tail =>
      rw [List.foldl_cons, List.foldl_cons]
      repeat rw [append_nodeLists]
      exact append_nodeLists_cons PDT (list₁ ++ PreDerivationTree.nodeList head) tail
/--Theorem: The append_nodeList function interacts with List.foldl in a specific way.-/
@[simp]
theorem concat_nodeLists_cons (PDT_List : List (PreDerivationTree G)) (list₁ list₂ : List (PreDerivationTree G)):
  PDT_List ++ List.foldl append_nodeLists list₁ list₂ = List.foldl append_nodeLists (PDT_List ++ list₁) list₂ := by
    cases list₂
    case nil =>
      rw [List.foldl_nil, List.foldl_nil]
    case cons head tail =>
      rw [List.foldl_cons, List.foldl_cons]
      repeat rw [append_nodeLists]
      have h_concat_assoc :
        PDT_List ++ list₁ ++ PreDerivationTree.nodeList head =
        PDT_List ++ (list₁ ++ PreDerivationTree.nodeList head) := by simp
      rw [h_concat_assoc]
      exact concat_nodeLists_cons PDT_List (list₁ ++ PreDerivationTree.nodeList head) tail

mutual
/--Theorem: The PreDerivationTree.nodeList function appends all of a nodes children and itself into a large list.-/
theorem PreDerivationTree.nodeList_eq_concat_children_nodeList
  {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) :
  PDT.nodeList = [PDT] ∨
  PDT.nodeList = List.foldl append_nodeLists [PDT] PDT.children := by
    cases PDT
    case leaf w =>
      apply Or.inl
      rfl
    case inner var children rule =>
      apply Or.inr
      rw [PreDerivationTree.children,
        PreDerivationTree.nodeList,
        NEPreDerivationTreeList.nodeList_eq_concat_children_nodeList]
      have h_list : NEPreDerivationTreeList.asList children = NEPreDerivationTreeList.asList children ++ [] := by simp
      rw [h_list]
      repeat rw [List.foldl_append _ _ _ []]
      simp

/--Theorem: The NEPreDerivationTreeList.nodeList function appends all of a the included nodes and their children into a large list.-/
theorem NEPreDerivationTreeList.nodeList_eq_concat_children_nodeList
  {G : ContextFreeGrammar α nt} (NEPDT : NEPreDerivationTreeList G) :
  NEPDT.nodeList = List.foldl append_nodeLists [] NEPDT.asList := by
  cases NEPDT
  case single PDT =>
    repeat rw [NEPreDerivationTreeList.nodeList, NEPreDerivationTreeList.asList]
    simp; rw [append_nodeLists]
    simp
  case cons PDT NEPDT₂ =>
    repeat rw [NEPreDerivationTreeList.nodeList, NEPreDerivationTreeList.asList]
    rw [List.foldl_cons]
    repeat rw [append_nodeLists]
    simp
    have h_PDT_nodeList : _ := PDT.nodeList_eq_concat_children_nodeList
    cases h_PDT_nodeList
    case inl h_inl =>
      -- rewrite using mutual-recursion theorem for PDT as well as recursion-theorem for NEPDT₂,
      rw [h_inl, NEPDT₂.nodeList_eq_concat_children_nodeList]
      -- Use the following theorem:
      -- PDT :: List.foldl append_nodeLists list₁ list₂ =
      -- List.foldl append_nodeLists (PDT::list₁) list₂
      exact append_nodeLists_cons PDT [] (NEPreDerivationTreeList.asList NEPDT₂)
      -- could just use simp instead also
    case inr h_inr =>
      -- rewrite using mutual-recursion theorem for PDT as well as recursion-theorem for NEPDT₂,
      rw [h_inr, NEPDT₂.nodeList_eq_concat_children_nodeList]
      -- Use the same theorem as before, but for concatenation of lists
      rw [concat_nodeLists_cons _ [] (NEPreDerivationTreeList.asList NEPDT₂)]
      -- the above is already included in simp, but I left it in for clarity
      simp
end

/--Theorem: Given a NEPreDerivationTreeList, its members have less nodes than the whole list.-/
theorem NEPreDerivationTreeList.children_have_leq_nodes
  {G : ContextFreeGrammar α nt} (NEPDT : NEPreDerivationTreeList G) :
  ∀ child ∈ NEPDT.asList, NEPDT.nodeList.length >= child.nodeList.length := by
  intro child h_membership
  cases NEPDT with
  | single c =>
    -- nodeList of single NEPDTL is that nodes nodeList exactly
    simp only [NEPreDerivationTreeList.nodeList]
    -- single NEPDTL has only one child ∈ NEPDT.asList
    have : child = c := by
      simp [NEPreDerivationTreeList.asList] at h_membership
      exact h_membership
    -- then solves itself with rfl
    rw [this]
  | cons PDT NEPDT₁ =>
    -- nodeList of cons PDT NEPDTL is nodeList PDT ++ nodeList NEPDTL
    simp only [NEPreDerivationTreeList.nodeList]
    -- Case distinction over if PDT is the child we are proving the expression for
    by_cases PDT = child -- TODO: this might use classical logic; should be possible with boolean equality
    -- Case PDT is the child over which we are proving, i.e. PDT is at the top of the list
    case pos h_eq =>
      -- List.length l₁ ++ l₂ = List.length l₁ + List.length l₂
      rw [List.length_append]
      -- reorder inequality
      simp
      -- rewrite PDT to child
      rw [h_eq]
      -- now we have a ≤ a + b
      apply Nat.le_add_right
    -- Case PDT in not the child over which we are proving, i.e. PDT is later in the list
    case neg h_neq =>
      -- List.length l₁ ++ l₂ = List.length l₁ + List.length l₂
      rw [List.length_append]
      -- reorder inequality
      simp
      -- Can add 0 + _ to the front of anything
      rw [← Nat.zero_add child.nodeList.length]
      -- Split into two proof tasks: 0 ≤ PDTlength and childlength ≤ NEPDT₁length
      apply Nat.add_le_add
      -- Close first goal: 0 ≤ anything
      apply Nat.zero_le
      -- Apply recursive theorem child vs NEPDTL₁
      apply NEPreDerivationTreeList.children_have_leq_nodes
      -- Applying the recursive theorem requires a proof that child is in NEPDT₁.asList
      unfold NEPreDerivationTreeList.asList at h_membership
      -- Which we know from ∀ child ∈ NEPDT.asList, ... plus that it is not at the start of the list
      simp at h_membership
      cases h_membership with
      | inl h_eq => rw [h_eq] at h_neq; contradiction
      | inr h_inList => exact h_inList

/--Theorem: The total number on nodes in a context-free (sub-)tree decreases the further we go down in a tree.-/
theorem PreDerivationTree.children_have_leq_nodes
  {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) :
  (∃ w, PDT = PreDerivationTree.leaf w) ∨
  (∃ var children rule, PDT =  PreDerivationTree.inner var children rule
    ∧ ∀ child ∈ children.asList,
    PDT.nodeList.length >= child.nodeList.length ):= by
      cases PDT
      -- If PDT is a leaf
      case leaf w' =>
        -- Then we prove the left side trivially
        apply Or.inl
        exists w'
      -- If the PDT is a node
      case inner var' children' rule' =>
        apply Or.inr
        exists var'; exists children'; exists rule'
        apply And.intro
        rfl
        intro child h_child_mem
        simp
        apply Nat.le_succ_of_le -- We tell LEAN that the number is going to increase
        -- We simply use the NEPDTL theorem
        apply NEPreDerivationTreeList.children_have_leq_nodes
        -- and somehow LEAN believes us, that the number increased
        exact h_child_mem

mutual
/--The condition that specifies a valid derivation tree.

- The production rule is applicable in this step.

- The children match the production rules result.

- The children are tree-valid.-/
def PreDerivationTree.treeValid {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) : Prop :=
  match PDT with
  | .leaf _ => True
  | .inner var children rule =>
      /- 1 The production rule is applicable in this step.-/
      var = rule.1.lhs ∧
      /- 2 The children match the production rules result. -/
      children.levelWord = rule.1.rhs ∧
      /- 3 The children are valid. -/
      children.treeValid
/- treeWord children = rule.rhs ∧ children.all (fun c => @decide (treeValid c) (Classical.propDecidable _))
termination_by t => depth t -/
/--A list of Derivation Trees is valid, if each of its children is valid.-/
def NEPreDerivationTreeList.treeValid {G : ContextFreeGrammar α nt} (NEPDTL : NEPreDerivationTreeList G) : Prop :=
  match NEPDTL with
  | .single PDT => PDT.treeValid
  | .cons PDT NEPDTL₂ => PDT.treeValid ∧ NEPDTL₂.treeValid
end

/--Theorem: If a list of tree nodes are valid, then so is any of its members.-/
theorem NEPreDerivationTreeList.treeValid_implies_child_valid
  {G : ContextFreeGrammar α nt} {NEPDTL : NEPreDerivationTreeList G} {child : PreDerivationTree G}
  (h_treeValid : NEPDTL.treeValid) (h_mem : child ∈ NEPDTL.asList) : (child.treeValid) := by
    -- Case distinction over the list
    cases h_constructor : NEPDTL
    -- Singleton case
    case single PDT =>
      rw [h_constructor] at h_treeValid
      rw [NEPreDerivationTreeList.treeValid] at h_treeValid
      -- Then the child must be exactly that singleton
      have h_equal : PDT = child := by
        rw [h_constructor] at h_mem
        rw [NEPreDerivationTreeList.asList] at h_mem
        rw [List.mem_singleton] at h_mem
        rw [h_mem]
      rw [← h_equal]
      -- Which by definition of NEPreDerivationTreeList.treeValid yields the childs validity
      exact h_treeValid
    -- Non-Empty case
    case cons PDT NEPDTL₂ =>
      rw [h_constructor] at h_treeValid h_mem
      rw [NEPreDerivationTreeList.treeValid] at h_treeValid
      rw [NEPreDerivationTreeList.asList] at h_mem
      -- Then the child is either at the top (head) of the list, or in the tail
      rw [List.mem_cons] at h_mem
      cases h_mem
      -- Case head
      case inl h_left =>
        rw [h_left]
        -- Then we know the head of the list is treeValid by definition of NEPreDerivationTreeList.treeValid
        exact h_treeValid.left
      -- Case tail
      case inr h_right =>
        -- Recursive call to the theorem
        exact NEPreDerivationTreeList.treeValid_implies_child_valid h_treeValid.right h_right

variable (PDT : PreDerivationTree G) (NEPDTL : NEPreDerivationTreeList G)

mutual
def NEPreDerivationTreeList.decideTreeValid {NEPDTL : NEPreDerivationTreeList G}
  --[decPDT : Decidable (PDT.treeValid)]
  [_h₁ : DecidableEq (G.V)] [_h₂ : DecidableEq (G.Z)]
  : Decidable (NEPDTL.treeValid) :=
  match NEPDTL with
    | .single PDT => by rw [NEPreDerivationTreeList.treeValid]; exact PDT.decideTreeValid
    | .cons PDT₂ NEPDTL₂ =>
      match (PDT₂.decideTreeValid : (Decidable PDT₂.treeValid)) with
        | isFalse h_isFalse => isFalse (by
          rw [NEPreDerivationTreeList.treeValid]
          apply Not.intro
          intro h_not
          absurd h_not.left
          exact h_isFalse)
        | isTrue _ => by
          rw [NEPreDerivationTreeList.treeValid]
          have _ : _ := NEPDTL₂.decideTreeValid
          have _ : _ := PDT₂.decideTreeValid
          apply instDecidableAnd
          --NEPDTL₂.decideTreeValid
def PreDerivationTree.decideTreeValid {PDT : PreDerivationTree G}
  --[d_terminals : DecidableEq α] [d_vars : DecidableEq nt]
  [h₁ : DecidableEq (G.V)] [h₂ : DecidableEq (G.Z)]
  -- [h_eqlhs : Decidable (NEPreDerivationTreeList.treeValid)]
  --[Decidable NEPreDerivationTreeList.treeValid]
  : Decidable PDT.treeValid :=
  match PDT with
    | .leaf _ => isTrue (by rw [PreDerivationTree.treeValid]; simp)
    | .inner var children rule =>
        @Decidable.by_cases (var = rule.1.lhs) (Decidable (PreDerivationTree.treeValid (PreDerivationTree.inner var children rule))) _
          (fun h_lhs : (var = rule.1.lhs) =>
            @Decidable.by_cases (children.levelWord = rule.1.rhs) _ _
              (fun h_rhs : (children.levelWord = rule.1.rhs) =>
                  @Decidable.by_cases (children.treeValid) (Decidable (PreDerivationTree.treeValid (PreDerivationTree.inner var children rule))) children.decideTreeValid
                  (fun h_children : (children.treeValid) =>
                    isTrue (by
                      rw [PreDerivationTree.treeValid]
                      rw [h_lhs, h_rhs]
                      simp
                      exact h_children
                    )
                  )
                  (fun h_children : ¬(children.treeValid) =>
                    isFalse (by
                      apply Not.intro; intro h_not
                      rw [PreDerivationTree.treeValid] at h_not
                      absurd h_not.right.right
                      exact h_children
              )))
                (fun h_rhs : ¬(children.levelWord = rule.1.rhs) =>
                isFalse (by
                  apply Not.intro; intro h_not
                  rw [PreDerivationTree.treeValid] at h_not
                  absurd h_not.right.left
                  exact h_rhs
                )
              )
          ) (fun h_lhs : ¬(var = rule.1.lhs) =>
            isFalse
            (by
              apply Not.intro; intro h_not
              rw [PreDerivationTree.treeValid] at h_not
              absurd h_not.left
              exact h_lhs
            )
          )

end

--instance : DecidableEq {x // x ∈ G.V } := by
  --sorry
--instance : DecidableEq {x // x ∈ G.Z } := by
  --sorry
instance [DecidableEq (G.V)] [DecidableEq (G.Z)] : Decidable (PDT.treeValid) := PDT.decideTreeValid
instance [DecidableEq (G.V)] [DecidableEq (G.Z)] : Decidable (NEPDTL.treeValid) := NEPDTL.decideTreeValid

/--The condition (prop) specifying whether it starts in the starting symbol-/
def PreDerivationTree.isFromStartingSymbolCondition {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Prop
| .leaf _ => False
| .inner var _ _ => var = G.start
/--Does this tree begin in the starting symbol?-/
def PreDerivationTree.isFromStartingSymbol {G : ContextFreeGrammar α nt} [ DecidableEq (G.V)] : (PDT : PreDerivationTree G) → Bool
| .leaf _ => False
| .inner var _ _ => @Decidable.by_cases (var = G.start) (Bool) _
  (fun _ => True)
  (fun _ => False)

-- Induction Principles for PreDerivationTrees and NEPreDerivationTreeLists
mutual
/--Doing an inductive proof over PDTs requires two to be proven properties.
  One for PDTs, one for NEPTLs. Equally induction basis and step must be provided for both data structures.-/
@[elab_as_elim]
def PreDerivationTree.induction_principle {G : ContextFreeGrammar α nt}
  /-Property over PDTs.-/
  (prop : PreDerivationTree G → Prop)
  /-Property over NEPDTLs.-/
  (prop₂ : NEPreDerivationTreeList G → Prop)
  /-Base case for PDTs.-/
  (ind_basis : ∀ terminal : Option G.Z , prop (PreDerivationTree.leaf terminal))
  /-Base case for NEPDTLs.-/
  (ind_basis₂ :
    ∀ PDT : PreDerivationTree G,
      prop PDT → prop₂ (NEPreDerivationTreeList.single PDT))
  /-Induction step for PDTs.-/
  (ind_step :
    ∀ (v : G.V) (children : NEPreDerivationTreeList G)
    (rule : G.productions),
    (ind_hyp : prop₂ children)
    →
    prop (PreDerivationTree.inner v children rule))
  /-Induction step for NEPDTLs.-/
  (ind_step₂ :
    ∀ PDT : PreDerivationTree G, ∀ NEPDTL₂ : NEPreDerivationTreeList G,
      prop PDT → prop₂ NEPDTL₂ → prop₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂))
  : ∀ PDT : PreDerivationTree G, prop PDT
  := @PreDerivationTree.rec α nt G prop prop₂
    (fun terminal =>
      by apply ind_basis terminal)
    (fun var children prodRule =>
      fun h₁ : prop₂ children =>
        ind_step var children prodRule h₁)
    (fun PDT =>
      fun h₂ : prop PDT =>
        ind_basis₂ PDT h₂)
    (fun PDT =>
      fun NEPDTL =>
        fun h₁ : prop PDT =>
          fun h₂ : prop₂ NEPDTL =>
            ind_step₂ PDT NEPDTL h₁ h₂)
/--Doing an inductive proof over NEPDTLs requires two to be proven properties.
  One for PDTs, one for NEPTLs. Equally induction basis and step must be provided for both data structures.-/
@[elab_as_elim]
def NEPreDerivationTreeList.induction_principle {G : ContextFreeGrammar α nt}
  /-Property over PDTs.-/
  (prop : PreDerivationTree G → Prop)
  /-Property over NEPDTLs.-/
  (prop₂ : NEPreDerivationTreeList G → Prop)
  /-Base case for PDTs.-/
  (ind_basis : ∀ terminal : Option G.Z , prop (PreDerivationTree.leaf terminal))
  /-Base case for NEPDTLs.-/
  (ind_basis₂ :
    ∀ PDT : PreDerivationTree G,
      prop PDT → prop₂ (NEPreDerivationTreeList.single PDT))
  /-Induction step for PDTs.-/
  (ind_step :
    ∀ (v : G.V) (children : NEPreDerivationTreeList G)
    (rule : G.productions),
    (ind_hyp : prop₂ children)
    →
    prop (PreDerivationTree.inner v children rule))
  /-Induction step for NEPDTLs.-/
  (ind_step₂ :
    ∀ PDT : PreDerivationTree G, ∀ NEPDTL₂ : NEPreDerivationTreeList G,
      prop PDT → prop₂ NEPDTL₂ → prop₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂))
  : ∀ NEPDTL : NEPreDerivationTreeList G, prop₂ NEPDTL
  := @NEPreDerivationTreeList.rec α nt G prop prop₂
    (fun terminal =>
      ind_basis terminal)
    (fun var children prodRule =>
      fun h₁ : prop₂ children =>
        ind_step var children prodRule h₁)
    (fun PDT =>
      fun h₂ : prop PDT =>
        ind_basis₂ PDT h₂)
    (fun PDT =>
      fun NEPDTL =>
        fun h₁ : prop PDT =>
          fun h₂ : prop₂ NEPDTL =>
            ind_step₂ PDT NEPDTL h₁ h₂)
end

--=============================================================
-- Section: DerivationTree structure
--=============================================================

/--Structure: A context-free derivation tree. Use`tree : PreDerivationTree`to define its structure and provide
  a validity proof`valid : treeValid tree`. Note that the definition of`tree`should be in correct order left-to-right.-/
structure DerivationTree (G : ContextFreeGrammar α nt) where
  tree : PreDerivationTree G
  valid : tree.treeValid
  deriving DecidableEq

/--Construct a context-free derivation-tree leaf from a terminal word.-/
@[match_pattern]
def DerivationTree.leaf {G : ContextFreeGrammar α nt} (w : Option G.Z) : DerivationTree G := {
  tree := PreDerivationTree.leaf w
  valid := by simp [PreDerivationTree.treeValid]
}

/--Construct a context-free derivation-tree node from:

- The variable`v`,

- A list of the nodes children`children`. Must be of type`NEPreDerivationTreeList`.

- The applied production rule`rule`,

- Constraints on the production rule:

-   -   `h_rule_lhs`

-   -   `h_rule_rhs`

- A proof of the validity-constraints for of the children`childrenValid`.-/
@[match_pattern]
def DerivationTree.inner {G : ContextFreeGrammar α nt}
  (v : G.V) (children : NEPreDerivationTreeList G)
  (rule : G.productions)
  (h_rule_lhs : rule.1.lhs = v) (h_rule_rhs : rule.1.rhs = children.levelWord) (childrenValid : children.treeValid)
  : DerivationTree G := {
    tree := PreDerivationTree.inner v children rule
    valid := by
      rw[PreDerivationTree.treeValid, h_rule_lhs, h_rule_rhs]
      simp; exact childrenValid
}

/--Construct a derivation tree child from the a proof of validity of
  the list of children and the child's membership in this list.-/
def DerivationTree.fromChild
  {G : ContextFreeGrammar α nt} {children : NEPreDerivationTreeList G} {child : PreDerivationTree G}
  (childrenValid : children.treeValid) (h_child_mem : child ∈ children.asList) : DerivationTree G :=
  match child with
  | .leaf terminal => DerivationTree.leaf terminal
  | .inner var child_children rule => by
    have h : _ := NEPreDerivationTreeList.treeValid_implies_child_valid childrenValid h_child_mem
    rw [PreDerivationTree.treeValid] at h
    exact
      DerivationTree.inner var child_children rule
      (h.left.symm)
      (h.right.left.symm)
      (h.right.right)

/--Induction principle for Derivation Trees.
  Induction basis is prop validity for any leaf.

  `∀ terminal : Word G.Z , prop (DerivationTree.leaf terminal)`

  Induction step requires a proof, that from prop being valid for
  an unknown collection of children we can generate prop(parent), where the parent is synthesized from
  an unknownm, but valid, derivation tree construction.

  `∀ (v : G.V) (children : NEPreDerivationTreeList G) (rule : ContextFreeProduction G.Z G.V) (h_rule_lhs : rule.lhs = v) (h_rule_rhs : rule.rhs = children.levelWord) (childrenValid : children.treeValid), (ind_hyp : ∀ child, (h_mem : child ∈ children.asList) → prop (DerivationTree.fromChild childrenValid (h_mem : child ∈ children.asList))) → prop (DerivationTree.inner v children rule h_rule_lhs h_rule_rhs childrenValid)`-/
@[elab_as_elim]
def DerivationTree.induction_principle {G : ContextFreeGrammar α nt}
  /-For any given property,-/
  (prop : DerivationTree G → Prop)
  /-if we can prove the prop for leaf DTs-/
  (ind_basis : ∀ terminal : Option G.Z , prop (DerivationTree.leaf terminal))
  /- and...-/
  (ind_step :
    /- for ANY inner DT-/
    ∀ (v : G.V) (children : NEPreDerivationTreeList G)
    (rule : G.productions) (h_rule_lhs : rule.1.lhs = v)
    (h_rule_rhs : rule.1.rhs = children.levelWord) (childrenValid : children.treeValid),
    /- from induction hypothesis (prop valid for all children)-/
    (ind_hyp : ∀ child, (h_mem : child ∈ children.asList) → prop (DerivationTree.fromChild childrenValid (h_mem : child ∈ children.asList)))
    →
    /- we can prove the prop for this "next" DT-/
    prop (DerivationTree.inner v children rule h_rule_lhs h_rule_rhs childrenValid))
  /- then the property is valid for all DTs-/
  : ∀ DT : DerivationTree G, prop DT
  :=
  @DerivationTree.rec α nt G
    /-The to-be-proven property-/
    prop
    ( /-For any DT, i.e. PDT + PDT.treeValid-/
      fun tree =>
      fun valid =>
        by
          /- Plan: Prove via mutual structural induction on PDT & NEPDTL
           that from ind_basis, ind_step we can follow prop for all
           This mutual induction uses two different propositions to be proven
           The difficulty lies in finding these propositions
           The propositions are propHelper for PDTs and propHelper₂ for NEPDTLs

           The property for PDTs is an implication with multiple pre-conditions
           These include... -/
          let propHelper : (PreDerivationTree G → Prop) :=
            fun PDT =>
              /-Validity of the PDT,-/
              (h_PDT_valid : PDT.treeValid) →
              /-the induction basis for DTs be proven,-/
              (∀ (terminal : Option { x // x ∈ G.Z }), prop (leaf terminal)) →
              /-... and a match from the induction step via actual recursive constructor for DTs to the
              more easily useable fromChild induction step for DTs.-/
              (∀
                (v : { x // x ∈ G.V }) (children : NEPreDerivationTreeList G) (rule : G.productions)
                (h_rule_lhs : rule.1.lhs = v) (h_rule_rhs : rule.1.rhs = NEPreDerivationTreeList.levelWord children)
                (childrenValid : NEPreDerivationTreeList.treeValid children),
              (∀ (child : PreDerivationTree G) (h_mem : child ∈ NEPreDerivationTreeList.asList children),
                  prop (fromChild childrenValid h_mem)) →
                prop (inner v children rule h_rule_lhs h_rule_rhs childrenValid)) →
              /-If all these are given we can prove the property for all DTs.-/
              prop {tree := PDT, valid := h_PDT_valid}
          /-The property for NEPDTLs is an implication with multiple pre-conditions
           These include... -/
          let propHelper₂ : (NEPreDerivationTreeList G → Prop) :=
            fun NEPDTL =>
              /-Validity of the NEPDTL,-/
              (h_NEPDTL_valid : NEPDTL.treeValid) →
              /-the induction basis for DTs be proven,-/
              (∀ (terminal : Option { x // x ∈ G.Z }), prop (leaf terminal)) →
              /-... and a match from the induction step via actual recursive constructor for DTs to the
              more easily useable fromChild induction step for DTs.-/
              (∀
                (v : { x // x ∈ G.V }) (children : NEPreDerivationTreeList G) (rule : G.productions)
                (h_rule_lhs : rule.1.lhs = v) (h_rule_rhs : rule.1.rhs = NEPreDerivationTreeList.levelWord children)
                (childrenValid : NEPreDerivationTreeList.treeValid children),
              (∀ (child : PreDerivationTree G) (h_mem : child ∈ NEPreDerivationTreeList.asList children),
                  prop (fromChild childrenValid h_mem)) →
                prop (inner v children rule h_rule_lhs h_rule_rhs childrenValid)) →
              /-If all these are given we can prove that the induction step using fromChild is legit.-/
              ∀ (child : PreDerivationTree G) (h_mem : child ∈ NEPreDerivationTreeList.asList NEPDTL),
                  prop (fromChild h_NEPDTL_valid h_mem)
          /-We now use structural induction on PDTs to prove propHelper for all DTs.-/
          have property_PDTs : _ := @PreDerivationTree.induction_principle α nt G propHelper propHelper₂
          /- For this we need to prove the base case for propHelper...-/
          have propHelper_basis : (∀ (terminal : Option G.Z), propHelper (PreDerivationTree.leaf terminal)) := by
            /-Name the implication pre-conditions of the base case.-/
            intro tw
            /-Name the implication pre-conditions of the property propHelper (...).-/
            intro _ _ _
            /-The induction base case yields our goal.-/
            exact ind_basis tw
          /- and the base case for propHelper₂ -/
          have propHelper₂_basis : (∀ (PDT : PreDerivationTree G), propHelper PDT → propHelper₂ (NEPreDerivationTreeList.single PDT)) := by
            /-Name the implication pre-conditions of the base case.-/
            intro PDT h_propHelper_PDT
            /-Name the implication pre-conditions of the property propHelper₂ (...).-/
            intro h_NEPDTL_valid h_basis h_step
            /-Introduce the necessary child variable & member assumption to do a ∀-proof.-/
            intro child h_mem
            /-We know that PDT is this child, because NEPDTL is a singleton "list".-/
            have h_refl : PDT = child := by
              apply Eq.symm
              rw [← List.mem_singleton]
              rw [NEPreDerivationTreeList.asList] at h_mem
              exact h_mem
            have h_mem₂ : _ := h_mem
            /-Thus yielding that PDT is in NEPDTL[PDT] -/
            rw [← h_refl] at h_mem₂
            /-Get PDT validity from it being in [PDT]-/
            have h_PDT_valid : PDT.treeValid :=
              NEPreDerivationTreeList.treeValid_implies_child_valid h_NEPDTL_valid h_mem₂
            /-Show that our goal is equivalent to proving prop for the PDT-based DerivationTree-/
            have h_refl₂ : (fromChild h_NEPDTL_valid h_mem) = { tree := PDT, valid := h_PDT_valid } := by
              rw [fromChild]
              cases child
              case leaf tw =>
                simp [DerivationTree.leaf]
                exact h_refl.symm
              case inner v c r =>
                simp [DerivationTree.inner]
                exact h_refl.symm
            /-Use the assumption that propHelper PDT to show our goal.-/
            have h_prop : _ := h_propHelper_PDT h_PDT_valid h_basis h_step
            rw [h_refl₂]
            exact h_prop
          /-Prove the induction step for propHelper.-/
          have propHelper_step : (∀ (v : { x // x ∈ G.V }) (children : NEPreDerivationTreeList G) (rule : G.productions),
            propHelper₂ children → propHelper (PreDerivationTree.inner v children rule)) := by
            /-Name the implication pre-conditions of the induction step.-/
            intro v_step children_step rule_step h_propHelper₂_children_step
            /-Name the implication pre-conditions of the property propHelper (...).-/
            intro h_valid_goal _ h_basis₂_goal
            /-We use, that the "fromChild"-based induction step generalises to the DT.inner-based induction step.
              (By propHelper assumption.)-/
            apply h_basis₂_goal v_step children_step rule_step
            /-Are valid by assumption.-/
            case h_rule_lhs =>
              exact h_valid_goal.left.symm
            case h_rule_rhs =>
              exact h_valid_goal.right.left.symm
            case childrenValid =>
              exact h_valid_goal.right.right
            /-Prove that generalisation was successfull.-/
            case a : ∀ (child : PreDerivationTree G) (h_mem : child ∈ NEPreDerivationTreeList.asList children_step), prop (fromChild _ h_mem) =>
              have h_children_step_valid : children_step.treeValid := h_valid_goal.right.right
              intro child_step h_mem_step
              /-From the induction hypothesis.-/
              exact h_propHelper₂_children_step h_children_step_valid ind_basis ind_step child_step h_mem_step
          /-Prove the induction step for propHelper₂.-/
          have propHelper₂_step : (∀ (PDT : PreDerivationTree G) (NEPDTL₂ : NEPreDerivationTreeList G),
            propHelper PDT → propHelper₂ NEPDTL₂ → propHelper₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂)) := by
            /-Name the implication pre-conditions of the induction step.-/
            intro PDT NEPDTL₂ h_propHelper_PDT h_propHelper₂_NEPDTL
            /-Name the implication pre-conditions of the property propHelper₂ (...).-/
            intro h_valid_goal _ _
            /-Introduce the necessary child variable & member assumption to do a ∀-proof.-/
            intro child h_mem
            /-Follow validity of both PDT and NEPDTL₂ from the propHelper₂ pre-condition.-/
            rw [NEPreDerivationTreeList.treeValid] at h_valid_goal
            have h_NEPDTL₂_valid : NEPDTL₂.treeValid := h_valid_goal.right
            have h_PDT_valid : PDT.treeValid := h_valid_goal.left
            /-Reduce / Use the propHelper(₂) assumptions-/
            have h_propHelper₂_NEPDTL_usage : _ :=
              h_propHelper₂_NEPDTL h_NEPDTL₂_valid ind_basis ind_step child
            have h_propHelper_PDT_usage : _ :=
              h_propHelper_PDT h_PDT_valid ind_basis ind_step
            /-Case distinction over leaf or not.-/
            cases child
            case leaf tw =>
              simp [fromChild]
              apply ind_basis
            case inner v c r =>
              simp [fromChild]
              rw [NEPreDerivationTreeList.asList] at h_mem
              rw [List.mem_cons] at h_mem
              /-Case distinction: child in top of list (=PDT) or in body (NEPDTL)-/
              cases h_mem
              case inl h_inl =>
                rw [DerivationTree.inner]
                have h_inl₂ : _ := h_inl.symm
                /-place child into propHelper(PDT) assumption-/
                simp [h_inl₂] at h_propHelper_PDT_usage
                /-If child is PDT, then we can use propHelper(PDT) to our advantage.-/
                exact h_propHelper_PDT_usage
              case inr h_inr =>
                /-If child is in NEPDTL, then we can use propHelper₂(NEPDTL) to our advantage.-/
                apply h_propHelper₂_NEPDTL_usage at h_inr
                exact h_inr
          /-Insert all the induction basis' and steps, yielding propHelper for all PDTs-/
          apply property_PDTs at propHelper_basis
          apply propHelper_basis at propHelper₂_basis
          apply propHelper₂_basis at propHelper_step
          apply propHelper_step at propHelper₂_step
          have h_tree : _ := propHelper₂_step tree
          /-Now fill in all the fulfilled pre-conditions (valid, ind-basis, ind-step) in propHelper,...-/
          apply h_tree at valid
          apply valid at ind_basis
          apply ind_basis at ind_step
          exact ind_step
          /-Finally yielding the actual condition prop (DT).-/
          )

--=============================================================
-- Section: Example DerivationTree
--=============================================================

def ExampleTerminals : Finset Char := { 'x', 'y', 'z', '(', ')', '+', '*' }
def ExampleVariables : Finset Char :=  { 'A', 'M', 'S', 'V' }
@[simp]
theorem ExampleVariables.definition : ExampleVariables = { 'A', 'M', 'S', 'V' } := by rw [ExampleVariables]
@[simp]
theorem ExampleTerminals.definition : ExampleTerminals = { 'x', 'y', 'z', '(', ')', '+', '*' } := by rw [ExampleTerminals]

def EP : List (ContextFreeProduction ExampleTerminals ExampleVariables) := [
    -- rule S -> A
    (⟨ 'S', by simp ⟩ →ₚ₂ [ .inl ⟨ 'A', by simp ⟩ ]),
    -- rule S -> M
    (⟨ 'S', by simp ⟩ →ₚ₂ [ .inl ⟨ 'M', by simp ⟩ ]),
    -- rule S -> V
    (⟨ 'S', by simp ⟩ →ₚ₂ [ .inl ⟨ 'V', by simp ⟩ ]),
    -- rule A -> (S+S)
    (⟨ 'A', by simp ⟩ →ₚ₂ [ .inr ⟨ '(', by simp ⟩, .inl ⟨ 'S', by simp ⟩, .inr ⟨ '+', by simp ⟩,
                                   .inl ⟨ 'S', by simp ⟩, .inr ⟨ ')', by simp ⟩,  ]),
    -- rule M -> (S*S)
    (⟨ 'M', by simp ⟩ →ₚ₂ [ .inr ⟨ '(', by simp ⟩, .inl ⟨ 'S', by simp ⟩, .inr ⟨ '*', by simp ⟩,
                                   .inl ⟨ 'S', by simp ⟩, .inr ⟨ ')', by simp ⟩,  ]),
    -- rule V -> x
    (⟨ 'V', by simp ⟩ →ₚ₂ [ .inr ⟨ 'x', by simp ⟩ ]),
    -- rule V -> y
    (⟨ 'V', by simp ⟩ →ₚ₂ [ .inr ⟨ 'y', by simp ⟩ ]),
    -- rule V -> z
    (⟨ 'V', by simp ⟩ →ₚ₂ [ .inr ⟨ 'z', by simp ⟩ ])
]

def ExampleGrammar: @ContextFreeGrammar Char Char where
  Z := { 'x', 'y', 'z', '(', ')', '+', '*' }
  V := { 'A', 'M', 'S', 'V' }
  start := ⟨ 'S', by simp ⟩
  productions := EP.toFinset

def EP.StoA : ExampleGrammar.productions := ⟨ EP[0], by decide ⟩
def EP.StoM : ExampleGrammar.productions := ⟨ EP[1], by decide ⟩
def EP.StoV : ExampleGrammar.productions := ⟨ EP[2], by decide ⟩
def EP.AtoSplusS : ExampleGrammar.productions := ⟨ EP[3], by decide ⟩
def EP.MtoStimesS : ExampleGrammar.productions := ⟨ EP[4], by decide ⟩
def EP.Vtox : ExampleGrammar.productions := ⟨ EP[5], by decide ⟩
def EP.Vtoy : ExampleGrammar.productions := ⟨ EP[6], by decide ⟩
def EP.Vtoz : ExampleGrammar.productions := ⟨ EP[7], by decide ⟩

theorem ExampleGrammar.productions_eq_ex_productions (p: ContextFreeProduction _ _):
  p ∈ ExampleGrammar.productions ↔ p ∈ EP := by
  simp [ExampleGrammar]
  exact List.mem_toFinset

def ExampleGrammar.lang: Language ({ 'x', 'y', 'z', '+', '*', '(', ')'} : Finset _) :=
  sorry

#check ExampleGrammar.GeneratedLanguage

-- Construct an example tree, bottom up.
-- l for leaf, i for inner, indexed seperately
-- First number is depth of node, second is numbered from left to right on this depth
def ExamplePreTreel2_0 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ '(' , by decide⟩)
def ExamplePreTreel4_0 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ 'x' , by decide⟩)
def ExamplePreTreel2_1 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ '*' , by decide⟩)
def ExamplePreTreel4_1 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ '(' , by decide⟩)
def ExamplePreTreel6_0 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ 'y' , by decide⟩)
def ExamplePreTreel4_2 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ '+' , by decide⟩)
def ExamplePreTreel6_1 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ 'z' , by decide⟩)
def ExamplePreTreel4_3 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ ')' , by decide⟩)
def ExamplePreTreel2_2 : PreDerivationTree ExampleGrammar :=
.leaf (some ⟨ ')' , by decide⟩)

def ExamplePreTreei3_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'V' , by decide⟩ DT[ExamplePreTreel4_0] EP.Vtox
def ExamplePreTreei2_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'S' , by decide⟩ DT[ExamplePreTreei3_0] EP.StoV
def ExamplePreTreei5_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'V' , by decide⟩ DT[ExamplePreTreel6_0] EP.Vtoy
def ExamplePreTreei4_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'S' , by decide⟩ DT[ExamplePreTreei5_0] EP.StoV
def ExamplePreTreei5_1 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'V' , by decide⟩ DT[ExamplePreTreel6_1] EP.Vtoz
def ExamplePreTreei4_1 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'S' , by decide⟩ DT[ExamplePreTreei5_1] EP.StoV
def ExamplePreTreei3_1 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'A' , by decide⟩ DT[ExamplePreTreel4_1, ExamplePreTreei4_0, ExamplePreTreel4_2, ExamplePreTreei4_1, ExamplePreTreel4_3] EP.AtoSplusS
def ExamplePreTreei2_1 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'S' , by decide⟩ DT[ExamplePreTreei3_1] EP.StoA
def ExamplePreTreei1_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'M' , by decide⟩ DT[ExamplePreTreel2_0, ExamplePreTreei2_0, ExamplePreTreel2_1, ExamplePreTreei2_1, ExamplePreTreel2_2] EP.MtoStimesS
def ExamplePreTreeRoot : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'S' , by decide⟩ DT[ExamplePreTreei1_0] EP.StoM

/--Define the derivation tree itself. Note: Only the root is a derivation tree.
  Corresponds to ExamplePreTreeRoot.-/
def ExampleDT : DerivationTree ExampleGrammar :=
  DerivationTree.inner ⟨ 'S', by decide⟩ DT[ExamplePreTreei1_0] EP.StoM (by decide) (by decide) (by
    decide) -- Decidable proofs allow this to be simple

--=============================================================
-- Section: Derivation Tree completeness and notation
--=============================================================

/--A context-free derivation tree is total or complete if and only if it begins from
  the starting symbol of its grammar.-/
def DerivationTree.isTotalCondition {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : (Prop) :=
  DT.tree.isFromStartingSymbolCondition
/--A context-free derivation tree is total or complete if and only if it begins from
  the starting symbol of its grammar.-/
def DerivationTree.isCompleteCondition {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : (Prop) := DT.isTotalCondition
/--Return whether this derivation tree is total.-/
def DerivationTree.isTotal {G : ContextFreeGrammar α nt} [DecidableEq (G.V)] (DT : DerivationTree G) : (Bool) :=
  DT.tree.isFromStartingSymbol
/--Return whether this derivation tree is complete (=total).-/
def DerivationTree.isComplete {G : ContextFreeGrammar α nt} [DecidableEq (G.V)] (DT : DerivationTree G) : (Bool) := DT.isTotal

/--Theorem: A total derivation tree is never a leaf, but an inner node.-/
theorem DerivationTree.total_trees_not_leaves {G : ContextFreeGrammar α nt} [DecidableEq (G.V)] (DT : DerivationTree G)
  (h_DT_total : DT.isTotal) :
  ∃ var children rule h_lhs h_rhs h_valid, DT = @DerivationTree.inner α nt G var children rule h_lhs h_rhs h_valid := by
  rw [DerivationTree.isTotal] at h_DT_total
  rw [PreDerivationTree.isFromStartingSymbol] at h_DT_total
  cases h_constructor : DT
  --simp at h_DT_total
  case mk tree treeValid=>
    have h_DT_tree : DT.tree = tree := by rw [h_constructor]
    cases h_tree_constructor : DT.tree
    case leaf _ =>
      rw [h_tree_constructor] at h_DT_total
      contradiction
    case inner var children rule =>
      exists var, children, rule
      have h_valid : _ := DT.valid
      rw [h_tree_constructor, PreDerivationTree.treeValid] at h_valid
      have h_lhs_ref : _ := h_valid.left
      nth_rewrite 1 [eq_comm] at h_valid
      nth_rewrite 2 [eq_comm] at h_valid
      exists h_valid.left, h_valid.right.left, h_valid.right.right
      rw [DerivationTree.inner]
      simp
      rw [← h_DT_tree, h_tree_constructor]

/--Theorem: A total derivation tree's tree part is always a tree.-/
theorem DerivationTree.total_trees_not_leaves₂ {G : ContextFreeGrammar α nt} [DecidableEq (G.V)] (DT : DerivationTree G)
  (h_DT_total : DT.isTotal) :
  ∃ var children rule, DT.tree = @PreDerivationTree.inner α nt G var children rule := by
    have h_other : _ := DT.total_trees_not_leaves h_DT_total
    cases h_other; case intro var h_other₂ =>
      cases h_other₂; case intro children h_other₃=>
        cases h_other₃; case intro rule h_other₄=>
          cases h_other₄; case intro _ h_other₅=>
            cases h_other₅; case intro _ h_other₆=>
              cases h_other₆; case intro _ h_other₇=>
                exists var, children, rule
                rw [DerivationTree.inner] at h_other₇
                rw [h_other₇]

/--The starting symbol.-/
def DerivationTree.startingSymbol {G : ContextFreeGrammar α nt} [DecidableEq (G.V)] {DT : DerivationTree G} (_ : DT.isTotal) : G.V := G.start

/--The variable from which we begin deriving if we are a tree, or the terminal word if we are a leaf.-/
def DerivationTree.fromAny {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : Word (G.V ⊕ G.Z) :=
  match DT.tree with
  | PreDerivationTree.leaf tw => match tw with
    | none =>
      ε
    | some ts =>
      [Sum.inr ts]
  | PreDerivationTree.inner v _ _ => [Sum.inl v]

/--Return the variable from which we begin deriving or none if we are a leaf.-/
def DerivationTree.fromOptionVar {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : Option (G.V) := match DT.tree with
| PreDerivationTree.leaf _ => none
| PreDerivationTree.inner v _ _ => v

/--Return the variable from which we begin deriving if the tree is total.-/
def DerivationTree.fromVar {G : ContextFreeGrammar α nt} [DecidableEq { x // x ∈ G.V }] (DT : DerivationTree G) (h_isTotal : DT.isTotal) : (G.V) := by
  have h_neverTerminal : _ := DT.total_trees_not_leaves₂ h_isTotal
  let var : _ := DT.fromOptionVar
  have h_neverBot : var.isSome = true := by
    cases h_constructor : DT.tree
    case leaf tw =>
      cases h_neverTerminal; case intro var₂ h_neverTerminal₂ =>
        cases h_neverTerminal₂; case intro _ h_neverTerminal₃ =>
          cases h_neverTerminal₃; case intro _ h_neverTerminal₄ =>
            absurd h_neverTerminal₄
            simp [h_constructor]
    case inner v c r =>
      have h_def : var = DT.fromOptionVar := by simp
      simp [h_def, fromOptionVar, h_constructor]
  exact Option.get var h_neverBot

/--Return the resulting word of the derivation tree.-/
def DerivationTree.result {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : Word G.Z :=
  DT.tree.result

/-- u ≺(G)⇒* v -notation for context-free tree-based derivations. Is the proposition that there
  exists a derivation (∃) from u to v in G.-/
notation:40 var:40 " ≺(" G:40 ")⇒⁺ " word:41 => (∃ dt : (DerivationTree G), DerivationTree.isTotalCondition dt ∧ ContextFreeGrammar.start G = var ∧ DerivationTree.result dt = word)

/--Derivation tree depth.-/
def DerivationTree.depth {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : (ℕ) :=
  DT.tree.depth + 1

/--List of child nodes. Is a list of DTs.-/
def DerivationTree.children {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : List (DerivationTree G) :=
  by
    have valid : _ := DT.valid
    cases h_constructor : DT.tree
    case leaf tw =>
      exact []
    case inner v c r =>
      have ctv : c.treeValid := by
        rw [h_constructor, PreDerivationTree.treeValid] at valid
        exact valid.right.right
      exact List.map (λ child : {x // x ∈ c.asList} =>
        @DerivationTree.fromChild α nt G c child ctv child.prop) c.asList.attach

def DerivationTree.collect_prodRules
  {G : ContextFreeGrammar α nt}
  (DT : DerivationTree G) :
  List (G.productions) := DT.tree.prodRuleList

/-Hard to formulate-/
--theorem DerivationTree.depth_eq_maxDT_of_children {G : ContextFreeGrammar α nt} : ∀ DT : DerivationTree G, DT.depth = (List.foldl () 0 DT.children) := by sorry

/- Cannot use this type of definition because fo syntax stuff and gaving
   types depend on location in list

--def TreeBasedContextFreeDerivation.v (tbcfd : TreebasedContextFreeDerivation G v w) : G.V := v
--def TreeBasedContextFreeDerivation.w (tbcfd : TreebasedContextFreeDerivation G v w) : (Word G.Z) := w
/--Tree-based context-free derivations. Notation: `v ⇒(≺)⁺ w`. Are defined to be

  - "complete", i.e. they go from a single variable to the final word of terminal symbols

  - multi-step, though at least 1 step

  - unordered, the order of the applied production rules cannot be ascertained or stored

  - define a tree-structure.-/
inductive TreeBasedContextFreeDerivation (G : ContextFreeGrammar α nt) : (v: G.V) → (w: Word G.Z) → Type
  /--`v ⇒(cfproduction) w' = w₁V₁...Vₙ₋₁wₙVₙwₙ₊₁ ⇒(used_cfds)* w =  = w₁w'₁...w'ₙ₋₁wₙw'ₙwₙ₊₁`-/
  | step
    {vars : List G.V}
    {words : List (Word G.Z)}
    {proof_len : vars.length+1 = words.length}
    {proof_words_non_empty : words.length>0}
    {words' : List (Word G.Z)}
    {proof_len_words' : words'.length = vars.length}
    (cfproduction : (ContextFreeProduction G.Z G.V))
    (proof_production_lhs : cfproduction.lhs = v)
    (proof_production_rhs : cfproduction.rhs =
      @Word.concat2ListsOfWordsAlternating
        (G.V ⊕ G.Z)
        (List.map (fun var : { x // x ∈ G.V } => Word.mk [Sum.inl var]) vars)
        (List.map (fun word : Word { x // x ∈ G.Z } => List.map Sum.inr word) words)
        (by simp; exact proof_len)
        (by simp; exact proof_words_non_empty)
    )
    (proof_ : ∀ x ∈ List.finRange (vars.length),
              ∃ cfd : (TreeBasedContextFreeDerivation G vars[x] result),
              have x_valid_index : x < words'.length :=
                by sorry
              result = words'[x])
    (list_of_used_cfds : List (TreeBasedContextFreeDerivation G vars[index] words'[index]))
    (proof_result_word_composition : w =
      @Word.concat2ListsOfWordsAlternating
        (G.Z)
        (words')
        (words)
        (by rw [proof_len_words', proof_len])
        (proof_words_non_empty)
    )
    : TreeBasedContextFreeDerivation G v w

-/

--=============================================================
-- Section: Context-free derivations: => form
--=============================================================

/--Define context free derivations u (G)=>* v inductively.
  Either no step was made (constructor:`same`, requires a proof that u = v), or
  we have a recursive definition with at least one step (constructor `step`)-/
inductive ContextFreeDerivation (G : ContextFreeGrammar α nt) : (Word (G.V ⊕ G.Z)) → (Word (G.V ⊕ G.Z)) → Type
  /--0 step derivations u (G)=>* v-/
  | same {u : (Word (G.V ⊕ G.Z))} {v : (Word (G.V ⊕ G.Z))} (h : u = v) : ContextFreeDerivation G u v
  /--The recursive step definition of a derivation. Requires:
  - `step`  - The derivation step with input u,
  - `_derivation`     - A derivation from u' to v (recursive part of the definition),
  - `sound` - The proof that`step`yields u'.
  -/
  | step
    {u u' v : Word (G.V ⊕ G.Z)}
    (step : @ContextFreeDerivationStep α nt G u)
    (_derivation : ContextFreeDerivation G u' v)
    (sound : (step : @Grammar.DerivationStep α nt GenericProduction _ G u).result = u') :
    ContextFreeDerivation G u v
    /- {v v' : G.V} {w w' u_mid l_of_v' r_of_v' : Word (G.V ⊕ G.Z)}
    (h_production : { lhs := v, rhs := u_mid}  ∈ G.productions)
    (h_u_mid : u_mid = l_of_v' * Word.mk [Sum.inl v'] * r_of_v'):
    ContextFreeDerivation G v' w' → ContextFreeDerivation G v (l_of_v' * w' * r_of_v') -/

#check instDecidableEqContextFreeDerivationStep

/--Define the equality determinating relation.-/
def ContextFreeDerivation.decEq [DecidableEq α] [DecidableEq nt] {G : ContextFreeGrammar α nt} {u v : Word (G.V ⊕ G.Z)} : (CFD₁ CFD₂ : ContextFreeDerivation G u v) → Decidable (Eq CFD₁ CFD₂) :=
  fun (CFD₁ CFD₂ : (@ContextFreeDerivation α nt G u v)) =>
  match h_constructor₁ : CFD₁, h_constructor₂ : CFD₂ with
    | .same h_same₁, .same h_same₂ =>
      isTrue ( by
        have h_same_same : h_same₁ = h_same₂ := by simp
        rw [h_same_same]
      )
    | .same _, .step _ _ _ =>
      isFalse (by simp)
    | .step _ _ _, .same _ =>
      isFalse (by simp)
    | @ContextFreeDerivation.step α nt G _ u'₁ _ step₁ derivation₁ sound₁, @ContextFreeDerivation.step α nt G _ u'₂ _ step₂ derivation₂ sound₂ =>
      match (instDecidableEqContextFreeDerivationStep step₁ step₂) with
      | isFalse h_isFalse => isFalse (by
        simp; intro _;
        rw [imp_iff_or_not];
        apply Or.inr h_isFalse)
      | isTrue h_isTrue =>
        match (List.hasDecEq u'₁ u'₂) with
        | isFalse h_isFalse₂ =>
          isFalse (by simp [imp_iff_or_not]; apply Or.inr h_isFalse₂)
        | isTrue h_isTrue₂ => by
          /- have derivation1as2 : @ContextFreeDerivation α nt G u'₂ v := by
            rw [h_isTrue₂] at derivation₁
            exact derivation₁ -/
          let dv₁_rw : _ := by
            rw [h_isTrue₂] at derivation₁
            exact derivation₁
          have h_same : ContextFreeDerivation G u'₁ v = ContextFreeDerivation G u'₂ v := by rw [h_isTrue₂]
          have h_dv₁_rw_same : dv₁_rw = cast h_same derivation₁ := by rfl
          match (ContextFreeDerivation.decEq dv₁_rw derivation₂) with
          | isFalse h_isFalse₃ => exact (isFalse (by
            simp; intro _ _;
            apply Not.elim
            apply Not.intro; intro h_HEq
            rw [← (@cast_eq_iff_heq _ (ContextFreeDerivation G u'₂ v) h_same _ derivation₂)] at h_HEq
            rw [← h_dv₁_rw_same] at h_HEq
            contradiction
            ))
          | isTrue h_isTrue₃ =>
            exact isTrue (by
              simp [h_isTrue, h_isTrue₂]
              apply (@cast_eq_iff_heq _ _ h_same derivation₁ dv₁_rw).mp at h_dv₁_rw_same
              rw [h_isTrue₃] at h_dv₁_rw_same
              exact h_dv₁_rw_same)

instance [dec₁ : DecidableEq α] [dec₂ : DecidableEq nt] {G : ContextFreeGrammar α nt} {u v : Word (G.V ⊕ G.Z)} (cfd₁ cfd₂ : @ContextFreeDerivation α nt G u v) : Decidable (cfd₁ = cfd₂) := @ContextFreeDerivation.decEq α nt dec₁ dec₂ G u v cfd₁ cfd₂

--IMPORTANT: theorems are not computable!
/--Define an embedding of context-free derivations in generic derivations.-/
def ContextFreeDerivation.toDerivation
    {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
    (cfd : @ContextFreeDerivation α nt G u v) :
    (@Grammar.Derivation α nt GenericProduction _ (↑G) u v) :=
    match cfd with
    | same h_same =>
      Grammar.Derivation.same h_same
    | step dStep derivation h_sound =>
      Grammar.Derivation.step dStep derivation.toDerivation h_sound

--Coercion CFDerivation into generic Derivations
instance {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  : Coe (@ContextFreeDerivation α nt G u v) (@Grammar.Derivation α nt GenericProduction _ (↑G) u v) where
  coe cfDerivation := ContextFreeDerivation.toDerivation cfDerivation

-- variable {CDF : (@ContextFreeDerivation α nt G u v)}
-- #check (↑(CDF) : @Grammar.Derivation α nt GenericProduction _ G u v).len
-- Grammar.Derivation.len (ContextFreeDerivation.toDerivation CDF) : ℕ

/-- u CF(G)⇒* v -notation for context-free derivations. Is the proposition that there
  exists a derivation (∃) from u to v in G.-/
notation:40 u:40 " CF(" G:40 ")⇒* " v:41 => (Nonempty $ ContextFreeDerivation G u v)

/--Condition specifying wether a derivation is exhaustive:
  It needs to evaluate ALL variables to terminal symbols,
  i.e. have exhaustively applied production rules.-/
def ContextFreeDerivation.exhaustiveCondition
  {G : ContextFreeGrammar α nt} {u v : Word (G.V ⊕ G.Z)}
  (_ : ContextFreeDerivation G u v) : Prop :=
  ∀ symbol ∈ v, Sum.isRight symbol

/--Condition specifying wether a derivation does one or more step,
  i.e. is not a 0-step derivation.-/
def ContextFreeDerivation.nonZeroStepCondition
  {G : ContextFreeGrammar α nt} {u v : Word (G.V ⊕ G.Z)}
  (cfd : ContextFreeDerivation G u v) : Prop :=
  (¬ ∃ h_same, cfd = ContextFreeDerivation.same h_same)

/--Condition specifying wether a derivation begins in either a single variable or a single terminal.-/
def ContextFreeDerivation.startsIn1Condition
  {G : ContextFreeGrammar α nt} {u v : Word (G.V ⊕ G.Z)}
  (_ : ContextFreeDerivation G u v) : Prop :=
  (u.len = 1)

/--Decide wether this cfd is exhaustive.-/
def ContextFreeDerivation.decideExhaustive
  (cfd : ContextFreeDerivation G u v)
  : Decidable (cfd.exhaustiveCondition) :=
  v.decideIsAllZ

-- @Decidable.by_cases (var = rule.lhs) (Decidable (PreDerivationTree.treeValid (PreDerivationTree.inner var children rule))) _

instance (cfd : ContextFreeDerivation G u v) : Decidable (cfd.exhaustiveCondition) := cfd.decideExhaustive

/--Decide wether this cfd satisfies the non-zero step condition.-/
def ContextFreeDerivation.decideNonZeroStepCondition
  (cfd : ContextFreeDerivation G u v)
  : Decidable (cfd.nonZeroStepCondition) :=
  match cfd with
  | same h_same => isFalse (by simp [nonZeroStepCondition, h_same])
  | step _ _ _ => isTrue (by simp [nonZeroStepCondition])

instance (cfd : ContextFreeDerivation G u v) : Decidable (cfd.nonZeroStepCondition) := cfd.decideNonZeroStepCondition

/--Decide wether this cfd satisfies the starts-in-1 condition.-/
def ContextFreeDerivation.decideStartsIn1
  (cfd : ContextFreeDerivation G u v)
  : Decidable (cfd.startsIn1Condition) :=
  match u_len : u.len with
  | 0 => isFalse (by simp [ContextFreeDerivation.startsIn1Condition, u_len])
  | Nat.succ 0 => isTrue (by simp [ContextFreeDerivation.startsIn1Condition, u_len])
  | Nat.succ (Nat.succ n) => isFalse (by simp [ContextFreeDerivation.startsIn1Condition, u_len])

instance (cfd : ContextFreeDerivation G u v) : Decidable (cfd.startsIn1Condition) := cfd.decideStartsIn1

/--Is this context-free derivation exhaustive?:
  It needs to evaluate ALL variables to terminal symbols,
  i.e. have exhaustively applied production rules.-/
def ContextFreeDerivation.isExhaustive
  {G : ContextFreeGrammar α nt} {u v : Word (G.V ⊕ G.Z)}
  (cfd : ContextFreeDerivation G u v) : Bool :=
  @Decidable.by_cases (cfd.exhaustiveCondition) (Bool) _
  (fun _ => True)
  (fun _ => False)

/--Does this context-free derivation start in a single symbol,
  i.e. a single variable (root) or a single terminal symbol (leaf).-/
def ContextFreeDerivation.startsIn1
  {G : ContextFreeGrammar α nt} {u v : Word (G.V ⊕ G.Z)}
  (cfd : ContextFreeDerivation G u v) : Bool :=
  @Decidable.by_cases (cfd.startsIn1Condition) (Bool) _
  (fun _ => True)
  (fun _ => False)

/--Structure: Define exhaustive contextfree derivations. They -/
structure ExhaustiveContextFreeDerivation {G : ContextFreeGrammar α nt} (u : Word (G.V ⊕ G.Z)) (v : Word (G.V ⊕ G.Z)) where
  derivation : @ContextFreeDerivation α nt G u v
  exhaustive : derivation.exhaustiveCondition
  startsIn1 : derivation.startsIn1Condition
  -- nonZero: isn't necessary: exhaustive means .leaf constructor can be used.
  deriving DecidableEq

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

-- TODO make this use colelctDerivationTreeNodes
def ContextFreeDerivation.toDerivationTree
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (cfd : @ContextFreeDerivation α nt G u v)
  (h_exhaustive : cfd.exhaustiveCondition)
  (h_starts_in_1 : cfd.startsIn1Condition) :
  DerivationTree G :=
    match h_constructor : cfd with
    | same h_same => sorry
    | @step _ _ _ _ u' _ dstep derivation sound => by
      let var := dstep.prod.val.lhs
      let var_as_word : (Word (G.V ⊕ G.Z)) := Word.mk [Sum.inl var]
      have h_dstep_sound := dstep.sound
      simp at h_dstep_sound
      have h_dstep_sound₂ : u = dstep.pre * (Word.mk [@Sum.inl G.V G.Z dstep.prod.val.lhs]) * dstep.suf := by exact h_dstep_sound
      rw [startsIn1Condition] at h_starts_in_1
      rw [h_dstep_sound₂] at h_starts_in_1
      rw [Word.length_mul_eq_add, Word.length_mul_eq_add] at h_starts_in_1
      have h_var_len : (Word.mk ([@Sum.inl G.V G.Z dstep.prod.val.lhs])).len = 1 := by tauto
      rw [h_var_len] at h_starts_in_1
      have h_pre_suff_len_0 : Word.len dstep.pre + Word.len dstep.suf = 0 := by
        simp
        rw [Nat.add_comm (Word.len dstep.pre), Nat.add_assoc] at h_starts_in_1
        have h_rw_helper₁ : ∀ a : ℕ, (1 + a = 1) ↔ (a = 0) := by simp
        apply Iff.mp (h_rw_helper₁ (Word.len dstep.pre + Word.len dstep.suf)) at h_starts_in_1
        apply Nat.add_eq_zero.mp at h_starts_in_1
        rw [Word.eps_len_0.symm,Word.eps_len_0.symm]
        exact h_starts_in_1
      have h_pre_is_eps : dstep.pre = ε := by
        apply Nat.add_eq_zero.mp at h_pre_suff_len_0
        apply (Word.eps_len_0.mp h_pre_suff_len_0.left)
      have h_suf_is_eps : dstep.suf = ε := by
        apply Nat.add_eq_zero.mp at h_pre_suff_len_0
        apply (Word.eps_len_0.mp h_pre_suff_len_0.right)
      simp [h_pre_is_eps, h_suf_is_eps] at h_dstep_sound₂
      have u_is_var_as_word : u = var_as_word := by simp [h_dstep_sound₂, var_as_word, var]
      let collectFollowVars := dstep.prod.val.rhs.collectVars --respects left to right

      let children : NEPreDerivationTreeList G := sorry
      let rule : G.productions := dstep.prod
      let h_rule_lhs : rule.1.lhs = var := by simp
      let h_rule_rhs : rule.1.rhs = NEPreDerivationTreeList.levelWord children := sorry
      let childrenValid : children.treeValid := sorry
      exact DerivationTree.inner var children rule h_rule_lhs h_rule_rhs childrenValid
#check Nat.lt_succ_of_le
/--Collect the DerivationTree Nodes. Each node in the list
  corresponds to exactly one variable in u and each variable in
  u has a returned DerivationTree node. Cannot be called for 0-step
  derivations.-/
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
          rw [Word.mk_from_list_len]
          simp
      have pre_len_less_u_len : dstep.pre.len < u.len := by
        rw [eq_iff_le_not_lt] at u_comp
        apply And.left at u_comp
        have var_len_1 : Word.len (Word.mk [@Sum.inl G.V G.Z dstep.prod.val.lhs]) = 1 := by
          rw [Word.mk_from_list_len]
          simp
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
          have rhs_comp : Word.len (dstep.prod.val.rhs) = (Word.mk [@Sum.inl G.V G.Z dstep.prod.val.lhs]).len + (rhs_symbol_count-1) := by
            simp [rhs_symbol_count, lhs_len]
            rw [add_comm, Nat.sub_add_cancel]
            exact h_rhs_non_empty
          simp [rhs_comp, Word.length_mul_eq_add]
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
            let index₃ : Fin (List.length rightSide) := ⟨ index, (by simp [Word.list_length_eq_word_len]) ⟩
            let symbol : _ := Word.get rightSide index₃
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
          simp [h_u_vs_u'_len, u_comp.symm]⟩
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

/--Theorem: It is possible to augment a prefix-word`w`to the left side of in- and output of a
  valid derivation. We recieve a valid derivation.-/
theorem ContextFreeDerivation.augment_left {u v w: Word _} (d: ContextFreeDerivation G u v) :
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
def ContextFreeDerivation.augment_left_mul {u v w: Word _} (d: ContextFreeDerivation G u v) :
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
def ContextFreeDerivation.augment_left_cons {u v: Word _} (d: ContextFreeDerivation G u v) :
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
theorem ContextFreeDerivation.augment_right {u v: Word (G.V ⊕ G.Z)} (d: ContextFreeDerivation G u v) :
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
def ContextFreeDerivation.augment_right_mul {u v: Word (G.V ⊕ G.Z)} (d: ContextFreeDerivation G u v) :
  ContextFreeDerivation G (u.append w) (v.append w) := by
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
def ContextFreeDerivation.augment_right_cons {u v: Word (G.V ⊕ G.Z)} (d: ContextFreeDerivation G u v) :
  ContextFreeDerivation G (u.append w) (v.append w) := by
  match d with
  | .same h => apply ContextFreeDerivation.same; simp [h]
  | .step s d' sound =>
    apply ContextFreeDerivation.step
    . exact d'.augment_right_cons
    swap
    . exact s.augment_right w
    . rw [<- sound]; exact s.augment_right_result _

/--Concatenate two derivations: Such that they are left/right of each other.-/
def ContextFreeDerivation.concat
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
      simp [Grammar.DerivationStep.result, step_augmented_result]
      simp [Grammar.DerivationStep.result] at sound₁
      rw [← sound₁]

def ExhaustiveContextFreeDerivation.toDerivationTree
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (ecfd : @ExhaustiveContextFreeDerivation α nt G u v) :
  DerivationTree G :=
    ecfd.derivation.toDerivationTree ecfd.exhaustive ecfd.startsIn1

def ExhaustiveContextFreeDerivation.fromProdRuleList
  {G : ContextFreeGrammar α nt}
  (startWord : Word (G.V ⊕ G.Z))
  (endWord : Word (G.V ⊕ G.Z))
  (prodRules : List G.productions) :
  ExhaustiveContextFreeDerivation startWord endWord :=
    sorry

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


-- Some advanced tactics to try out at some point:
-- rcases
--    matchexpression die gleichzeitig die Teile benennt
-- obtain
-- z.B. obtain ⟨ Q, uniqueness⟩ := M
--    aus etwas komplexem zwei sachen rausholen
-- rintro
--    intro iwas

end ContextFreeGrammar

--=============================================================
-- Section: Pumping Lemma
--=============================================================

class ContextFreeLanguage (α : Type) {nt : Type} (language : Language α) where
  language := language
  generated := ∃ CFG : (ContextFreeGrammar α nt), CFG.GeneratedLanguage = language



--=============================================================
-- Section: Miscellaneous Theorems
--=============================================================

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

/--Given a word derivation step

  a::xs (G)=> w,

  construct a set of possible derivation steps of the form

  xs (G)=> w.tail .-/
def Grammar.DerivationStep.cancelLeft
  { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (d: G.DerivationStep lhs) (h_lhs: lhs = (.inr a :: xs)):
  -- Proof of existence and construction method for a specific set
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

/--Given a derivation a::xs (G)=>* w,
  construct a derivation xs (G)=>* w-/
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

/--Theorem: Looking only at the xs in a derivation a::xs (G)=>* w
  when the xs are constructed using the "same"-constructor yields
  a 0 length derivation.-/
theorem Grammar.Derivation.cancelLeft_len_same
  { w: Word G.Z } { h_rhs: _ }:
  (cancelLeft (w := w) (.same h) h_lhs h_rhs).len = 0 := by
  simp [cancelLeft]
  unfold len
  rfl

/--Theorem: Terminal symbols on the left-hand side don't induce derivation steps:
  The derivation a::xs (G)=>* w
  and the derivation xs (G)=>* w.tail have the same length.-/
theorem Grammar.Derivation.cancelLeft_len
  (d: G.Derivation lhs rhs):
  (d.cancelLeft h_lhs h_rhs).len = d.len := by
  match d with
  | .same _ => simp [len]
  | .step _ _ _ =>
    simp [len]
    apply cancelLeft_len
