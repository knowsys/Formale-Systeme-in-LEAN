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

--variable {CFP : ContextFreeProduction Z V}
--#check (↑CFP : GenericProduction Z V).eq_iff_lhs_and_rhs_eq
/- GenericProduction.eq_iff_lhs_and_rhs_eq
  (([Sum.inl CFP.lhs] →ₚ CFP.rhs)
    (instCoeContextFreeProductionGenericProduction.proof_1
      CFP)) : ∀ (p₂ : GenericProduction Z V),
  ([Sum.inl CFP.lhs] →ₚ CFP.rhs) ⋯ = p₂ ↔
    (([Sum.inl CFP.lhs] →ₚ CFP.rhs) ⋯).lhs = p₂.lhs ∧ (([Sum.inl CFP.lhs] →ₚ CFP.rhs) ⋯).rhs = p₂.rhs -/

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
-- Section: Context Free Grammar
--=============================================================

/--Define Context Free Grammars to have context free production rules.-/
def ContextFreeGrammar (α nt: Type) := @Grammar α nt ContextFreeProduction _

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

--Note: Need to name all type parameters explicitly for coercion to work!

--variable {CFDS : (@ContextFreeDerivationStep α nt G u)}
--#check ((↑CFDS) : @Grammar.DerivationStep α nt GenericProduction _ (↑G) u).result

--Idea: Split everything up into many sub-tasks
mutual
/--Basic structure of a context-free derivation tree without validity-constraints. Values returned by all sub-defined functions are only
  ordered correctly if ordered correctly during definition.-/
inductive PreDerivationTree (G : ContextFreeGrammar α nt)
  | leaf (terminalWord : Word G.Z) : PreDerivationTree G
  | inner (var : G.V) (children : NEPreDerivationTreeList G) (prodRule : (ContextFreeProduction G.Z G.V)) : PreDerivationTree G
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
def PreDerivationTree.decEq {G : ContextFreeGrammar α nt} [DecidableEq α] [DecidableEq nt] : (PDT₁ PDT₂ : PreDerivationTree G) → Decidable (Eq PDT₁ PDT₂)
| .leaf terminalWord₁ , .leaf terminalWord₂ =>
    match (terminalWord₁.hasDecEq terminalWord₂) with
      | isTrue h_isTrue => isTrue (by rw [h_isTrue])
      | isFalse h_isFalse => isFalse (by
          apply Not.intro
          intro h_not
          simp at h_not
          contradiction)
| .leaf terminalWord₁ , .inner _ _ _ =>
  isFalse (by
    apply Not.intro
    intro h_not
    contradiction)
| .inner _ _ _ , .leaf terminalWord₂ =>
  isFalse (by
    apply Not.intro
    intro h_not
    contradiction)
| .inner var₁ children₁ prodRule₁, .inner var₂ children₂ prodRule₂ =>
  match (prodRule₁.decEq prodRule₂) with
    | isFalse h_isFalse => isFalse (by simp; intro _ _ ; exact h_isFalse)
    | isTrue h_isTrue_prodRule =>
      match (children₁.decEq children₂) with
        | isFalse h_isFalse => isFalse (by simp; intro _ _; contradiction)
        | isTrue h_isTrue_children =>
          match (decEq var₁ var₂) with
            | isFalse h_isFalse => isFalse (by
              intro h_not;
              --rw [h_isTrue_children, h_isTrue_prodRule] at h_not
              simp [h_isTrue_children, h_isTrue_prodRule] at h_not
              rw [h_not] at h_isFalse
              contradiction)
            | isTrue h_isTrue_var => isTrue (by
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
def PreDerivationTree.prodRuleList {G : ContextFreeGrammar α nt} : (PreDerivationTree G) → List (ContextFreeProduction G.Z G.V)
  | .leaf _ => []
  | .inner _ children prodRule => prodRule :: children.prodRuleList
/--Get the list of used production rules. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.prodRuleList {G : ContextFreeGrammar α nt} : (NEPDT : (NEPreDerivationTreeList G)) → List (ContextFreeProduction G.Z G.V)
  | .single PDT => PDT.prodRuleList
  | .cons PDT NEPDT₂ => PDT.prodRuleList ++ NEPDT₂.prodRuleList
end

mutual
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.result {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Word (G.V ⊕ G.Z)
  | .leaf terminalWord => Word.mk (terminalWord.map (fun terminal => Sum.inr terminal))
  | .inner _ children _ => children.result
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.result {G : ContextFreeGrammar α nt} : (NEPDT : NEPreDerivationTreeList G) → Word (G.V ⊕ G.Z)
  | .single PDT => PDT.result
  | .cons PDT NEPDT₂ => Word.concatListOfWords [PDT.result , NEPDT₂.result]
end

mutual
/--The intermediate level word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.levelWord {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Word (G.V ⊕ G.Z)
  | .leaf terminalWord => Word.mk (terminalWord.map (fun terminal => Sum.inr terminal))
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

/--Given a NEPreDerivationTreeList, its members have less nodes than the whole list.-/
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
      -- 1 The production rule is applicable in this step.
      var = rule.lhs ∧
      -- 2 The children match the production rules result.
      children.levelWord = rule.rhs ∧
      -- 3 The children are valid.
      children.treeValid
/- treeWord children = rule.rhs ∧ children.all (fun c => @decide (treeValid c) (Classical.propDecidable _))
termination_by t => depth t -/
/--A list of Derivation Trees is valid, if each of its children is valid.-/
def NEPreDerivationTreeList.treeValid {G : ContextFreeGrammar α nt} (NEPDTL : NEPreDerivationTreeList G) : Prop :=
  match NEPDTL with
  | .single PDT => PDT.treeValid
  | .cons PDT NEPDTL₂ => PDT.treeValid ∧ NEPDTL₂.treeValid
end

/--Does this tree begin in the starting symbol?-/
def PreDerivationTree.isFromStartingSymbol {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Prop
| .leaf _ => False
| .inner var _ _ => var = G.start


/--Structure: A context-free derivation tree. Use`tree : PreDerivationTree`to define its structure and provide
  a validity proof`valid : treeValid tree`. Note that the definition of`tree`should be in correct order left-to-right.-/
structure DerivationTree (G : ContextFreeGrammar α nt) where
  tree : PreDerivationTree G
  valid : tree.treeValid
  deriving DecidableEq

/--Construct a context-free derivation-tree leaf from a terminal word.-/
@[match_pattern]
def DerivationTree.leaf {G : ContextFreeGrammar α nt} (w : Word G.Z) : DerivationTree G := {
  tree := PreDerivationTree.leaf w
  valid := by rw [PreDerivationTree.treeValid]; simp
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
  (rule : ContextFreeProduction G.Z G.V)
  (h_rule_lhs : rule.lhs = v) (h_rule_rhs : rule.rhs = children.levelWord) (childrenValid : children.treeValid)
  : DerivationTree G := {
    tree := PreDerivationTree.inner v children rule
    valid := by
      rw[PreDerivationTree.treeValid, h_rule_lhs, h_rule_rhs]
      simp; exact childrenValid
}

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
def EP.StoA : ContextFreeProduction ExampleTerminals ExampleVariables := EP[0]
def EP.StoM : ContextFreeProduction ExampleTerminals ExampleVariables := EP[1]
def EP.StoV : ContextFreeProduction ExampleTerminals ExampleVariables := EP[2]
def EP.AtoSplusS : ContextFreeProduction ExampleTerminals ExampleVariables := EP[3]
def EP.MtoStimesS : ContextFreeProduction ExampleTerminals ExampleVariables := EP[4]
def EP.Vtox : ContextFreeProduction ExampleTerminals ExampleVariables := EP[5]
def EP.Vtoy : ContextFreeProduction ExampleTerminals ExampleVariables := EP[6]
def EP.Vtoz : ContextFreeProduction ExampleTerminals ExampleVariables := EP[7]

def ExampleGrammar: @ContextFreeGrammar Char Char where
  Z := { 'x', 'y', 'z', '(', ')', '+', '*' }
  V := { 'A', 'M', 'S', 'V' }
  start := ⟨ 'S', by simp ⟩
  productions := EP.toFinset

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
.leaf [ ⟨ '(' , by decide⟩ ]
def ExamplePreTreel4_0 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ 'x' , by decide⟩ ]
def ExamplePreTreel2_1 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ '*' , by decide⟩ ]
def ExamplePreTreel4_1 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ '(' , by decide⟩ ]
def ExamplePreTreel6_0 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ 'y' , by decide⟩ ]
def ExamplePreTreel4_2 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ '+' , by decide⟩ ]
def ExamplePreTreel6_1 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ 'z' , by decide⟩ ]
def ExamplePreTreel4_3 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ ')' , by decide⟩ ]
def ExamplePreTreel2_2 : PreDerivationTree ExampleGrammar :=
.leaf [ ⟨ ')' , by decide⟩ ]

def DT_Test : DerivationTree ExampleGrammar :=
  DerivationTree.inner ⟨ 'V', by decide⟩ DT[ExamplePreTreel6_1] EP.Vtoz (by decide) (by decide) (by decide)

def ExamplePreTreei3_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'V' , by decide⟩ DT[ExamplePreTreel4_0] EP.Vtox
def ExamplePreTreei2_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'S' , by decide⟩ DT[ExamplePreTreei3_0] EP.StoV
def ExamplePreTreei5_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'V' , by decide⟩ DT[ExamplePreTreel6_0] EP.Vtoy
def ExamplePreTreei4_0 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'S' , by decide⟩ DT[ExamplePreTreei5_0] EP.StoV
def ExamplePreTreei5_1 : PreDerivationTree ExampleGrammar :=
.inner ⟨ 'V' , by decide⟩ DT[ExamplePreTreel6_0] EP.Vtoz
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

--/--Return the root of a context-free derivation tree. Is itself though.-/
--def DerivationTree.root {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : (DerivationTree G) := DT

/--A context-free derivation tree is total or complete if and only if it begins from
  the starting symbol of its grammar.-/
def DerivationTree.isTotal {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : (Prop) :=
  DT.tree.isFromStartingSymbol
/--A context-free derivation tree is total or complete if and only if it begins from
  the starting symbol of its grammar.-/
def DerivationTree.isComplete {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : (Prop) := DT.isTotal

/--Return the root of a context-free derivation tree. Is itself though.-/
def DerivationTree.startOrBot {G : ContextFreeGrammar α nt} : (DT : DerivationTree G) → (WithBot G.V)
| .leaf w => ⊥
| .inner var children rule _ _ _ => sorry --match child. with
  --|

/-- u ≺(G)⇒* v -notation for context-free tree-based derivations. Is the proposition that there
  exists a derivation (∃) from u to v in G.-/
notation:40 var:40 " ≺(" G:40 ")⇒⁺ " word:41 => (∃ dt ∈ (DerivationTree G), dt.start = var ∧ dt.result = word)

def DerivationTree.depth {G : ContextFreeGrammar α nt} : (DT : DerivationTree G) → () := sorry
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

--IMPORTANT: theorems are not computable!
/--Define an embedding of context-free derivations in generic derivations.-/
def ContextFreeDerivation.toDerivation
    (cfd : @ContextFreeDerivation α nt G u v) :
    (@Grammar.Derivation α nt GenericProduction _ (↑G) u v) :=
    match cfd with
    | same h_same =>
      Grammar.Derivation.same h_same
    | step dStep derivation h_sound =>
      Grammar.Derivation.step dStep derivation.toDerivation h_sound

--Coercion CFDerivation into generic Derivations
instance : Coe (@ContextFreeDerivation α nt G v w) (@Grammar.Derivation α nt GenericProduction _ (↑G) v w) where
  coe cfDerivation := ContextFreeDerivation.toDerivation cfDerivation

-- variable {CDF : (@ContextFreeDerivation α nt G u v)}
-- #check (↑(CDF) : @Grammar.Derivation α nt GenericProduction _ G u v).len
-- Grammar.Derivation.len (ContextFreeDerivation.toDerivation CDF) : ℕ

/-- u CF(G)⇒* v -notation for context-free derivations. Is the proposition that there
  exists a derivation (∃) from u to v in G.-/
notation:40 u:40 " CF(" G:40 ")⇒* " v:41 => (Nonempty $ ContextFreeDerivation G u v)

end ContextFreeGrammar

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
