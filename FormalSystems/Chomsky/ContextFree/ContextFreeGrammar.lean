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
def PreDerivationTree.result {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Word (G.Z)
  | .leaf terminalWord => Word.mk (terminalWord.map (fun terminal => terminal))
  | .inner _ children _ => children.result
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.result {G : ContextFreeGrammar α nt} : (NEPDT : NEPreDerivationTreeList G) → Word (G.Z)
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
      var = rule.lhs ∧
      /- 2 The children match the production rules result. -/
      children.levelWord = rule.rhs ∧
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
        @Decidable.by_cases (var = rule.lhs) (Decidable (PreDerivationTree.treeValid (PreDerivationTree.inner var children rule))) _
          (fun h_lhs : (var = rule.lhs) =>
            @Decidable.by_cases (children.levelWord = rule.rhs) _ _
              (fun h_rhs : (children.levelWord = rule.rhs) =>
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
                (fun h_rhs : ¬(children.levelWord = rule.rhs) =>
                isFalse (by
                  apply Not.intro; intro h_not
                  rw [PreDerivationTree.treeValid] at h_not
                  absurd h_not.right.left
                  exact h_rhs
                )
              )
          ) (fun h_lhs : ¬(var = rule.lhs) =>
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
  (ind_basis : ∀ terminalWord : Word G.Z , prop (PreDerivationTree.leaf terminalWord))
  /-Base case for NEPDTLs.-/
  (ind_basis₂ :
    ∀ PDT : PreDerivationTree G,
      prop PDT → prop₂ (NEPreDerivationTreeList.single PDT))
  /-Induction step for PDTs.-/
  (ind_step :
    ∀ (v : G.V) (children : NEPreDerivationTreeList G)
    (rule : ContextFreeProduction G.Z G.V),
    (ind_hyp : prop₂ children)
    →
    prop (PreDerivationTree.inner v children rule))
  /-Induction step for NEPDTLs.-/
  (ind_step₂ :
    ∀ PDT : PreDerivationTree G, ∀ NEPDTL₂ : NEPreDerivationTreeList G,
      prop PDT → prop₂ NEPDTL₂ → prop₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂))
  : ∀ PDT : PreDerivationTree G, prop PDT
  := @PreDerivationTree.rec α nt G prop prop₂
    (fun terminalWord =>
      by apply ind_basis terminalWord)
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
  (ind_basis : ∀ terminalWord : Word G.Z , prop (PreDerivationTree.leaf terminalWord))
  /-Base case for NEPDTLs.-/
  (ind_basis₂ :
    ∀ PDT : PreDerivationTree G,
      prop PDT → prop₂ (NEPreDerivationTreeList.single PDT))
  /-Induction step for PDTs.-/
  (ind_step :
    ∀ (v : G.V) (children : NEPreDerivationTreeList G)
    (rule : ContextFreeProduction G.Z G.V),
    (ind_hyp : prop₂ children)
    →
    prop (PreDerivationTree.inner v children rule))
  /-Induction step for NEPDTLs.-/
  (ind_step₂ :
    ∀ PDT : PreDerivationTree G, ∀ NEPDTL₂ : NEPreDerivationTreeList G,
      prop PDT → prop₂ NEPDTL₂ → prop₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂))
  : ∀ NEPDTL : NEPreDerivationTreeList G, prop₂ NEPDTL
  := @NEPreDerivationTreeList.rec α nt G prop prop₂
    (fun terminalWord =>
      ind_basis terminalWord)
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

/--Construct a derivation tree child from the a proof of validity of
  the list of children and the child's membership in this list.-/
def DerivationTree.fromChild
  {G : ContextFreeGrammar α nt} {children : NEPreDerivationTreeList G} {child : PreDerivationTree G}
  (childrenValid : children.treeValid) (h_child_mem : child ∈ children.asList) : DerivationTree G :=
  match child with
  | .leaf terminalWord => DerivationTree.leaf terminalWord
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

  `∀ terminalWord : Word G.Z , prop (DerivationTree.leaf terminalWord)`

  Induction step requires a proof, that from prop being valid for
  an unknown collection of children we can generate prop(parent), where the parent is synthesized from
  an unknownm, but valid, derivation tree construction.

  `∀ (v : G.V) (children : NEPreDerivationTreeList G) (rule : ContextFreeProduction G.Z G.V) (h_rule_lhs : rule.lhs = v) (h_rule_rhs : rule.rhs = children.levelWord) (childrenValid : children.treeValid), (ind_hyp : ∀ child, (h_mem : child ∈ children.asList) → prop (DerivationTree.fromChild childrenValid (h_mem : child ∈ children.asList))) → prop (DerivationTree.inner v children rule h_rule_lhs h_rule_rhs childrenValid)`-/
@[elab_as_elim]
def DerivationTree.induction_principle {G : ContextFreeGrammar α nt}
  /-For any given property,-/
  (prop : DerivationTree G → Prop)
  /-if we can prove the prop for leaf DTs-/
  (ind_basis : ∀ terminalWord : Word G.Z , prop (DerivationTree.leaf terminalWord))
  /- and...-/
  (ind_step :
    /- for ANY inner DT-/
    ∀ (v : G.V) (children : NEPreDerivationTreeList G)
    (rule : ContextFreeProduction G.Z G.V) (h_rule_lhs : rule.lhs = v)
    (h_rule_rhs : rule.rhs = children.levelWord) (childrenValid : children.treeValid),
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
              (∀ (terminalWord : Word { x // x ∈ G.Z }), prop (leaf terminalWord)) →
              /-... and a match from the induction step via actual recursive constructor for DTs to the
              more easily useable fromChild induction step for DTs.-/
              (∀
                (v : { x // x ∈ G.V }) (children : NEPreDerivationTreeList G) (rule : ContextFreeProduction G.Z G.V)
                (h_rule_lhs : rule.lhs = v) (h_rule_rhs : rule.rhs = NEPreDerivationTreeList.levelWord children)
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
              (∀ (terminalWord : Word { x // x ∈ G.Z }), prop (leaf terminalWord)) →
              /-... and a match from the induction step via actual recursive constructor for DTs to the
              more easily useable fromChild induction step for DTs.-/
              (∀
                (v : { x // x ∈ G.V }) (children : NEPreDerivationTreeList G) (rule : ContextFreeProduction G.Z G.V)
                (h_rule_lhs : rule.lhs = v) (h_rule_rhs : rule.rhs = NEPreDerivationTreeList.levelWord children)
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
          have propHelper_basis : (∀ (terminalWord : Word G.Z), propHelper (PreDerivationTree.leaf terminalWord)) := by
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
          have propHelper_step : (∀ (v : { x // x ∈ G.V }) (children : NEPreDerivationTreeList G) (rule : ContextFreeProduction G.Z G.V),
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
  | PreDerivationTree.leaf tw => tw.ZtoVZ
  | PreDerivationTree.inner v _ _ => [Sum.inl v]

/--Return the variable from which we begin deriving or bottom if we are a leaf.-/
def DerivationTree.fromVarOrBot {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : WithBot (G.V) := match DT.tree with
| PreDerivationTree.leaf _ => ⊥
| PreDerivationTree.inner v _ _ => v

/--Return the variable from which we begin deriving if the tree is total.-/
def DerivationTree.fromVar {G : ContextFreeGrammar α nt} [DecidableEq { x // x ∈ G.V }] (DT : DerivationTree G) (h_isTotal : DT.isTotal) : (G.V) := by
  have h_neverTerminal : _ := DT.total_trees_not_leaves₂ h_isTotal
  let var : _ := DT.fromVarOrBot
  have h_neverBot : var ≠ ⊥ := by
    cases h_constructor : DT.tree
    case leaf tw =>
      cases h_neverTerminal; case intro var₂ h_neverTerminal₂ =>
        cases h_neverTerminal₂; case intro _ h_neverTerminal₃ =>
          cases h_neverTerminal₃; case intro _ h_neverTerminal₄ =>
            absurd h_neverTerminal₄
            simp [h_constructor]
    case inner v c r =>
      have h_def : var = DT.fromVarOrBot := by simp
      simp [h_def, fromVarOrBot, h_constructor]
  exact WithBot.unbot var h_neverBot

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
      let cList := c.asList
      exact List.map (λ child =>
        have a : ∃ c ∈ cList, c = child := by
          have b : _ := NEPDTL.asList_never_nil
          --apply Not.elim at b
          by_contra h_contra
          absurd b
          sorry

        @DerivationTree.fromChild α nt G c child ctv ( by

        sorry
      )) cList

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

def ContextFreeDerivation.toDerivationTree
  {G : ContextFreeGrammar α nt} {u : Word (G.V ⊕ G.Z) } {v : Word (G.V ⊕ G.Z)}
  (cfd : @ContextFreeDerivation α nt G u v)
  (h_multipleStep : ¬ ∃ h_same, cfd = ContextFreeDerivation.same h_same) :
  DerivationTree G :=
    match h_constructor : cfd with
    | same h_same => by
      have h_singleStep : ∃ h_same, cfd = ContextFreeDerivation.same h_same := by use h_same
      rw [← h_constructor] at h_multipleStep
      contradiction

      --Default? Bottom?

    | step dstep derivation sound =>

      sorry

def DerivationTree.toContextFreeDerivation
  {G : ContextFreeGrammar α nt}
  [DecidableEq G.V]
  (DT : DerivationTree G) :
  (cfd : @ContextFreeDerivation α nt G DT.fromAny (@Word.ZtoVZ _ _ _ _ G DT.result)) :=

  sorry

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
