import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor

import FormalSystems.Chomsky.ContextFree.ContextFreeGrammar
--================================================================================
-- File: PreDerivationTree
/-  Containts PreDerivationTree and NEPreDerivationTreeList definitions.
    They are required to pre-build the trees, enforce the existence of children
    at child nodes.
-/
--================================================================================

namespace ContextFreeGrammar

mutual
/--Basic structure of a context-free derivation tree without validity-constraints. Values returned by all sub-defined functions are only
  ordered correctly if ordered correctly during definition.

  TODO: The leaves have either one or zero symbols associated with them.
  This is done using the Option type. It might be better to instead add
  a third constructor for leaves that are the result of production rules
  that go to ε.-/
inductive PreDerivationTree (G : ContextFreeGrammar α nt)
  | leaf (terminal : Option G.Z) : PreDerivationTree G
  | inner (var : G.V) (children : NEPreDerivationTreeList G) (prodRule : (G.productions)) : PreDerivationTree G
-- Originally I wanted a parameter: (children_non_empty : 0 < List.length (↑children))
-- But: children is recursively bound => doesn't work
-- To still ensure non-emptiness of children we use the below mutual structure
/--Ensure that we have a non-empty list of children with this structure. Is basically
  a list of PreDerivationTree G elements.-/
inductive NEPreDerivationTreeList (G : ContextFreeGrammar α nt)
  | single (PDT : PreDerivationTree G) : NEPreDerivationTreeList G
  | cons (PDT : PreDerivationTree G) (NEPDTL : NEPreDerivationTreeList G) : NEPreDerivationTreeList G
end

-- TODO: maybe this can be derived somehow instead of implementing this by hand?
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
  match (decEq prodRule₁.val prodRule₂.val) with
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

namespace NEPreDerivationTreeList
  /--Convert to a List (PreDerivationTree G). Only correct order if child nodes were assigned left-to-right.-/
  def asList (NEPDTL : NEPreDerivationTreeList G) : List (PreDerivationTree G) := match NEPDTL with
    | single PDT => [PDT]
    | cons (PDT) (NEPDTL₂) => PDT :: NEPDTL₂.asList

  /--Folds a function over a non-empty pre-derivation tree list from the left:
  `foldl f z NEPDT(a, b, c) = f (f (f z a) b) c`-/
  @[specialize]
  def foldl
    (f : α → (PreDerivationTree G) → α) :
    (init : α) → (NEPreDerivationTreeList G) → α
    | a, single PDT => f a PDT
    | a, cons PDT NEPDTL₂ => NEPreDerivationTreeList.foldl f (f a PDT) NEPDTL₂

  /--Theorem: The lists constructed with asList are never [].-/
  theorem asList_never_nil (NEPDTL : NEPreDerivationTreeList G) :
    ¬ NEPDTL.asList = [] := by
    apply Not.intro
    intro h
    cases NEPDTL
    repeat rw [NEPreDerivationTreeList.asList] at h; contradiction

  /--Theorem: The lists constructed with asList have non-zero length.-/
  theorem asList_length (NEPDTL : NEPreDerivationTreeList G) :
    NEPDTL.asList.length > 0 := by
    apply List.length_pos_of_ne_nil NEPDTL.asList_never_nil
end NEPreDerivationTreeList

mutual
/--Return a list of the context-free node's children. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.nodeList (NEPDT : NEPreDerivationTreeList G) : List (PreDerivationTree G) := match (NEPDT : NEPreDerivationTreeList G) with
  | .single PDT => PDT.nodeList
  | .cons PDT NEPDT₂ => PDT.nodeList ++ NEPDT₂.nodeList

/--Return a list of the context-free node's children. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.nodeList (PDT : PreDerivationTree G) : List (PreDerivationTree G) := match (PDT : PreDerivationTree G) with
  | .leaf _ => [PDT]
  | .inner _ children _ => PDT :: children.nodeList
end

mutual
/--Theorem: The list of nodes returned with nodeList is never empty.-/
theorem NEPreDerivationTreeList.nodeList_never_nil
  (NEPDT : NEPreDerivationTreeList G) :
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
  (PDT : PreDerivationTree G) :
  ¬ PDT.nodeList = [] := by
    intro h_not
    cases PDT
    case leaf r =>
      rw [PreDerivationTree.nodeList] at h_not
      contradiction
    case inner v children rule =>
      rw [PreDerivationTree.nodeList] at h_not
      have _ : _ := List.cons_ne_nil (PreDerivationTree.inner v children rule) (NEPreDerivationTreeList.nodeList children)
      contradiction
end

/--Return a (possibly empty) list of this nodes children. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.children : PreDerivationTree G → List (PreDerivationTree G)
  | leaf _ => []
  | inner _ children _ => children.asList

mutual
/--Get the list of used production rules. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.prodRuleList : PreDerivationTree G → List (G.productions)
  | .leaf _ => []
  | .inner _ children prodRule => prodRule :: children.prodRuleList
/--Get the list of used production rules. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.prodRuleList : NEPreDerivationTreeList G → List (G.productions)
  | .single PDT => PDT.prodRuleList
  | .cons PDT NEPDT => PDT.prodRuleList ++ NEPDT.prodRuleList
end

mutual
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.result : PreDerivationTree G → Word (G.Z)
  | .leaf terminal =>
    match terminal with
    | none =>
      ε
    | some terminalSymbol =>
      Word.mk [terminalSymbol]
  | .inner _ children _ => children.result
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.result : NEPreDerivationTreeList G → Word (G.Z)
  | .single PDT => PDT.result
  | .cons PDT NEPDT => Word.concatListOfWords [PDT.result, NEPDT.result]
end

mutual
/--The intermediate level word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def PreDerivationTree.levelWord : PreDerivationTree G → Word (G.V ⊕ G.Z)
  | .leaf terminal =>
    match terminal with
    | none =>
      ε
    | some terminalSymbol =>
      Word.mk [Sum.inr terminalSymbol]
  | .inner var _ _ => Word.mk [(Sum.inl var)]
/--The final result-word defined by the children of a context-free tree-node. Only correct order if child nodes were assigned left-to-right.-/
def NEPreDerivationTreeList.levelWord : NEPreDerivationTreeList G → Word (G.V ⊕ G.Z)
  | .single PDT => PDT.levelWord
  | .cons PDT NEPDT => Word.concatListOfWords [PDT.levelWord , NEPDT.levelWord]
end

mutual
/--Define the depth of a context-free derivation-tree.-/
def PreDerivationTree.depth : PreDerivationTree G -> Nat
  | .leaf _ => 0
  | .inner _ children _ => children.depth + 1
/--Define the depth of a context-free derivation-tree.-/
def NEPreDerivationTreeList.depth : NEPreDerivationTreeList G -> Nat
  | .single PDT => PDT.depth
  | .cons PDT NEPDT => Nat.max PDT.depth NEPDT.depth
end

theorem NEPreDerivationTreeList.elementDepthLeq (NEPDT : NEPreDerivationTreeList G) : ∀ child ∈ NEPDT.asList, child.depth ≤ NEPDT.depth := by
  intro child h
  cases NEPDT with
  | single PDT => simp [asList] at h; rw [h]; simp [depth]
  | cons head tail =>
    conv => rhs; unfold depth
    simp [asList] at h
    simp
    cases h with
    | inl h =>
      apply Or.inl
      rw [h]
    | inr h =>
      apply Or.inr
      apply NEPreDerivationTreeList.elementDepthLeq
      exact h

theorem PreDerivationTree.childDepthSmaller (PDT: PreDerivationTree G) : ∀ child ∈ PDT.children, child.depth < PDT.depth := by
  intro child h
  cases PDT with
  | leaf _ => unfold children at h; simp at h
  | inner _ children _ =>
    conv => rhs; unfold depth
    apply Nat.lt_succ_of_le
    apply NEPreDerivationTreeList.elementDepthLeq
    exact h

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
  (PDT : PreDerivationTree G) :
  PDT.nodeList = [PDT] ∨
  PDT.nodeList = List.foldl append_nodeLists [PDT] PDT.children := by
    cases PDT
    case leaf w =>
      apply Or.inl
      unfold PreDerivationTree.nodeList
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
  (NEPDT : NEPreDerivationTreeList G) :
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
  (NEPDT : NEPreDerivationTreeList G) :
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
  (PDT : PreDerivationTree G) :
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
def PreDerivationTree.treeValid (PDT : PreDerivationTree G) : Prop :=
  match PDT with
  | .leaf _ => True
  | .inner var children rule =>
      /- 1 The production rule is applicable in this step.-/
      var = rule.1.lhs ∧
      /- 2 The children match the production rules result. -/
      children.levelWord = rule.1.rhs ∧
      /- 3 The children are valid. -/
      children.treeValid
/--A list of Derivation Trees is valid, if each of its children is valid.-/
def NEPreDerivationTreeList.treeValid (NEPDTL : NEPreDerivationTreeList G) : Prop :=
  match NEPDTL with
  | .single PDT => PDT.treeValid
  | .cons PDT NEPDTL₂ => PDT.treeValid ∧ NEPDTL₂.treeValid
end

/--Theorem: If a list of tree nodes are valid, then so is any of its members.-/
theorem NEPreDerivationTreeList.treeValid_implies_child_valid
  (NEPDTL : NEPreDerivationTreeList G) (child : PreDerivationTree G)
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
        exact NEPreDerivationTreeList.treeValid_implies_child_valid NEPDTL₂ child h_treeValid.right h_right

variable (PDT : PreDerivationTree G) (NEPDTL : NEPreDerivationTreeList G)

mutual
/--Decide the treeValid attribute.-/
def NEPreDerivationTreeList.decideTreeValid (NEPDTL : NEPreDerivationTreeList G)
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
        | isTrue _ => (by
          rw [NEPreDerivationTreeList.treeValid]
          have _ : _ := NEPDTL₂.decideTreeValid
          have _ : _ := PDT₂.decideTreeValid
          apply instDecidableAnd)
/--Decide the treeValid attribute.-/
def PreDerivationTree.decideTreeValid (PDT : PreDerivationTree G)
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

instance [DecidableEq (G.V)] [DecidableEq (G.Z)] : Decidable (PDT.treeValid) := PDT.decideTreeValid
instance [DecidableEq (G.V)] [DecidableEq (G.Z)] : Decidable (NEPDTL.treeValid) := NEPDTL.decideTreeValid

/--The condition (prop) specifying whether it starts in the starting symbol-/
def PreDerivationTree.isFromStartingSymbolCondition {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Prop
| .leaf _ => False
| .inner var _ _ => var = G.start
/--Does this tree begin in the starting symbol? Returns a Bool-/
def PreDerivationTree.isFromStartingSymbol {G : ContextFreeGrammar α nt} [DecidableEq (G.V)] : (PDT : PreDerivationTree G) → Bool
| .leaf _ => False
| .inner var _ _ => Decidable.decide (var = G.start)

-- TODO: find out if this is usable or if the induction principle needs to be defined differently; I'm not sure if we even need this here since we already have a mutual inductive type underneath

/- -- Induction Principles for PreDerivationTrees and NEPreDerivationTreeLists -/
/- mutual -/
/- /--Doing an inductive proof over PDTs requires two to be proven properties. -/
/-   One for PDTs, one for NEPTLs. Equally induction basis and step must be provided for both data structures.-/ -/
/- @[elab_as_elim] -/
/- def PreDerivationTree.induction_principle {G : ContextFreeGrammar α nt} -/
/-   /-Property over PDTs.-/ -/
/-   (prop : PreDerivationTree G → Prop) -/
/-   /-Property over NEPDTLs.-/ -/
/-   (prop₂ : NEPreDerivationTreeList G → Prop) -/
/-   /-Base case for PDTs.-/ -/
/-   (ind_basis : ∀ terminal : Option G.Z , prop (PreDerivationTree.leaf terminal)) -/
/-   /-Base case for NEPDTLs.-/ -/
/-   (ind_basis₂ : -/
/-     ∀ PDT : PreDerivationTree G, -/
/-       prop PDT → prop₂ (NEPreDerivationTreeList.single PDT)) -/
/-   /-Induction step for PDTs.-/ -/
/-   (ind_step : -/
/-     ∀ (v : G.V) (children : NEPreDerivationTreeList G) -/
/-     (rule : G.productions), -/
/-     (ind_hyp : prop₂ children) -/
/-     → -/
/-     prop (PreDerivationTree.inner v children rule)) -/
/-   /-Induction step for NEPDTLs.-/ -/
/-   (ind_step₂ : -/
/-     ∀ PDT : PreDerivationTree G, ∀ NEPDTL₂ : NEPreDerivationTreeList G, -/
/-       prop PDT → prop₂ NEPDTL₂ → prop₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂)) -/
/-   : ∀ PDT : PreDerivationTree G, prop PDT -/
/-   := @PreDerivationTree.rec α nt G prop prop₂ -- "simply" use the automatically generated recursor -/
/-     (fun terminal => -/
/-       by apply ind_basis terminal) -/
/-     (fun var children prodRule => -/
/-       fun h₁ : prop₂ children => -/
/-         ind_step var children prodRule h₁) -/
/-     (fun PDT => -/
/-       fun h₂ : prop PDT => -/
/-         ind_basis₂ PDT h₂) -/
/-     (fun PDT => -/
/-       fun NEPDTL => -/
/-         fun h₁ : prop PDT => -/
/-           fun h₂ : prop₂ NEPDTL => -/
/-             ind_step₂ PDT NEPDTL h₁ h₂) -/
/- /--Doing an inductive proof over NEPDTLs requires two to be proven properties. -/
/-   One for PDTs, one for NEPTLs. Equally induction basis and step must be provided for both data structures.-/ -/
/- @[elab_as_elim] -/
/- def NEPreDerivationTreeList.induction_principle {G : ContextFreeGrammar α nt} -/
/-   /-Property over PDTs.-/ -/
/-   (prop : PreDerivationTree G → Prop) -/
/-   /-Property over NEPDTLs.-/ -/
/-   (prop₂ : NEPreDerivationTreeList G → Prop) -/
/-   /-Base case for PDTs.-/ -/
/-   (ind_basis : ∀ terminal : Option G.Z , prop (PreDerivationTree.leaf terminal)) -/
/-   /-Base case for NEPDTLs.-/ -/
/-   (ind_basis₂ : -/
/-     ∀ PDT : PreDerivationTree G, -/
/-       prop PDT → prop₂ (NEPreDerivationTreeList.single PDT)) -/
/-   /-Induction step for PDTs.-/ -/
/-   (ind_step : -/
/-     ∀ (v : G.V) (children : NEPreDerivationTreeList G) -/
/-     (rule : G.productions), -/
/-     (ind_hyp : prop₂ children) -/
/-     → -/
/-     prop (PreDerivationTree.inner v children rule)) -/
/-   /-Induction step for NEPDTLs.-/ -/
/-   (ind_step₂ : -/
/-     ∀ PDT : PreDerivationTree G, ∀ NEPDTL₂ : NEPreDerivationTreeList G, -/
/-       prop PDT → prop₂ NEPDTL₂ → prop₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂)) -/
/-   : ∀ NEPDTL : NEPreDerivationTreeList G, prop₂ NEPDTL -/
/-   := @NEPreDerivationTreeList.rec α nt G prop prop₂ -- "simply" use the automatically generated recursor -/
/-     (fun terminal => -/
/-       ind_basis terminal) -/
/-     (fun var children prodRule => -/
/-       fun h₁ : prop₂ children => -/
/-         ind_step var children prodRule h₁) -/
/-     (fun PDT => -/
/-       fun h₂ : prop PDT => -/
/-         ind_basis₂ PDT h₂) -/
/-     (fun PDT => -/
/-       fun NEPDTL => -/
/-         fun h₁ : prop PDT => -/
/-           fun h₂ : prop₂ NEPDTL => -/
/-             ind_step₂ PDT NEPDTL h₁ h₂) -/
/- end -/

end ContextFreeGrammar
