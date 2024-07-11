import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Tauto
import FormalSystems.Chomsky.ContextFree.PreDerivationTree

namespace ContextFreeGrammar
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
  | .inner var child_children rule =>
    DerivationTree.inner var child_children rule
      ((NEPreDerivationTreeList.treeValid_implies_child_valid childrenValid h_child_mem).left.symm)
      ((NEPreDerivationTreeList.treeValid_implies_child_valid childrenValid h_child_mem).right.left.symm)
      ((NEPreDerivationTreeList.treeValid_implies_child_valid childrenValid h_child_mem).right.right)


def DerivationTree._getChildrenValid
  {DT : DerivationTree G} (c : NEPreDerivationTreeList G)
  (h_cons : DT.tree = PreDerivationTree.inner v c r) : (c.treeValid) := by
    let valid := DT.valid
    rw [h_cons, PreDerivationTree.treeValid] at valid
    exact valid.right.right

/--List of child nodes. Is a list of DTs.-/
def DerivationTree.children {G : ContextFreeGrammar α nt} (DT : DerivationTree G) : List (DerivationTree G) :=
    match h_constructor : DT.tree with
    | .leaf _ =>
      []
    | .inner _ c _ =>
      List.map (λ child : {x // x ∈ c.asList} =>
        @DerivationTree.fromChild α nt G c child (DT._getChildrenValid c h_constructor) child.prop) c.asList.attach

theorem DerivationTree.child_in_children_imp_child_tree_in_asList :
  ∀ child ∈ DerivationTree.children (DerivationTree.inner v c prodRule h_lhs h_rhs h_treeValid),
  child.tree ∈ c.asList := by
    intro child h_child_mem
    unfold NEPreDerivationTreeList.asList
    cases c
    case single PDT =>
      simp
      simp [DerivationTree.children, DerivationTree.inner, NEPreDerivationTreeList.single] at h_child_mem
      cases h_child_mem
      case intro a_PDT h_child_mem =>
        cases h_child_mem
        case intro a_PDT_mem h_child_mem =>
          rw [h_child_mem.symm]
          have a_PDT_eq : PDT = a_PDT := by
            simp [NEPreDerivationTreeList.asList] at a_PDT_mem
            tauto
          unfold DerivationTree.fromChild
          cases a_PDT
          case leaf tw =>
            simp [DerivationTree.leaf]
            exact a_PDT_eq.symm
          case inner v c r =>
            simp [DerivationTree.inner]
            exact a_PDT_eq.symm
    case cons PDT NEPDTL =>
      simp
      simp [DerivationTree.children] at h_child_mem
      cases h_child_mem
      case intro a_PDT h_child_mem =>
        cases h_child_mem
        case intro a_PDT_mem h_child_mem =>
          simp [DerivationTree.fromChild] at h_child_mem
          cases a_PDT
          case leaf tw =>
            simp at h_child_mem
            rw [h_child_mem.symm]
            simp [DerivationTree.leaf]
            simp [NEPreDerivationTreeList.asList] at a_PDT_mem
            exact a_PDT_mem
          case inner v c r =>
            simp at h_child_mem
            rw [h_child_mem.symm]
            simp [DerivationTree.inner]
            simp [NEPreDerivationTreeList.asList] at a_PDT_mem
            exact a_PDT_mem

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
    (ind_hyp : ∀ child : {child : PreDerivationTree G // child ∈ children.asList}, prop (DerivationTree.fromChild childrenValid (child.2)))
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
              (∀ child : {child : PreDerivationTree G // child ∈ children.asList},
                  prop (fromChild childrenValid child.2)) →
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
              (∀ child : {child : PreDerivationTree G // child ∈ children.asList},
                  prop (fromChild childrenValid child.2)) →
                prop (inner v children rule h_rule_lhs h_rule_rhs childrenValid)) →
              /-If all these are given we can prove that the induction step using fromChild is legit.-/
              ∀ child : {child : PreDerivationTree G //  child ∈ NEPreDerivationTreeList.asList NEPDTL},
                  prop (fromChild h_NEPDTL_valid child.2)
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
            intro child
            /-We know that PDT is this child, because NEPDTL is a singleton "list".-/
            have h_mem := child.2
            have h_refl : PDT = child := by
              apply Eq.symm
              rw [← List.mem_singleton]
              simp [NEPreDerivationTreeList.asList] at h_mem
              rw [h_mem]
              tauto
            have h_mem₂ : _ := child.2
            /-Thus yielding that PDT is in NEPDTL[PDT] -/
            rw [← h_refl] at h_mem₂
            /-Get PDT validity from it being in [PDT]-/
            have h_PDT_valid : PDT.treeValid :=
              NEPreDerivationTreeList.treeValid_implies_child_valid h_NEPDTL_valid h_mem₂
            /-Show that our goal is equivalent to proving prop for the PDT-based DerivationTree-/
            have h_refl₂ : (fromChild h_NEPDTL_valid h_mem) = { tree := PDT, valid := h_PDT_valid } := by
              simp [fromChild]
              match h_cons : child.1, h_mem with
              | PreDerivationTree.leaf tw, t =>
                simp [h_refl.symm, DerivationTree.leaf, h_cons.symm]
              | PreDerivationTree.inner v c r, t =>
                simp [h_refl.symm, DerivationTree.inner, h_cons.symm]
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
            case a : ∀ (child : { child // child ∈ NEPreDerivationTreeList.asList children_step }), prop (fromChild _ _) =>
              have h_children_step_valid : children_step.treeValid := h_valid_goal.right.right
              intro child_step
              /-From the induction hypothesis.-/
              exact h_propHelper₂_children_step h_children_step_valid ind_basis ind_step child_step
          /-Prove the induction step for propHelper₂.-/
          have propHelper₂_step : (∀ (PDT : PreDerivationTree G) (NEPDTL₂ : NEPreDerivationTreeList G),
            propHelper PDT → propHelper₂ NEPDTL₂ → propHelper₂ (NEPreDerivationTreeList.cons PDT NEPDTL₂)) := by
            /-Name the implication pre-conditions of the induction step.-/
            intro PDT NEPDTL₂ h_propHelper_PDT h_propHelper₂_NEPDTL
            /-Name the implication pre-conditions of the property propHelper₂ (...).-/
            intro h_valid_goal _ _
            /-Introduce the necessary child variable & member assumption to do a ∀-proof.-/
            intro child
            /-Follow validity of both PDT and NEPDTL₂ from the propHelper₂ pre-condition.-/
            rw [NEPreDerivationTreeList.treeValid] at h_valid_goal
            have h_NEPDTL₂_valid : NEPDTL₂.treeValid := h_valid_goal.right
            have h_PDT_valid : PDT.treeValid := h_valid_goal.left
            /-Case distinction over leaf or not.-/
            match h_cons : child.1, child.2 with
            | PreDerivationTree.leaf tw, h_mem =>
              simp [fromChild]
              apply ind_basis
            | PreDerivationTree.inner v c r, h_mem =>
              simp [fromChild]
              rw [NEPreDerivationTreeList.asList] at h_mem
              rw [List.mem_cons] at h_mem
              /-Case distinction: child in top of list (=PDT) or in body (NEPDTL)-/
              cases h_mem
              case inl h_inl =>
                rw [DerivationTree.inner]
                have h_inl₂ : _ := h_inl.symm
                /-Reduce / Use the propHelper assumption-/
                have h_propHelper_PDT_usage : _ :=
                  h_propHelper_PDT h_PDT_valid ind_basis ind_step
                /-place child into propHelper(PDT) assumption-/
                simp [h_inl₂] at h_propHelper_PDT_usage
                /-If child is PDT, then we can use propHelper(PDT) to our advantage.-/
                exact h_propHelper_PDT_usage
              case inr h_inr =>
                /-If child is in NEPDTL, then we can use propHelper₂(NEPDTL) to our advantage.-/
                have h_propHelper₂_NEPDTL_usage : _ :=
                  h_propHelper₂_NEPDTL h_NEPDTL₂_valid ind_basis ind_step ⟨ PreDerivationTree.inner v c r , h_inr⟩
                simp [fromChild] at h_propHelper₂_NEPDTL_usage
                exact h_propHelper₂_NEPDTL_usage
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
  DT.tree.depth

def DerivationTree.collectProdRules
  {G : ContextFreeGrammar α nt}
  (DT : DerivationTree G) :
  List (G.productions) := DT.tree.prodRuleList

-- theorem children_func_returns_fromChilds
--   {G : ContextFreeGrammar α nt}
--   {children : NEPreDerivationTreeList G}
--   {DT : DerivationTree G} :
--   ∀ child ∈ DT.children,
--   ∃ (childrenValid : children.treeValid),
--   ∃ (h_child_mem : child.tree ∈ children.asList),
--   child = @DerivationTree.fromChild α nt G children child.tree childrenValid h_child_mem := by
--   intro child child_mem
--   cases h_constructor_DT : DT.tree
--   case leaf tw =>
--     simp [DerivationTree.fromChild]
--     rw [h_constructor_DT] at child_mem

--   match h_DT_constructor : DT.tree with
--   | .leaf tw =>

--     rw [DerivationTree.children] at child_mem
--     rw [h_DT_constructor] at child_mem
--     by_contra h_contra
--     simp at h_contra

--     let DT_child := DerivationTree.children DT
--     repeat rw [DT_child.symm] at h_contra

--     induction DT_child with
--     | nil =>
--       --rw [h_child_constructor] at h_contra
--       absurd h_contra.left
--       --rw [DT.children]
--       sorry
--     | cons head tail ind_hyp =>

--     sorry
--   | .inner v c r =>
--     sorry

theorem child_less_depth :
  ∀ DT : DerivationTree G, ∀ child ∈ DT.children,
  child.depth < DT.depth := by
    intro DT
    induction DT using DerivationTree.induction_principle
    case ind_basis terminal =>
      have children_leaf_is_nil : DerivationTree.children (DerivationTree.leaf terminal) = [] := by
        tauto
      rw [children_leaf_is_nil]
      tauto
    case ind_step v c prodRule h_lhs h_rhs h_treeValid ind_hyp =>
      intro child h_child_mem

      --nth_rewrite 2 [DerivationTree.inner, PreDerivationTree.depth]
      have h₁ : child.tree ∈ NEPreDerivationTreeList.asList c := by
        exact DerivationTree.child_in_children_imp_child_tree_in_asList child h_child_mem
      -- All children of child.tree have less depth than child.tree
      have ind_hyp_applied := ind_hyp ⟨ child.tree , h₁⟩
      --repeat rw [DerivationTree.depth] at ind_hyp_applied
      rw [ DerivationTree.inner, DerivationTree.depth, DerivationTree.depth, PreDerivationTree.depth]

      sorry




def DerivationTree.collectLeaves
  {G : ContextFreeGrammar α nt}
  (DT : DerivationTree G) :
  List (DerivationTree G) := match DT.tree with
  | .leaf _ =>
    [DT]
  | .inner _ _ _ =>
    List.foldl (fun prev (child : {x // x ∈ DT.children}) =>
      have _ : depth child.1 < depth DT := by
        exact child_less_depth DT child.1 child.2
      prev ++ child.1.collectLeaves
      ) [] DT.children.attach
  termination_by (DT.depth, 0)



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
end ContextFreeGrammar
