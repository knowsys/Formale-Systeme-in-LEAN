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

/--Shorthand for goes to ε productions.-/
def ContextFreeProduction.isEps (cfp : (ContextFreeProduction Z V)) : Prop :=
  cfp.rhs = Word.epsilon

-- TODO: Prove decidability?

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
--Do I need to define CFDerivations?
--Probably yes, lots of cool theorems


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

--New idea: Split everything up into many sub-tasks
mutual
/--Basic structure of a derivation tree without validity-constraints. Assume ordered-/
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

/--Convert to a List (PreDerivationTree G).-/
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
/--Return a list of the nodes children.-/
def NEPreDerivationTreeList.nodeList {G : ContextFreeGrammar α nt} (NEPDT : NEPreDerivationTreeList G) : List (PreDerivationTree G) := match (NEPDT : NEPreDerivationTreeList G) with
  | .single PDT => PDT.nodeList
  | .cons PDT NEPDT₂ => PDT.nodeList ++ NEPDT₂.nodeList -- NEPreDerivationTreeList.foldl (fun prev tree => tree.nodeList ++ prev) [PDT] NEPDT
/--Return a list of the nodes children.-/
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

/--Return a (possibly empty) list of this nodes children.-/
def PreDerivationTree.children {G : ContextFreeGrammar α nt} : (PDT : (PreDerivationTree G)) → List (PreDerivationTree G)
  | leaf _ => []
  | inner _ children _ => children.asList

mutual
/--Get the list of used production rules.-/
def PreDerivationTree.prodRuleList {G : ContextFreeGrammar α nt} : (PreDerivationTree G) → List (ContextFreeProduction G.Z G.V)
  | .leaf _ => []
  | .inner _ children prodRule => prodRule :: children.prodRuleList
/--Get the list of used production rules-/
def NEPreDerivationTreeList.prodRuleList {G : ContextFreeGrammar α nt} : (NEPDT : (NEPreDerivationTreeList G)) → List (ContextFreeProduction G.Z G.V)
  | .single PDT => PDT.prodRuleList
  | .cons PDT NEPDT₂ => PDT.prodRuleList ++ NEPDT₂.prodRuleList
end

/- /--Collect the applied production rules, as left-first derivation.-/
def PreDerivationTree.prodRuleList : (PreDerivationTree G) → List (ContextFreeProduction G.Z G.V)
| leaf _ => []
| inner var children prodRule =>
    NEPreDerivationTreeList.foldl
    (fun previous child =>
        -- have : SizeOf.sizeOf child < 2 + SizeOf.sizeOf children + SizeOf.sizeOf prodRule := by
        --   sorry
        have : List.length (nodeList child) < List.length (nodeList (inner var children prodRule)) := by
          sorry
        previous ++ child.prodRuleList)
    [prodRule]
    children
termination_by tree => tree.nodeList.length -/

mutual
/--The final result-word defined by the children of a tree-node.-/
def PreDerivationTree.result {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Word (G.V ⊕ G.Z)
  | .leaf terminalWord => Word.mk (terminalWord.map (fun terminal => Sum.inr terminal))
  | .inner _ children _ => children.result
/--The final result-word defined by the children of a tree-node.-/
def NEPreDerivationTreeList.result {G : ContextFreeGrammar α nt} : (NEPDT : NEPreDerivationTreeList G) → Word (G.V ⊕ G.Z)
  | .single PDT => PDT.result
  | .cons PDT NEPDT₂ => Word.concatListOfWords [PDT.result , NEPDT₂.result]
end

mutual
/--The intermediate level word defined by the children of a tree-node.-/
def PreDerivationTree.levelWord {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) → Word (G.V ⊕ G.Z)
  | .leaf terminalWord => Word.mk (terminalWord.map (fun terminal => Sum.inr terminal))
  | .inner var _ _ => Word.mk [(Sum.inl var)]
/--The final result-word defined by the children of a tree-node.-/
def NEPreDerivationTreeList.levelWord {G : ContextFreeGrammar α nt} : (NEPDT : NEPreDerivationTreeList G) → Word (G.V ⊕ G.Z)
  | .single PDT => PDT.levelWord
  | .cons PDT NEPDT₂ => Word.concatListOfWords [PDT.levelWord , NEPDT₂.levelWord]
end

/- /--The final result-word defined by the children of a tree-node.-/
def PreDerivationTree.result {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) : Word (G.V ⊕ G.Z) :=
  match PDT with
    | .leaf terminalWord => Word.mk (terminalWord.map (fun terminal => Sum.inr terminal))
    | .inner _ children prodRule =>
      Word.mk (List.foldl List.append []
        (children.asList.map (
            fun child : PreDerivationTree G =>
            (child.result : List _)
          )
        )
      )
decreasing_by
  simp
  tauto -/

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
/- /--Define the depth of a context-free derivation-tree.-/
def PreDerivationTree.depth {G : ContextFreeGrammar α nt} : (PDT : PreDerivationTree G) -> Nat
| .leaf _ => 0
| .inner _ children _ => (
  (List.map (fun child : _ => child.depth) children.asList
  ).maximum_of_length_pos (by simp; exact children.asList_length )) + 1
decreasing_by
  simp
  tauto -/
mutual
theorem PreDerivationTree.nodeList_eq_concat_children_nodeList
  {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) :
  PDT.nodeList = [PDT] ∨
  PDT.nodeList = List.foldl (fun prev child => prev ++ child.nodeList) [PDT] PDT.children := by
    cases h_constructor : PDT
    case leaf w =>
      apply Or.inl
      rfl
    case inner var children rule =>
      apply Or.inr
      rw [PreDerivationTree.children,PreDerivationTree.nodeList]; simp
      apply List.foldl_cons

theorem NEPreDerivationTreeList.nodeList_eq_concat_children_nodeList
  {G : ContextFreeGrammar α nt} (NEPDT : NEPreDerivationTreeList G) :
  NEPDT.nodeList = List.foldl (fun prev child => prev ++ child.nodeList) [] NEPDT.asList := by
    induction PDT with
    | leaf terminalWord =>
      sorry
    | inner var children rule h_ih =>
      sorry
end
    /- cases h_constructor_asList : NEPDT.asList
    case nil prodRule =>
      have h_not : _ := NEPDT.asList_never_nil
      contradiction
    case cons head tail =>
      induction NEPDT.nodeList with
        | nil =>
          by_contra f

          have h_not : _ := NEPDT.nodeList_never_nil
          absurd h_not

        | cons head₂ tail₂ ih =>
          simp -/
mutual
theorem PreDerivationTree.children_have_less_nodes
  {G : ContextFreeGrammar α nt} (PDT : PreDerivationTree G) :
  (∃ w, PDT = PreDerivationTree.leaf w) ∨
  (∃ var children rule, PDT =  PreDerivationTree.inner var children rule
    ∧ ∀ child ∈ children.asList,
    PDT.nodeList.length > child.nodeList.length ):= by
      cases PDT
      case leaf w' =>
        apply Or.inl
        exists w'
      case inner var' children' rule' =>
        apply Or.inr
        exists var'; exists children'; exists rule'
        apply And.intro
        rfl
        intro child; intro h_child_mem



/--Given a NEPreDerivationTreeList, its members have less nodes than the whole list.-/
theorem NEPreDerivationTreeList.children_have_less_nodes
  {G : ContextFreeGrammar α nt} (NEPDT : NEPreDerivationTreeList G) :
  ∀ child ∈ NEPDT.asList, NEPDT.nodeList.length > child.nodeList.length := by
  intro child
  intro h_membership

  sorry
end
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

/--Structure: A derivation tree. Use`tree : PreDerivationTree`to define its structure and provide
  a validity proof`valid : treeValid tree`.-/
structure DerivationTree (G : ContextFreeGrammar α nt) where
  tree : PreDerivationTree G
  valid : tree.treeValid

/--Construct a derivation-tree leaf from a terminal word.-/
@[match_pattern]
def DerivationTree.leaf {G : ContextFreeGrammar α nt} (w : Word G.Z) : DerivationTree G := {
  tree := PreDerivationTree.leaf w
  valid := by rw [PreDerivationTree.treeValid]; simp
}

/--Construct a derivation-tree node from:

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

/--Define context free derivations v (G)=>* w inductively. Constructors:

  - `same_var`  - 0 step derivations v (G)=>* v

  - `same_word` - 0 step derivations v (G)=>* w with w is a "word" that looks like v

  - `step`  - Given a derivation`v' → w'`, and a production rule

    `v → u_mid = l_of_v' * v' * r_of_v'`,

    construct a derivation

    `v → l_of_v' * w' * r_of_v'`

    Note: u, v and w are not the same as in type-0 derivations. This is confusing!-/
inductive ContextFreeDerivation (G : ContextFreeGrammar α nt) : (v: G.V) → (w: Word (G.V ⊕ G.Z)) → Type
  /--0 step derivations v (G)=>* v-/
  | same_var {v : G.V} (w' : G.V) (h : v = w') : ContextFreeDerivation G v [.inl w']
  /--0 step derivations v (G)=>* w with w is a "word" that looks like v-/
  | same_word {v : G.V} {w : Word (G.V ⊕ G.Z)} (h : [.inl v] = w) : ContextFreeDerivation G v w
  /--step: Given a derivation`v' → w'`, and a production rule`v → u_mid = l_of_v' * v' * r_of_v'`,
    construct a derivation`v → l_of_v' * w' * r_of_v'`-/
  | step {v v' : G.V} {w w' u_mid l_of_v' r_of_v' : Word (G.V ⊕ G.Z)}
    (h_production : { lhs := v, rhs := u_mid}  ∈ G.productions)
    (h_u_mid : u_mid = l_of_v' * Word.mk [Sum.inl v'] * r_of_v'):
    ContextFreeDerivation G v' w' → ContextFreeDerivation G v (l_of_v' * w' * r_of_v')

/--Define the length of a CFDerivation. Cannot use generic derivation definition due to
  requiring this definition in the construction of the embedding.-/
def ContextFreeDerivation.len (cfd : ContextFreeDerivation G v w) : Nat :=
  match cfd with
    | same_var _ _  => 0
    | same_word _    => 0
    | step _ _ cfd' => Nat.succ cfd'.len

--IMPORTANT: theorems are not computable!
/--Define an embedding of context-free derivations in generic derivations.-/
def ContextFreeDerivation.toDerivation
    (cfd : @ContextFreeDerivation α nt G v w) :
    (@Grammar.Derivation α nt GenericProduction _ (↑G) (Word.mk [Sum.inl v]) w) :=
    -- Constructing a generic-grammar derivation from a cfderivation
    -- requires a case distinction on the constructor of cfderivation
    -- these were same_var, same_word and step
    match cfd with

    | same_var w' h =>
      have h_h : (Word.mk [@Sum.inl {x // x ∈ G.V} {x // x ∈ G.Z} v] = Word.mk [Sum.inl w']) := by simp [h]
      by exact Grammar.Derivation.same h_h

    | same_word h =>
      by exact Grammar.Derivation.same h

    -- Given a derivation v' → w', and a production rule
    -- v → u_mid = l_of_v' * v' * r_of_v',
    -- construct a derivation v → l_of_v' * w' * r_of_v'
    | @step α nt G v v' w w' u_mid l_of_v' r_of_v' h_production h_u_mid deriv_v'_to_w' =>
      let G' : Grammar GenericProduction := { Z := G.Z, V := G.V, start := G.start, productions := Finset.map ContextFreeProduction.toProduction G.productions }
      let prod_but_cf := {lhs := v, rhs := u_mid : ContextFreeProduction G'.Z G'.V}
      let productionRule : G'.productions := ⟨ prod_but_cf ,
        by
          simp -- simp might already use classical reasoning in mathlib
            -- tauto uses classical reasoning
          tauto -- credit to Henrik for coming up with this proof
            -- exact Exists.intro prod h_production
          ⟩
      by
      apply Grammar.Derivation.step -- construct the step using generic step constructor
      -- yields a derivation from u to v
      case step => -- prodrule from `v` to `u_mid (= l_of_v' * v' * r_of_v')`
        exact Grammar.DerivationStep.fromRule productionRule
      case x => -- A derivation from u' to v (recursive part of the definition),
        exact (@Grammar.Derivation.augment_right α nt _ _ G' r_of_v' (l_of_v' * Word.mk [(Sum.inl v')]) (l_of_v' * w') (@Grammar.Derivation.augment_left α nt _ _ G' _ _ l_of_v' (ContextFreeDerivation.toDerivation deriv_v'_to_w')))
      case sound =>
        rw [Grammar.DerivationStep.from_rule_result]
        simp
        rw [h_u_mid]
        rfl
termination_by (cfd.len, 0)

--Coercion CFDerivation into generic Derivations
instance : Coe (@ContextFreeDerivation α nt G v w) (@Grammar.Derivation α nt GenericProduction _ (↑G) (Word.mk [Sum.inl v]) w) where
  coe cfDerivation := ContextFreeDerivation.toDerivation cfDerivation

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
