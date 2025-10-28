import FormaleSystemeInLean.Chomsky.Grammar
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Tauto

import FormaleSystemeInLean.Chomsky.ContextFree.ContextFreeDerivation
--================================================================================
-- File: Theorems
/-  Containts multiple theorems leading up to the Pumping Lemma for context-free
    languages, includes definitions of context-free languages, chomsky normal form.
-/
--================================================================================

variable {α nt : Type} {Prod : Finset α → Finset nt → Type} [Production α nt Prod]

/--Coerce a word from a grammars terminal symbol type (a.k.a. finset) into
  that finsets supertype.-/
def coerceWord {Z : Finset α} (w : Word Z) : Word α := w.map (fun t => t.val)

/--Coerce a language from a grammars terminal symbol type (a.k.a. finset) into
  that finsets supertype.-/
def coerceLang {Z : Finset α} (l : Language Z) : Language α := fun word => ∃ w, w ∈ l ∧ (coerceWord w = word)

instance {Z : Finset α} : CoeOut (Word Z) (Word α) where
  coe word := @coerceWord α Z word

instance {Z : Finset α} : CoeOut (Language Z) (Language α) where
  coe lang := @coerceLang α Z lang

/--Theorem: coerceWord and coerceLang respect the language membership relation.-/
theorem coerceLang_mem {Z : Finset α} {w : Word Z} (l : Language Z) :
  w ∈ l ↔ coerceWord w ∈ coerceLang l := by sorry
/--Theorem: coerceWord and coerceLang respect the language membership relation.-/
theorem coerceLang_not_mem {Z : Finset α} {w : Word Z} (l : Language Z) :
  w ∉ l ↔ coerceWord w ∉ coerceLang l := by sorry

/--Theorem: All words over a type of terminal symbols that are in a coerced
  version of a grammar's generated language have a corresponding word in the generated
  language that is of the type of the grammar's terminal symbol finset.-/
theorem coerceLang_mem_imp_word_of_type :
  ∀ word : Word α, ∀ G : Grammar Prod,
  word ∈ coerceLang G.GeneratedLanguage →
  ∃ word₂ : Word G.Z, word₂ ∈ G.GeneratedLanguage ∧ coerceWord word₂ = word := by
    sorry

/--Theorem: All words over a type of terminal symbols that are in a coerced
  version of a context-free grammar's generated language have a corresponding word in the generated
  language that is of the type of the context-free grammar's terminal symbol finset.-/
theorem coerceCFGLang_mem_imp_word_of_type :
  ∀ word : Word α, ∀ G : ContextFreeGrammar α nt,
  word ∈ coerceLang G.GeneratedLanguage →
  ∃ word₂ : Word G.Z, word₂ ∈ G.GeneratedLanguage ∧ coerceWord word₂ = word := by
  sorry

/--A language is context-free if it has a context-free grammar that produces it.
  Requires the usage of coerceLang to adjust the types.-/
def Language.is_context_free (language : Language α) :=
  ∃ (nt : _) (CFG : ContextFreeGrammar α nt),
  (coerceLang CFG.GeneratedLanguage) = language

/--The Subtype of context-free languages is those languages, that are context-free.-/
def ContextFreeLanguage := { l : Language α // l.is_context_free }

/--A context-free grammar is in chomsky normal-form if all of its productions have
  either of the shapes:

  - `A → B * C` where `A`,`B` and`C`are variables, or

  - `A → c` where `A`is a variable and`c`is a terminal symbol.-/
def isInChomskyNormalForm (cfg : ContextFreeGrammar α nt) :=
  ∀ production ∈ cfg.productions,
  (∃ A B C : cfg.V, production = {lhs := A, rhs := Word.mk [Sum.inl B]* Word.mk [Sum.inl C]})
  ∨ (∃ A : cfg.V, ∃ c : cfg.Z, production = {lhs := A, rhs := Word.mk [Sum.inr c]})

/--The Subtype of context-free grammars are those context-free grammars, that are in chomsky normal-form.-/
def ContextFreeGrammarCNF α nt := { l : ContextFreeGrammar α nt // isInChomskyNormalForm l }

/--All derivations that take place in context-free grammars in chomsky normal
  form have the attribute, that the length of the manipulated string is
  monotonically increasing along said derivation.-/
theorem deriv_length_monotone_CNF :
  ∀ (cfg : ContextFreeGrammarCNF α nt),
  ∀ u v, (∃ (_ : (ContextFreeGrammar.ContextFreeDerivation cfg.1 u v)), True) →
  u.len ≤ v.len := by
    intro cfg u v h_exists
    apply @Exists.elim _ _ (Word.len u ≤ Word.len v) h_exists
    intro deriv _
    induction deriv
    case same h_same =>
      rw [h_same]
    case step u u' v dstep deriv sound h_ind =>
      have h_ind_applied :=
        h_ind
          (Exists.intro deriv (by tauto))
      have h_step_len : Word.len u ≤ Word.len u' := by
        simp [sound.symm]
        simp [dstep.len_u_composition]
        have dstep_CNF := cfg.2 dstep.prod.1 dstep.prod.2
        cases rule_form : dstep_CNF
        case inl h_var_form =>
          cases h_var_form
          case intro A h_var_form =>
            cases h_var_form
            case intro B h_var_form =>
              cases h_var_form
              case intro C h_var_form =>
                simp [ContextFreeGrammar.ContextFreeDerivationStep.result, Grammar.DerivationStep.result, Word.length_mul_eq_add]
                simp [Word.len, Word.mk]
                simp [h_var_form, Production.rhs, ContextFreeProduction.toProduction, Coe.coe, Word.mk]
                unfold_projs
                simp
        case inr h_terminal_form =>
          cases h_terminal_form
          case intro A h_terminal_form =>
            cases h_terminal_form
            case intro c h_terminal_form =>
              simp [ContextFreeGrammar.ContextFreeDerivationStep.result, Grammar.DerivationStep.result, Word.length_mul_eq_add]
              simp [Word.len, Word.mk]
              simp [h_terminal_form, Production.rhs, ContextFreeProduction.toProduction, Coe.coe, Word.mk]
      apply Nat.le_trans h_step_len h_ind_applied

/--Theorem: ε is not in the generated languages of context-free grammars in chomsky normal-form.-/
theorem eps_not_in_CNF_Grammar {α nt : Type} :
  ∀ grammar : @ContextFreeGrammarCNF α nt,
  ε ∉ grammar.val.GeneratedLanguage := by
    --intro cfg h_contra
    intro cfg h_contra
    unfold ContextFreeGrammar.GeneratedLanguage at h_contra
    cases h_contra with | intro default_CFGCNF =>
      have monotone := deriv_length_monotone_CNF cfg _ _ (Exists.intro default_CFGCNF (by tauto))
      nth_rewrite 2 [Word.eps_len_0.mpr] at monotone
      have start_len_1 : Word.len [@Sum.inl cfg.1.V cfg.1.Z cfg.1.start] = 1 := by tauto
      rw [start_len_1] at monotone
      rw [Nat.le_zero_eq 1] at monotone
      tauto
      rfl

/--Return a corresponding context-free grammar in chomsky normal-form that accepts
  the same language.

  TODO: Note, that nt and nt₂ are part of the input. This is nonsensical and
  stems from our definition of grammars / context-free grammars that has
  the type of non-terminals as an input type parameter.-/
def generate_equivalent_CNF
  (cfg : {cfg : ContextFreeGrammar α nt // ε ∉ cfg.GeneratedLanguage})
  : { cfg₂ : ContextFreeGrammar α nt₂ // isInChomskyNormalForm cfg₂} := sorry

/--The grammar returned by`generate_equivalent_CNF`has the same generated language
  as the input context-free grammar.

  TODO: Note, that nt and nt₂ are part of the input. This is nonsensical and
  stems from our definition of grammars / context-free grammars that has
  the type of non-terminals as an input type parameter.-/
def generate_equivalent_CNF_is_eq :
  ∀ α nt nt₂ : Type,
  ∀ (cfg : {cfg : ContextFreeGrammar α nt // ε ∉ cfg.GeneratedLanguage}),
   @coerceLang α _ cfg.val.GeneratedLanguage
  = @coerceLang α
    ((Subtype.val (@generate_equivalent_CNF α nt nt₂ cfg)).Z) (generate_equivalent_CNF cfg).val.GeneratedLanguage := sorry

/--Theorem: For every context-free grammar without
  ε there is a corresponding context-free grammar in chomsky normal-form that
  accepts the same language. (Requires coerceLang).

  TODO: Note, that nt and nt₂ are part of the input. This is nonsensical and
  stems from our definition of grammars / context-free grammars that has
  the type of non-terminals as an input type parameter.-/
theorem equivalent_CNF_Grammar :
  ∀ α nt nt₂,
  ∀ cfg : {cfg : ContextFreeGrammar α nt | ε ∉ cfg.GeneratedLanguage},
  ∃ cfg₂ : { cfg₂ : ContextFreeGrammar α nt₂ // isInChomskyNormalForm cfg₂},
    coerceLang cfg.val.GeneratedLanguage
    =
    coerceLang cfg₂.val.GeneratedLanguage := by
      sorry

/--Theorem: The length of a context-free derivation in chomsky normal-form
  is two times the length of the result word minus 1.-/
theorem CNF_derivation_lengths {α nt : Type} :
  ∀ cfgCNF : @ContextFreeGrammarCNF α nt, ∀ word : Word cfgCNF.val.Z,
  (word ∈ cfgCNF.val.GeneratedLanguage →
  (∀ derivation : (ContextFreeGrammar.ContextFreeDerivation cfgCNF.val (Word.mk [Sum.inl cfgCNF.val.start]) word.ZtoVZ),
  (2 * word.len) - 1 = derivation.length)) := by sorry

/--Sub-tree relationship.

  TODO: This is relatively new and not tested yet.
    Should equality be allowed?
    Perhaps this is more useful for an induction principle?-/
def ContextFreeGrammar.DerivationTree.subTree (sub : DerivationTree G) (super : DerivationTree G) : Prop :=
  sub = super ∨
  ∃ sub₂ : {x : DerivationTree G // x ∈ super.children},
    have _ : sub₂.1.depth < super.depth := ContextFreeGrammar.child_less_depth super sub₂.1 sub₂.prop
    sub.subTree sub₂.1
  termination_by (super.depth, 0)

/--Direct sub-tree relationship.

  TODO: This is relatively new and not tested yet.
    Perhaps this is more useful for an induction principle?-/
def ContextFreeGrammar.DerivationTree.isChild (sub : DerivationTree G) (super : DerivationTree G) : Prop :=
  ∃ sub₂ : {x : DerivationTree G // x ∈ super.children},
    sub = sub₂.1

/--A Path is just a list of nodes.-/
def DerivationTreePath
  { cfg : ContextFreeGrammar α nt }
  ( _dt : ContextFreeGrammar.DerivationTree cfg) :=
  List (ContextFreeGrammar.DerivationTree cfg)

/--Words are lists and can thus be coerced.-/
instance
  {cfg : ContextFreeGrammar α nt}
  {dt : ContextFreeGrammar.DerivationTree cfg}
  (_ : DerivationTreePath dt)
  : CoeOut (DerivationTreePath dt) (List (ContextFreeGrammar.DerivationTree cfg)) where
  coe path := path

/--A temporary example of how to define a valid DerivationTree Path. WIP.-/
structure ValidDerivationTreePath
  { cfg : ContextFreeGrammar α nt }
  ( dt : ContextFreeGrammar.DerivationTree cfg) where
  /--The path-/
  path : DerivationTreePath dt
  /--Every node alongth the path is a child of the next-/
  valid : ∀ i : Fin (List.length path - 1),
          --ContextFreeGrammar.DerivationTree.subTree
          ContextFreeGrammar.DerivationTree.isChild
            (List.get path ⟨i, Nat.lt_of_lt_pred i.2 ⟩ )
            (List.get path ⟨i+1, Nat.lt_sub_iff_add_lt.mp i.2 ⟩ )

/--Theorem: A context-free derivation tree has a number of leaves equal to
  the length of the result word.-/
theorem derivation_result_is_leaf_count :
  ∀ dt : ContextFreeGrammar.DerivationTree G,
  Word.len dt.result = List.length dt.collectLeaves' := by
  sorry

/--Theorem: A path in a context-free derivation tree in chomsky normal-form
  has a length of at least log2 of the number of leaves in said tree.
  TODO: A Derivation is not a path! Rewrite accordingly.-/
theorem derivation_path_length :
  ∀ n : ℕ, ∀ cfg_CNF : ContextFreeGrammarCNF α nt,
  ∀ dt : (ContextFreeGrammar.DerivationTree cfg_CNF.1),
  dt.collectLeaves'.length = n
  →
  ∃ path : ContextFreeGrammar.ExhaustiveContextFreeDerivation cfg_CNF.val [Sum.inl cfg_CNF.1.start] (@Word.ZtoVZ α nt _ _ cfg_CNF.1 dt.result),
  path.derivation.length ≥ Nat.log2 n := by
  sorry

/--Theorem: Any path of sufficient length must contain a variable multiple
  times. (Schubfachprinzip)
  TODO: A Derivation is not a path! Rewrite accordingly.-/
theorem derivation_len_over_V_imp_double_var
  {α nt : Type} :
  ∀ cfg_CNF : @ContextFreeGrammarCNF α nt, ∀ u v,
  ∀ deriv : ContextFreeGrammar.ContextFreeDerivation cfg_CNF.1 u v,
  deriv.length ≥ cfg_CNF.1.V.card
  →
  ∃ var : cfg_CNF.val.V,
    ∃ u' u'',
    ∃ deriv₁ : ContextFreeGrammar.ContextFreeDerivation cfg_CNF.1 u u',
    ∃ deriv₂ : ContextFreeGrammar.ContextFreeDerivation cfg_CNF.1 u' u'',
    ∃ deriv₃ : ContextFreeGrammar.ContextFreeDerivation cfg_CNF.1 u'' v,
    Sum.inl var ∈ u' ∧ Sum.inl var ∈ u'' := by sorry

/--An attempt at proving the pumping lemma for context-free languages.-/
theorem PumpingLemma :
  ∀ language : ContextFreeLanguage, ∃ n : ℕ,
  ∀ z : {z ∈ language.val | z.len ≥ n},
  ∃ u v w x y : Word α, z.val = u * v * w * x * y ∧ Word.len (v * x) ≥ 1 ∧ Word.len (v * w * x) ≤ n
  ∧ (∀ k : ℕ, u * (v^k) * w * (x^k) * y ∈ language.val) := by
    intro language
    by_cases ε ∈ language.1
    case pos =>
      --Ignoriere den Fall ε ∈ L
      sorry
    case neg h_eps_not_in_language =>
      -- Forme um: Sprache ist kontextfrei
      have property := language.2
      simp [Language.is_context_free] at property
      cases property
      case intro nt property =>
        cases property
        -- Dann haben wir eine kontextfreie Grammatik cfg,
        -- welche genau die Sprache akzeptiert.
        case intro cfg h_cfg_gen_is_lang =>
          -- Ohne Beschränkung der Allgemeinheit, sei diese
          -- Grammatik in Chomsky-Normalform.
          -- Man bemerke hier, dass nt₂ mit sorry generiert werden muss,
          -- obwohl wir auf diesem Abstraktionslevel definitiv nicht darüber
          -- nachdenken wollen!

          -- Generiere die äquivalente Grammatik in CNF
          have nt₂ : Type := sorry
          have h_eps_not_gen : ε ∉ ContextFreeGrammar.GeneratedLanguage cfg := by
            rw [h_cfg_gen_is_lang.symm] at h_eps_not_in_language
            have eps_coe : @Word.epsilon α = coerceWord (@Word.epsilon cfg.Z) := by tauto
            rw [eps_coe, ← coerceLang_not_mem] at h_eps_not_in_language
            exact h_eps_not_in_language
          -- und beweise die Äquivalenz
          let cfg_CNF := @generate_equivalent_CNF α nt nt₂ ⟨ cfg , h_eps_not_gen⟩
          have h_cfg_CNF_gen_is_lang : coerceLang (cfg.GeneratedLanguage) = coerceLang (cfg_CNF.1.GeneratedLanguage) := by
            apply generate_equivalent_CNF_is_eq _ _ _ ⟨ cfg, h_eps_not_gen ⟩

          -- Wähle n wie folgt:
          exists 2^cfg_CNF.val.V.card
          -- Führe z sowie die Eigenschaften von z ein
          intro z
          -- Benenne z's Eigenschaften sinnvoll
          have z_exists_deriv := z.prop.left
          simp [h_cfg_gen_is_lang.symm, h_cfg_CNF_gen_is_lang] at z_exists_deriv
          -- Man ist gezwungen z₂ vom Typ Word G.Z einzuführen
          apply coerceCFGLang_mem_imp_word_of_type z.val cfg_CNF.1 at z_exists_deriv
          cases z_exists_deriv with | intro z₂ z₂_mem =>
          -- Benenne z₂'s Eigenschaften sinnvoll
          have z_eq_z₂ := z₂_mem.right
          have z₂_mem := z₂_mem.left
          -- Erlange die Existenz einer Ableitung nach z₂ in cfg
          unfold ContextFreeGrammar.GeneratedLanguage at z₂_mem
          apply Nonempty.elim_to_inhabited at z₂_mem
          apply z₂_mem
          case f =>
          intro h_exists_deriv_z₂
          -- Die Ableitung von z₂ in cfg_CNF (Ableitungspfad)
          let default_deriv_z₂ := h_exists_deriv_z₂.default
          have proof_exhaustive : ContextFreeGrammar.ContextFreeDerivation.exhaustiveCondition default_deriv_z₂ := (by
            unfold ContextFreeGrammar.ContextFreeDerivation.exhaustiveCondition
            intro symbol symbol_mem
            simp at symbol_mem
            rw [List.mem_map] at symbol_mem
            cases symbol_mem
            case intro symbol₂ symbol₂_mem =>
            rw [symbol₂_mem.right.symm]
            tauto)
          -- Der zugehörige Ableitungsbaum
          let default_derivTree_z₂ := (default_deriv_z₂.toDerivationTree (proof_exhaustive) (by tauto))
          -- mit Lemmas zu seiner Korrektheit
          have defaultDerivTree_z₂_respects_result :=
            ContextFreeGrammar.ContextFreeDerivation.toDerivationTree_respects_result default_deriv_z₂ proof_exhaustive (by tauto)
          let _ : DecidableEq { x // x ∈ cfg_CNF.val.V } := sorry
          have defaultDerivTree_z₂_respects_start :=
            ContextFreeGrammar.ContextFreeDerivation.toDerivationTree_respects_start default_deriv_z₂ cfg_CNF.val.start rfl (by tauto) (by tauto) (by sorry)

          -- Word.len (v * x) ≥ 1, da die Ursprungsvariable A,
          -- welche wir mit der Schleife erreichen, aufgrund von
          -- CNF genau zwei Kinder hat. Eins der Kinder wird die Schleife,
          -- das andere Kind landet in dem Vorgänger von v oder in dem von x.
          -- (Dann wende Monotonie der Ableitungsterme für CNF an.)

          -- Schritte:
          -- 1) Ableitungsbaum für z hat Word.len z Blätter
          have lemma_deriv_leaf_count := derivation_result_is_leaf_count (default_derivTree_z₂)

          -- TODO: Note, that a derivation is not a path!
          -- Fix this!

          -- 2) Ein Binärbaum mit Word.len z Blättern muss Pfade der Länge
          -- ≥ log₂ Word.len z enthalten
          have lemma_deriv_log := @derivation_path_length α nt₂ z₂.len cfg_CNF default_derivTree_z₂ (by
            rw [defaultDerivTree_z₂_respects_result] at lemma_deriv_leaf_count
            unfold Word.VZtoZ at lemma_deriv_leaf_count
            unfold Word.len at lemma_deriv_leaf_count
            rw [List.length_map, List.length_attach] at lemma_deriv_leaf_count
            simp at lemma_deriv_leaf_count
            exact lemma_deriv_leaf_count.symm
          )

          -- 3) Jeder Pfad der Länge ≥ Z.card muss mindestens eine Variable doppelt
          -- enthalten
          have lemma_multiple_var := @derivation_len_over_V_imp_double_var α nt₂ cfg_CNF [Sum.inl cfg_CNF.1.start] (Sum.inr <$> z₂) default_deriv_z₂

          -- Konsequenz: Wenn Word.len z ≥ 2^Z.card dann gibt es einen Pfad, in dem
          -- eine Variable doppelt vorkommt

          -- Word.len (v * w * x) ≤ n
          --Ein Binärbaum der Tiefe ℓ hat maximal 2ℓ Blätter
          --• Wir können annehmen, dass das obere doppelte Vorkommen der gewählten
          --Variable maximal |V| Schritte von der vorletzten Ebene (d.h. der letzten im inneren
          --Binärbaum) entfernt ist
          --• Also kann der Baum unterhalb dieses Vorkommens maximal 2|V| = n Blätter haben
          --(dies sind die Symbole in vwx)
          sorry

