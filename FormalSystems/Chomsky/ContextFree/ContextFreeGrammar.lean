import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor

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

/--Define context free derivations v (G)=>* w inductively. Constructors:

  - `same_var`  - 0 step derivations v (G)=>* v

  - `same_word` - 0 step derivations v (G)=>* w with w is a "word" that looks like v

  - `step`  - Given a derivation`v' → w'`, and a production rule

    `v → u_mid = l_of_v' * v' * r_of_v'`,

    construct a derivation

    `v → l_of_v' * w' * r_of_v'`-/
inductive ContextFreeDerivation (G: ContextFreeGrammar α nt): (v: G.V) → (w: Word (G.V ⊕ G.Z)) → Type
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

--Coercion CFDerivation into generic Derivations
instance : Coe (@ContextFreeDerivation α nt G v w) (@Grammar.Derivation α nt GenericProduction _ (↑G) (Word.mk [Sum.inl v]) w) where
  coe cfDerivation := match cfDerivation with
  | ContextFreeDerivation.same_var w' h =>
    have h_h : (Word.mk [Sum.inl v] = Word.mk [Sum.inl w']) := by simp [h]
    by exact Grammar.Derivation.same h_h
  | ContextFreeDerivation.same_word h =>
      Grammar.Derivation.same h
  | @ContextFreeDerivation.step α nt G v v' w w' u_mid l_of_v' r_of_v'
      h_production
      h_u_mid
      deriv_v'_to_w'
    =>
      let productionRule : G.productions := ⟨ {lhs:=v, rhs:=u_mid : ContextFreeProduction G.Z G.V} , h_production ⟩
      Grammar.Derivation.step (Grammar.DerivationStep.fromRule productionRule)
        ((deriv_v'_to_w' : ContextFreeDerivation G _ _) : Grammar.Derivation _ _)
        (sorry)

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
      simp;
      have hxs : xs = lhs.tail
      simp [h_lhs]
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
