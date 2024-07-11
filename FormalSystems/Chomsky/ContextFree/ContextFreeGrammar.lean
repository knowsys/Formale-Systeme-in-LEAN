import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor
import Mathlib.Tactic.Tauto
import FormalSystems.Chomsky.ContextFree.ContextFreeProductions

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
-- Section: Miscellaneous Theorems
--=============================================================

variable [i: Production.ContextFree α nt P] { G: Grammar P}


/--Theorem: Derivation steps in context free grammars that start in the string
  lhs, with lhs = a :: xs, where a is a terminal symbol,
  have the symbol a as the leftmost symbol of
  the`pre`attribute also.
  -/
theorem derivation_step_prefix
  { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (step: G.DerivationStep lhs) (h_lhs: lhs = (.inr a :: xs)):
  step.pre = Sum.inr a :: step.pre.tail := by
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
theorem derivation_preserves_prefix
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
      rw [@ContextFreeGrammar.derivation_step_prefix α nt _ _ _ lhs xs a d h_lhs]
      simp
  }
  property := by
    simp [Grammar.DerivationStep.result, HMul.hMul, Mul.mul]
    rw [<- List.tail_append_of_ne_nil]
    rw [ContextFreeGrammar.derivation_step_prefix d h_lhs]
    simp



/--Given a derivation a::xs (G)=>* w,
  construct a derivation xs (G)=>* w-/
def Grammar.Derivation.cancelLeft
  { w: Word G.Z } { xs: Word (G.V ⊕ G.Z) } { a: G.Z }
  (d: G.Derivation lhs rhs) (h_lhs: lhs = (.inr a :: xs)) (h_rhs: rhs = (.inr <$> w)):
  G.Derivation xs (.inr <$> w.tail) := by
  match d with
  | .same h =>
    apply Grammar.Derivation.same
    rw [<- h, h_lhs] at h_rhs
    cases w
    contradiction
    simp at h_rhs
    rw [List.cons_eq_cons] at h_rhs
    simp [h_rhs.2]
  | .step s d r =>
    let ⟨s', r'⟩ := ContextFreeGrammar.Grammar.DerivationStep.cancelLeft s h_lhs
    rw [r] at r'
    apply Grammar.Derivation.step (u' := s'.result)
    swap; rfl
    apply (ContextFreeGrammar.Grammar.Derivation.cancelLeft d)
    rw [r', <-r]
    simp [Grammar.DerivationStep.result, HMul.hMul, Mul.mul]
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
  unfold Grammar.Derivation.len
  rfl

/--Theorem: Terminal symbols on the left-hand side don't induce derivation steps:
  The derivation a::xs (G)=>* w
  and the derivation xs (G)=>* w.tail have the same length.-/
theorem Grammar.Derivation.cancelLeft_len
  (d: G.Derivation lhs rhs):
  (ContextFreeGrammar.Grammar.Derivation.cancelLeft d h_lhs h_rhs).len = d.len := by
  match d with
  | .same _ => simp [Grammar.Derivation.len]
  | .step _ _ _ =>
    simp [Grammar.Derivation.len]
    apply cancelLeft_len
