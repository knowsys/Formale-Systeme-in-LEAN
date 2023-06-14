import FormalSystems.Chomsky.Grammar
import Mathlib.Data.Finset.Functor

structure ContextFreeProduction (Z: Finset α) (V: Finset nt) where
  lhs: V
  rhs: Word (V ⊕ Z)

class Production.ContextFree (α nt : Type) (P: Finset α → Finset nt → Type)
  extends Production α nt P
  where
    lhs_var: P Z V → V
    lhs_condition: ∀(p: P Z V), lhs p = [.inl $ lhs_var p]

def Production.ContextFree.toContextFreeProduction [Production.ContextFree α nt P] :
  P Z V ↪ ContextFreeProduction Z V where
  toFun p := { lhs := lhs_var p, rhs := rhs p }
  inj' a b h := by
    simp at h
    apply (Production.prod_ext a b).mpr
    constructor
    . rw [lhs_condition a, lhs_condition b, List.cons_eq_cons]
      simp; exact h.left
    . exact h.right

instance : Coe (ContextFreeProduction Z V) (GenericProduction Z V) where
  coe p := {
    lhs := [.inl p.lhs],
    rhs := p.rhs,
    lhs_contains_var := ⟨ p.lhs, List.Mem.head _ ⟩
  }

def ContextFreeProduction.toProduction : ContextFreeProduction Z V ↪ GenericProduction Z V where
  toFun := Coe.coe
  inj' := by
    intro p₁ p₂; simp [Coe.coe]; intro h1 h2
    rw [List.cons_eq_cons] at h1; simp at h1
    match p₁ with
    | ⟨l, r⟩ => simp at h1; simp at h2; simp_rw [h1, h2]

instance : Production α nt ContextFreeProduction :=
  Production.fromEmbedding (fun _ _ => ContextFreeProduction.toProduction)

instance : Production.ContextFree α nt ContextFreeProduction where
  lhs_var p := p.lhs
  lhs_condition _ := by rfl

def ContextFreeGrammar (α nt: Type) := @Grammar α nt ContextFreeProduction _

instance : Coe (ContextFreeGrammar α nt) (@Grammar α nt GenericProduction _) where
  coe g := {
    Z := g.Z,
    V := g.V,
    start := g.start,
    productions := g.productions.map ContextFreeProduction.toProduction
  }

open Grammar

variable [Production.ContextFree α nt P] { G: Grammar P }

variable { v w: Word (G.V ⊕ G.Z) } { a: G.Z }

def Grammar.DerivationStep.cancel_left_cons (step: DerivationStep G w) (h: ∃v, w = (.inr a :: v)):
DerivationStep G (w.tail) where
  prod := step.prod
  pre := step.pre.tail
  suf := step.suf
  sound := by
    simp
    have sound := step.sound
    have ⟨_, h⟩ := h
    simp_rw [h] at sound
    cases Word.mul_eq_cons.mp (Eq.symm sound)
    case inl h =>
      have ⟨_, h'⟩ := Word.mul_eq_eps.mp h.1
      have c := Production.lhs_contains_var step.prod.val
      apply Exists.elim c
      intro _ c
      simp [h', Word.eps_eq_nil] at c
      contradiction
    case inr h' =>
      have ⟨_, l, r⟩ := h'
      cases Word.mul_eq_cons.mp l
      case inl h' =>
        have c := Production.ContextFree.lhs_condition step.prod.val
        have cc := c ▸ h'.2
        rw [List.cons_eq_cons] at cc
        simp at cc
      case inr h'' =>
        have ⟨_, ll, lr⟩ := h''
        simp [ll]; rw [<- lr, <- r]; simp [h]

def Word.mk { a: Type } (l: List a) : Word a := l

theorem Grammar.DerivationStep.cancel_left_cons_result (step: DerivationStep G w) (h:∃v, w = (.inr a :: v)):
  step.result = .inr a :: (step.cancel_left_cons h).result := by
  unfold cancel_left_cons; simp [result]
  apply Word.mul_eq_cons.mpr
  apply Or.inr
  exists Word.mk (step.pre.tail) * Production.rhs step.prod.val
  unfold Word.mk
  apply And.intro
  apply Word.mul_eq_cons.mpr
  apply Or.inr
  exists step.pre.tail
  constructor
  sorry
  rfl
  rfl

theorem Grammar.Derivation.rhs_nt_imp_lhs_nt (d: Derivation G w) (h: ∀a ∈ w, a.isLeft):
  ∀v ∈ d.lhs, v.isLeft := by
  induction d with
  | same =>
    intro v h'
    unfold lhs at h'
    exact h _ h'
  | step steps step dsound hind =>
    have ⟨prod, pre, suf, sound⟩ := step
    intro v hv
    simp [lhs] at hv

    apply hind
    case step.a => assumption

    case step.h =>
      rw [dsound] at h
      unfold DerivationStep.result at h
      dsimp at h
      intro a
      rw [sound]
      dsimp [HMul.hMul, Mul.mul]
      intro ha
      repeat rw [List.mem_append] at ha
      cases ha
      case inl ha =>
        cases ha
        sorry
        sorry
      
      case inr =>
        sorry

theorem Grammar.Derivation.rhs_destructured_of_lhs_cons (w: Word _) (d: G.Derivation w) (h: d.lhs = .inr a :: v):
  ∃w', w = .inr a :: w' := by
  match d with
  | same _ => exists v
  | step xs x sound =>
    unfold lhs at h
    have ih := xs.rhs_destructured_of_lhs_cons _ h
    exists (x.cancel_left_cons ih).result
    rw [sound]
    apply x.cancel_left_cons_result

def Grammar.Derivation.cancel_left_cons (w: Word _) (d: G.Derivation w) (h: d.lhs = .inr a :: v):
  G.Derivation w.tail := by
  match d with
  | same _ => simp; exact same _
  | step xs x sound =>
    unfold lhs at h
    have xs' := xs.cancel_left_cons _ h
    have h2 := xs.rhs_destructured_of_lhs_cons _ h
    rw [sound]
    rw [x.cancel_left_cons_result h2]; simp
    exact .step xs' (x.cancel_left_cons h2) rfl
