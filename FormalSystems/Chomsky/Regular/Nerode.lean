import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Congruence
import FormalSystems.Preliminaries.Language
import FormalSystems.Chomsky.Regular.DFA

def MyhillNerodeRelation (L : Language α) (u v : Word α) : Prop :=
  ∀w, u * w ∈ L ↔ v * w ∈ L

notation:60 u:60 " ≃( " L:61 " ) " v:61 => MyhillNerodeRelation L u v

variable {L: Language α} {u v: Word α}

instance myhillNerodeEquivalence (L: Language α) : Setoid (Word α) where
  r a b := a ≃(L) b
  iseqv := {
    refl := fun _ _ => Iff.refl _
    symm := fun h w => (h w).symm
    trans := fun h1 h2 w => (h1 w).trans (h2 w)
  }

theorem MyhillNerodeRelation.right_congruence:
  u ≃(L) v ↔ ∀x, (u * x) ≃(L) (v * x) := by
  constructor
  . intro h w x
    have := h (w * x)
    rw [<- Word.monoid.mul_assoc] at this
    rw [<- Word.monoid.mul_assoc] at this
    assumption
  . intro h w
    have := (h w) ε
    simp at this
    assumption

notation "⟪" word "⟫" => Word.mk (String.toList word)

local instance : HasEquiv (Word α) where
  Equiv := fun a b => a ≃(L) b

theorem MyhillNerodeRelation.not_congruent_if (pre: u ≠ v):
  (∃w, Language.isSingleton ({u*w, v*w} ∩ L)) → ¬ u ≃(L) v := by
  intro ⟨ w, singl, singl_inter, h ⟩
  intro contra
  have h2 := contra w
  cases singl_inter.left
  case inl e =>
    have vw_in_l := h2.mp $ e ▸ singl_inter.right
    have vw_eq_uw := e ▸ h (v*w) ⟨ Or.inr rfl, vw_in_l ⟩
    exact pre <| Eq.symm <| Word.mul_right_cancel vw_eq_uw
  case inr e =>
    have uw_in_l := h2.mpr $ e ▸ singl_inter.right
    have uw_eq_vw := e ▸ h (u*w) ⟨ Or.inl rfl, uw_in_l ⟩
    exact pre <| Word.mul_right_cancel uw_eq_vw

theorem MyhillNerodeRelation.not_congruent_if':
  (∃w, u*w ∈ L ∧ v*w ∉ L) → ¬ u ≃(L) v := by
  intro ⟨ w, uw_in_l, vw_nin_l ⟩ contra
  apply vw_nin_l
  apply (contra w).mp
  exact uw_in_l

theorem MyhillNerodeRelation.mem_language:
  u ≃(L) v → (u ∈ L ↔ v ∈ L) := fun h => by
    have := h ε
    simp at this
    assumption

theorem MyhillNerodeRelation.mem_language':
  u ≃(L) v → ((u ∈ L) = (v ∈ L)) :=
    propext ∘ MyhillNerodeRelation.mem_language

def DecisionProcedure (L: Language α): Type := DecidablePred (· ∈ L)

-- classically, every Language has a decision procedure, so we might choose one
noncomputable def DecisionProcedure.classical: DecisionProcedure L := Classical.decPred (· ∈ L)

def FinalClass (L: Language α) (q: Quotient (myhillNerodeEquivalence L)): Prop :=
  q.lift (· ∈ L) (by apply MyhillNerodeRelation.mem_language')

def final_class_decidable (proc: DecisionProcedure L):
  DecidablePred (FinalClass L) := fun q =>
    q.recOn (f := proc) (h := by simp)

def liftPredicateToSubtype (p: α → Prop) (prop: α → Prop):
  { a : α // prop a } → Prop := p ∘ Subtype.val

def decidable_pred_from_subtype (p: α → Prop) (h: DecidablePred p):
  ∀prop: α → Prop, @DecidablePred { a: α // prop a } (p ∘ Subtype.val) :=
  fun _ ⟨x, _⟩ => h x

open Classical
def canonicalAutomaton {L: Language α} (proc: DecisionProcedure L)
  [Fintype α] [DecidableEq α]
  (nerode_classes: Fintype (Quotient (myhillNerodeEquivalence L))):
  (DFA α (Quotient (myhillNerodeEquivalence L))) where
  Z := Fintype.elems
  Q := nerode_classes.elems
  q₀ := ⟨ Quotient.mk _ ε, nerode_classes.complete _ ⟩
  F :=
    have : DecidablePred (FinalClass L ∘ Subtype.val) :=
      decidable_pred_from_subtype _ (final_class_decidable proc) _
    @Finset.filter _ (FinalClass L ∘ Subtype.val) this Fintype.elems.attach
  δ := fun (q, a) => some $ q.val.lift
    (fun w =>
      have w' := w * Word.mk [a.val]
      ⟨Quotient.mk (myhillNerodeEquivalence L) w',
      nerode_classes.complete _⟩)
    (fun a b => by
      simp [Quotient.eq (r := myhillNerodeEquivalence L)]
      intro h
      apply MyhillNerodeRelation.right_congruence.mp
      assumption)
