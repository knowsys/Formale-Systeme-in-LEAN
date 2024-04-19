import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Congruence
import FormalSystems.Preliminaries.Language
import FormalSystems.Chomsky.Regular.TotalDFA

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
  DecidablePred (FinalClass L) := fun q => q.recOnSubsingleton proc

def liftPredicateToSubtype (p: α → Prop) (prop: α → Prop):
  { a : α // prop a } → Prop := p ∘ Subtype.val

def decidable_pred_from_subtype (p: α → Prop) (h: DecidablePred p):
  ∀prop: α → Prop, @DecidablePred { a: α // prop a } (p ∘ Subtype.val) :=
  fun _ ⟨x, _⟩ => h x

variable {α: Type} {Z: Finset α} {L: Language Z}
variable {proc: DecisionProcedure L}
variable (nc: Fintype $ Quotient (myhillNerodeEquivalence L))

def canonicalAutomaton: (TotalDFA α (Quotient (myhillNerodeEquivalence L))) where
  Z := Z
  Q := nc.elems
  q₀ := ⟨ Quotient.mk _ ε, nc.complete _ ⟩
  F :=
    have : DecidablePred (FinalClass L) := final_class_decidable proc
    Finset.map
      ⟨fun q => ⟨q, nc.complete _⟩, fun _ _ h => by simp at h; assumption⟩
      (@Finset.filter _ (FinalClass L) this nc.elems)
  δ := fun (q, a) => some $ q.val.lift
    (fun w =>
      let w' := w * Word.mk [a]
      ⟨Quotient.mk (myhillNerodeEquivalence L) w',
      nc.complete _⟩)
    (fun a b => by
      simp [Quotient.eq (r := myhillNerodeEquivalence L)]
      intro h
      apply MyhillNerodeRelation.right_congruence.mp
      assumption)
  totality := fun _ _ => rfl

variable {nc: Fintype (Quotient (myhillNerodeEquivalence L))}

set_option quotPrecheck false
local notation "⟪" word "⟫" =>
  ⟨Quotient.mk (myhillNerodeEquivalence L) word, nc.complete _⟩
set_option quotPrecheck true

theorem del_eq:
  let M := canonicalAutomaton nc (proc := proc)
  ∀(w: Word M.Z), ∀a, M.δ' (⟪w⟫, a) = ⟪w * Word.mk [a]⟫ :=
  fun _ _ => rfl

theorem del_star_eq:
  let M := canonicalAutomaton nc (proc := proc)
  ∀(w: Word M.Z), ∀v, M.del_star' (⟪w⟫, v) = ⟪w * v⟫ :=
  fun w v => Subtype.eq $ by
    induction v generalizing w
    case nil => simp [<-Word.eps_eq_nil, Word.monoid.mul_one]; rfl
    case cons _ _ ih =>
      simp [HMul.hMul, Mul.mul]
      simp [TotalDFA.del_star']
      rw [List.append_cons]
      apply ih

theorem final_state_eq:
  let M := canonicalAutomaton nc (proc := proc)
  ∀w, M.del_star' (⟪ε⟫, w) = ⟪w⟫ := fun w => Subtype.eq $ by
  simp [del_star_eq]

theorem initial_state_eq:
  let M := canonicalAutomaton nc (proc := proc)
  M.q₀ = ⟪ε⟫ := rfl

theorem final_state_accepts_iff:
  let M := canonicalAutomaton nc (proc := proc)
  ∀w, M.del_star' (M.q₀, w) ∈ M.F ↔ w ∈ L := by
  intro M w
  rw [initial_state_eq, final_state_eq]
  simp [M, canonicalAutomaton]
  simp [Fintype.complete]
  unfold FinalClass
  rw [@Quotient.lift_mk _ _ (myhillNerodeEquivalence L) _ _ _]

theorem canonicalAutomaton_accepted_language:
  (canonicalAutomaton nc (proc := proc)).AcceptedLanguage = L := by
  apply Set.ext
  intro w
  rw [TotalDFA.in_language_iff_del_star_final, final_state_accepts_iff]
