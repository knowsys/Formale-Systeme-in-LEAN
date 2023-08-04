import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Fold

variable [DecidableEq β]

theorem List.mem_fold_union_iff { l: List (Finset β) }:
  e ∈ List.foldr (· ∪ ·) ∅ l ↔ ∃s ∈ l, e ∈ s := by
  constructor
  . intro h
    induction l with
    | nil => contradiction
    | cons _ _ ih =>
      simp at h
      cases h <;> simp
      . apply Or.inl
        assumption
      . apply Or.inr
        apply ih
        assumption

  . intro ⟨s, h, _⟩
    induction l with
    | nil => contradiction
    | cons _ _ ih =>
      simp at h
      cases h <;> simp
      case inl h =>
        apply Or.inl; rw [<- h]
        assumption
      case inr _ =>
        apply Or.inr
        apply ih
        assumption

theorem Finset.mem_fold_union_iff { f: α → Finset β }:
  e ∈ Finset.fold Union.union ∅ f s ↔ ∃ x ∈ s, e ∈ f x := by
  constructor
  . have ⟨s, _⟩ := s
    revert s
    apply Quot.ind
    intro l _ h
    dsimp [Finset.fold] at h
    have ⟨_, h, _⟩ := List.mem_fold_union_iff.mp h
    simp at h
    have ⟨x, _, h⟩ := h
    exists x; simp [h]
    constructor; repeat { assumption }

  . intro ⟨x, h₁, h₂⟩
    have ⟨s, _⟩ := s
    revert s
    apply Quot.ind
    intro l _ h
    simp [Finset.fold, Multiset.fold]
    apply List.mem_fold_union_iff.mpr
    exists f x
    simp; constructor
    exists x
    assumption
