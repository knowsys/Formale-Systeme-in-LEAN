import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Prod

import FormalSystems.Preliminaries.Fold

structure Variable where
  index: Nat
  deriving DecidableEq

theorem Variable.eq (v₁ v₂: Variable): v₁ = v₂ ↔ v₁.index = v₂.index := by
  constructor
  . intro; congr
  . intro h
    cases v₁; cases v₂
    dsimp at h; rw [h]

inductive LoopProgram
| add (x y: Variable) (n: Nat)
| sub (x y: Variable) (n: Nat)
| concat (p₁ p₂: LoopProgram)
| loop (x: Variable) (p: LoopProgram)
deriving DecidableEq

def LoopProgram.toFunction (p: LoopProgram):
  Nat → Nat :=
  -- Todo: define how to evaluate `p`, with x₀ bound to the input
  -- for example one could use a state monad with an `AssocList`
  sorry

def LoopProgram.len: LoopProgram → Nat
| add x y n => x.index + y.index + n + 1
| sub x y n => x.index + y.index + n + 1
| concat p₁ p₂ => p₁.len + p₂.len + 1
| loop n p => p.len + n.index + 1

theorem LoopProgram.len_gt_zero:
  ∀ p: LoopProgram, p.len > 0 := by
  intro p
  cases p <;> unfold len <;> simp_arith

def LoopProgram.lenOne: Finset LoopProgram :=
  { add (Variable.mk 0) (Variable.mk 0) 0,
    sub (Variable.mk 0) (Variable.mk 0) 0 }

theorem LoopProgram.lenOne_complete:
  ∀ p: LoopProgram, p.len = 1 → p ∈ LoopProgram.lenOne := by
  intro p h
  cases p <;> simp [len] at h <;> simp [h, lenOne, Variable.eq]
  case concat p =>
    apply Nat.not_le_of_gt
    apply LoopProgram.len_gt_zero p
    apply Nat.le_of_eq
    exact h.right
  case loop p =>
    apply Nat.not_le_of_gt
    apply LoopProgram.len_gt_zero p
    apply Nat.le_of_eq
    exact h.left

def LoopProgram.extendLenOne: LoopProgram → Finset LoopProgram
| add x y n =>
  { add (Variable.mk $ x.index + 1) y n,
    add x (Variable.mk $ y.index + 1) n,
    add x y (n + 1)
  }
| sub x y n =>
  { sub (Variable.mk $ x.index + 1) y n,
    sub x (Variable.mk $ y.index + 1) n,
    sub x y (n + 1)
  }
| concat p₁ p₂ =>
  Finset.image (λp => concat p p₂) p₁.extendLenOne ∪
  Finset.image (λp => concat p₁ p) p₂.extendLenOne
| loop x p =>
  { loop (Variable.mk $ x.index + 1) p } ∪
  Finset.image (λp => loop x p) p.extendLenOne

def LoopProgram.ofLen: Nat → Finset LoopProgram
| 0 => {}
| 1 => LoopProgram.lenOne
| 2 =>
  Finset.fold (λa b => a ∪ b) {} extendLenOne lenOne ∪
  Finset.image (λp => loop (Variable.mk 0) p) lenOne
| 3 =>
  Finset.fold (λa b => a ∪ b) {} extendLenOne (ofLen 2) ∪
  Finset.image (λ(p₁, p₂) => concat p₁ p₂) (Finset.product lenOne lenOne)
| n + 1 =>
  Finset.fold (λa b => a ∪ b) {} extendLenOne (ofLen n)

open LoopProgram

theorem LoopProgram.ofLen_two_complete:
  ∀ p: LoopProgram, p.len = 2 → p ∈ LoopProgram.ofLen 2 := by
  intro p h
  rw [ofLen]
  match p with
  | add (.mk x) (.mk y) m =>
    simp
    apply Finset.mem_fold_union_iff.mpr
    exists add (.mk 0) (.mk 0) 0
    simp [extendLenOne]
    dsimp [len] at h
    cases x <;> cases y <;> simp [Nat.succ_add] at h <;> simp [h]
  | sub (.mk x) (.mk y) m =>
    simp
    apply Finset.mem_fold_union_iff.mpr
    exists sub (.mk 0) (.mk 0) 0
    simp [extendLenOne]
    dsimp [len] at h
    cases x <;> cases y <;> simp [Nat.succ_add] at h <;> simp [h]
  | loop (.mk x) p =>
    apply Finset.mem_union_right
    simp
    dsimp [len] at h
    cases x <;> simp [Nat.add_succ] at h <;> simp [lenOne_complete, h]
    apply Nat.ne_of_gt
    apply p.len_gt_zero
    exact h.left
  | concat p₁ p₂ =>
    apply False.elim
    simp [len] at h
    apply Nat.not_le.mpr; swap
    apply Nat.le_of_eq h
    apply Nat.succ_lt_succ
    apply Nat.lt_of_le_of_lt
    show 1 ≤ p₁.len
    apply len_gt_zero
    simp
    apply len_gt_zero


theorem LoopProgram.ofLen_complete (n: Nat):
  ∀ p: LoopProgram, p.len = n → p ∈ LoopProgram.ofLen n := by
  intro p h
  match n with
  | 0 =>
    apply False.elim
    apply Nat.ne_of_gt
    apply len_gt_zero p
    assumption
  | 1 =>
    dsimp [ofLen]
    apply lenOne_complete
    assumption
  | 2 =>
    apply ofLen_two_complete
    assumption
  -- Todo: prove, that all possible programs are caught by the above defn.
  -- this could be done with a special case for len 3, from len 4 everything follows from induction
  | n + 3 => sorry

def LoopProgram.diagonal (n: Nat): Nat := 
  Finset.fold max 0 (λ p => p.toFunction n) (LoopProgram.ofLen n) + 1

theorem LoopProgram.diagonal_is_not_loop_computable:
  ∀ p: LoopProgram, p.toFunction ≠ diagonal := by
  intro p h
  apply Nat.ne_of_lt

  . show p.toFunction p.len < diagonal p.len
    unfold diagonal
    rw [Nat.lt_add_one_iff, Finset.le_fold_max]
    apply Or.inr
    exists p; constructor
    apply ofLen_complete; rfl
    rfl

  . apply congrFun
    assumption
