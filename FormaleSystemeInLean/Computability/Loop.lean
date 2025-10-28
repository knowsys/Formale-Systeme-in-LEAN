import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Cases

import FormaleSystemeInLean.Preliminaries.Fold

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

def LoopProgram.len: LoopProgram → Nat
| add x y n => x.index + y.index + n + 1
| sub x y n => x.index + y.index + n + 1
| concat p₁ p₂ => p₁.len + p₂.len + 1
| loop n p => p.len + n.index + 1

def LoopProgramState := Lean.AssocList Variable Nat

namespace LoopProgramState
  def get (s: LoopProgramState) (v: Variable): Nat := (s.find? v).getD 0

  def put (s: LoopProgramState) (v: Variable) (n: Nat): LoopProgramState :=
    if s.contains v then s.replace v n else s.insert v n
end LoopProgramState

def LoopProgram.run: LoopProgram -> LoopProgramState -> LoopProgramState
| add x y n => fun s =>
  let new_val := s.get y + n
  s.put x new_val
| sub x y n => fun s =>
  let new_val := s.get y - n
  s.put x new_val
| concat p q => fun s =>
  q.run (p.run s)
| loop x p => fun s =>
  Nat.iterate p.run (s.get x) s

def LoopProgram.toFunction (p: LoopProgram) (input: Nat): Nat :=
  let x0 : Variable := { index := 0 }
  let initialState : LoopProgramState := Lean.AssocList.cons x0 input Lean.AssocList.nil
  let result : LoopProgramState := p.run initialState
  result.get x0

theorem LoopProgram.len_gt_zero:
  ∀ p: LoopProgram, p.len > 0 := by
  intro p
  cases p <;> unfold len <;> simp

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
    add x y (n + 1),
    loop (.mk 0) (add x y n)
  }
| sub x y n =>
  { sub (Variable.mk $ x.index + 1) y n,
    sub x (Variable.mk $ y.index + 1) n,
    sub x y (n + 1),
    loop (.mk 0) (sub x y n)
  }
| concat p₁ p₂ => { loop (.mk 0) (concat p₁ p₂) }
| loop x p =>
  { loop (Variable.mk $ x.index + 1) p, loop (.mk 0) (loop x p) } ∪
  Finset.image (λp => loop x p) p.extendLenOne

def LoopProgram.baseProgram: Nat → Finset LoopProgram
| 0 => {}
| 1 => LoopProgram.lenOne
| 2 => Finset.image (loop (Variable.mk 0)) lenOne
| _ => {}

def LoopProgram.ofLen: Nat → Finset LoopProgram
| 0 => {}
| n + 1 =>
  Finset.fold (λa b => a ∪ b) {} extendLenOne (ofLen n) ∪
  Finset.fold (·∪·) {}
    (λ⟨l, h⟩ =>
      have : l < Nat.succ n := by rw [Finset.mem_range] at h; apply Nat.lt_succ_of_lt; assumption
      (Finset.product (ofLen l) (ofLen $ n - l)).image
      (λ(a, b) => concat a b))
    (Finset.range n).attach ∪
  baseProgram (n + 1)
-- NOTE that termination_by is not needed but we do need the have statement to show termination

open LoopProgram

theorem LoopProgram.ofLen_contains_extendLenOne_image
  (h₁: p ∈ ofLen n) (h₂: p' ∈ p.extendLenOne):
  p' ∈ ofLen (n + 1) := by
  unfold ofLen
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_fold_union_iff.mpr
  exists p

theorem LoopProgram.ofLen_stmt_complete
  (stmt: Variable → Variable → ℕ → LoopProgram)
  (h_stmt: stmt = add ∨ stmt = sub):
  stmt (.mk x) (.mk y) n ∈ LoopProgram.ofLen (x + y + n + 1) := by
  simp [ofLen]
  cases' x with x'
  cases' y with y'
  cases' n with n'
  . refine' .inr ∘ .inr $ lenOne_complete _ _
    cases' h_stmt with h h <;> rw [h] <;> rfl
  . apply Or.inl ∘ Finset.mem_fold_union_iff.mpr
    refine' ⟨stmt (.mk 0) (.mk 0) n', ⟨ofLen_stmt_complete _ h_stmt, _⟩⟩
    cases' h_stmt with h h <;> rw [h] <;> simp [extendLenOne]
  . apply Or.inl ∘ Finset.mem_fold_union_iff.mpr
    refine' ⟨stmt (.mk 0) (.mk y') n, ⟨_, _⟩⟩
    rw [Nat.add_succ, Nat.succ_add, Nat.succ_eq_add_one]
    apply ofLen_stmt_complete _ h_stmt
    cases' h_stmt with h h <;> rw [h] <;> simp [extendLenOne]
  . apply Or.inl ∘ Finset.mem_fold_union_iff.mpr
    refine' ⟨stmt (.mk x') (.mk y) n, ⟨_, _⟩⟩
    rw [Nat.succ_add, Nat.succ_add, Nat.succ_eq_add_one]
    apply ofLen_stmt_complete _ h_stmt
    cases' h_stmt with h h <;> rw [h] <;> simp [extendLenOne]
termination_by x + y + n

theorem LoopProgram.ofLen_complete:
  ∀ p: LoopProgram, p ∈ LoopProgram.ofLen p.len := by
  intro p
  match p with
  | add (.mk x) (.mk y) n =>
    apply ofLen_stmt_complete
    apply Or.inl; rfl
  | sub (.mk x) (.mk y) m =>
    apply ofLen_stmt_complete
    apply Or.inr; rfl
  | loop (.mk x) p =>
    dsimp [len]
    cases' x with x'
    match h: p.len with
    | 0 => exact False.elim $ Nat.ne_of_gt p.len_gt_zero h
    | 1 =>
      unfold ofLen
      apply Finset.mem_union_right
      apply Finset.mem_image_of_mem
      exact lenOne_complete _ h
    | n + 1 =>
      apply ofLen_contains_extendLenOne_image
      rw [<- Nat.succ_eq_add_one, <- h]
      apply ofLen_complete
      cases p <;> simp [extendLenOne]
    apply ofLen_contains_extendLenOne_image
    case p => exact loop (.mk x') p
    have : p.len + x'.succ = (loop (.mk x') p).len := by rfl
    rw [this]
    apply ofLen_complete
    simp [extendLenOne]
  | concat a b =>
    simp [len, ofLen]
    refine' .inr $ .inl (Finset.mem_fold_union_iff.mpr ⟨⟨a.len, _⟩, _⟩)
    rw [Finset.mem_range]; simp [len_gt_zero]
    simp
    exact ⟨ofLen_complete _, ofLen_complete _⟩

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
    apply ofLen_complete
    rfl

  . apply congrFun
    assumption
