/-!
This file contains auxiliary results about lists that do not have anything to do with Formale Systeme.
-/

/--
Removing all occurrences of [[]] from a list before applying flatten does not change the result of flatten.
-/
theorem List.removeAll_nil_flatten [BEq α] : ∀ (l : List (List α)), (l.removeAll [[]]).flatten = l.flatten := by
  intro l
  induction l with
  | nil =>
    simp
  | cons a l ih =>
    rw [List.cons_removeAll]
    by_cases h : [[]].contains a
    . have a_eq : a=[] := by simp_all
      simp only [h]
      rw [a_eq, List.flatten_cons, List.nil_append, if_neg]
      . exact ih
      . trivial
    . simp only [h]
      rw [if_true]
      have a_eq : ¬(a = []) := by simp_all
      rw [List.flatten_cons, ih]
      rfl

/--
Eliminates duplicates from a list, keeping the rightmost occurrence. (Implementation copied from https://github.com/monsterkrampe/Basic-Lean-Datastructures/blob/main/BasicLeanDatastructures/List/EraseDupsKeepRight.lean)
-/
def List.removeDups [DecidableEq α] : List α -> List α
  | [] => []
  | hd::tl => if hd ∈ tl then tl.removeDups else hd::(tl.removeDups)

/--
Removing duplicates from a list does not change the elements contained in it.
-/
theorem List.mem_removeDups [DecidableEq α] (l : List α) : ∀ a, a ∈ l ↔ a ∈ l.removeDups := by
  induction l with
  | nil =>
    intro a
    simp only [removeDups]
  | cons b l' ih =>
    unfold removeDups
    intro a
    by_cases b_mem : b ∈ l'
    . simp only [b_mem, ite_true, List.mem_cons, ih]
      by_cases a_eq : a = b
      . simp only [a_eq, true_or]
        specialize ih b
        have aux : b ∈ l'.removeDups := ih.mp b_mem
        simpa using aux
      . simp only [a_eq, false_or]
    . simp only [b_mem, ite_false, List.mem_cons, ih]

/-- In a list with removed duplicates, each element has count 1. -/
theorem List.removeDups_count [DecidableEq α] (l : List α) : ∀ a, a ∈ l → l.removeDups.count a = 1 := by
  intro a a_mem
  have a_mem_rd : a ∈ l.removeDups := (mem_removeDups l a).mp a_mem
  induction l with
  | nil =>
    grind
  | cons b l' ih =>
    by_cases b_mem : b ∈ l'
    . simp only [removeDups, b_mem, ite_true]
      by_cases a_eq : a = b
      . rw [← a_eq] at b_mem
        simp only [removeDups, ← a_eq, b_mem, ite_true] at a_mem_rd
        apply ih b_mem a_mem_rd
      . simp only [mem_cons, a_eq, false_or] at a_mem
        have a_mem_l'_rd : a ∈ l'.removeDups := by
          simp only [removeDups, b_mem, ite_true] at a_mem_rd; exact a_mem_rd
        apply ih a_mem a_mem_l'_rd
    . simp only [removeDups, b_mem, ite_false]
      by_cases a_eq : a = b
      . simp only [a_eq]
        have count_b : l'.removeDups.count b = 0 := by
          rw [mem_removeDups] at b_mem
          rw [count_eq_zero]
          exact b_mem
        grind
      . have a_mem_l' : a ∈ l' := by
          rw [mem_cons] at a_mem
          simp only [a_eq, false_or] at a_mem
          exact a_mem
        rw [mem_removeDups] at a_mem_l'
        grind

theorem List.removeDups_nodup [DecidableEq α] (l : List α) : l.removeDups.Nodup := by
  unfold Nodup removeDups
  induction l_eq : l generalizing l with
  | nil =>
    simp only [Pairwise.nil]
  | cons h t ih =>
    have aux := ih t rfl
    simp only [forall_eq] at *
    by_cases h_mem : h ∈ t
    . simp only [h_mem, ite_true]
      unfold removeDups
      exact aux
    . simp only [h_mem, ite_false, pairwise_cons]
      constructor
      . intro a a_mem
        rw [← mem_removeDups] at a_mem
        grind
      . unfold removeDups
        exact aux

/--
Infix is decidable for Lists whose elements have decidable equality. (The proof is essentially the expanded version of the one from mathlib)
-/
instance List.decidableInfix [DecidableEq α] : ∀ (k l : List α), Decidable (k <:+: l)
  | [], l => by
    apply isTrue
    unfold List.IsInfix
    exists l, []
    simp only [append_nil]
  | a :: k, [] => by
    apply isFalse
    unfold List.IsInfix
    simp only [append_assoc, cons_append, append_eq_nil_iff, reduceCtorEq, and_false, exists_const,
      not_false_eq_true]
  | k, b :: l =>
    letI := k.decidableInfix l
    @decidable_of_decidable_of_iff (k <+: b :: l ∨ k <:+: l) _ _
      infix_cons_iff.symm
