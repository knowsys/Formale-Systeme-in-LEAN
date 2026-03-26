import FormaleSystemeInLean.Set
import FormaleSystemeInLean.Finset

/-!
The powerset DFA (as it is defined in Lecture 4) has subsets of Q (the states of the original NFA)
as its states. However, the automaton definitions in this formalisation don't use finite sets of states
but instead lists over a Fintype Q. So we need to define something like a powerset but for lists.
We also need to prove that the resulting "powerlist" contains only finitely many elements
because the states of an NFA have to be of a Fintype.
-/

/--
The powerset of a set X just contains all possible subsets of X. (See Set.lean)
We define the power of a list l as the list containing all lists up to the length if l with elements from l.
The following recursive function computes all lists with elements from a given list l that have
a length up to n. This includes lists with duplicate elements and all possible sequences.
We do this by repeatedly appending elements of l to all lists we currently have.
-/
def List.power_upto (l : List α) (n : Nat) : List (List α) :=
  let rec loop : Nat → List (List α)
    | 0 => [[]]
    | n+1 => let prev := loop n; prev ++ (prev.flatMap (fun l' => l.map fun e => e:: l'))
  loop n

/-!
This example shows how the power of a list is computed. As you can see, all the
different lists are added to the powerlist multiple times.
-/
#eval [0, 1, 2, 3].power_upto 4

/-!
After defining the power of a list, we can use this function to compute the Powertype of a Fintype
and prove that it is also finite. As a reminder: a Fintype is a type with a corresponding list ("elems")
containing all things of this type (refer to Fintype.lean for further information).

The following 4 theorems are auxiliary results required to prove that for a Fintype T with elements of type α
T.elems.power_upto (T.elems.length) contains all lists of type List α that are at most of the same length as T.elems.
-/

/-- the result of [].power_upto n is [[]] for all n. -/
theorem nil_power (n : Nat) (l : List α) : l = [] -> l.power_upto n = [[]] := by
  intro l_eq
  induction n with
  | zero =>
    unfold List.power_upto List.power_upto.loop
    rfl
  | succ n ih =>
    unfold List.power_upto List.power_upto.loop
    subst l
    simp only [List.map_nil]
    unfold List.power_upto at ih
    rw [ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- T.elems.power_upto n contains every List α of length n -/
theorem mem_power_upto_n (T : Fintype α) (l : List α) : l.length ≤ T.elems.length → l ∈ T.elems.power_upto (l.length) := by
  intro l_length
  induction n_eq : l.length generalizing l with
  | zero =>
    unfold List.power_upto List.power_upto.loop
    rw [← List.eq_nil_iff_length_eq_zero] at n_eq
    rw [n_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  | succ n ih =>
    have l_neq_nil : l ≠ [] := by
        have l_len_gz : l.length > 0 := by
          rw [← Nat.succ_eq_add_one] at n_eq
          grind
        rw [List.ne_nil_iff_length_pos]
        exact l_len_gz
    have l_eq : ∃ a l', l = a::l' ∧ l'.length = n := by
      rw [List.ne_nil_iff_exists_cons] at l_neq_nil
      rcases l_neq_nil with ⟨a, l', l_eq⟩
      exists a, l'
      constructor
      . exact l_eq
      . grind
    rcases l_eq with ⟨a, l', l_eq, l'_len⟩
    have l'_len_le : l'.length ≤ T.elems.length := by grind
    have l'_mem := ih l' l'_len_le l'_len
    unfold List.power_upto List.power_upto.loop
    simp only [List.mem_append, List.mem_flatMap, List.mem_map]
    apply Or.inr
    exists l'
    constructor
    . exact l'_mem
    . exists a
      constructor
      . exact T.complete a
      . symm; exact l_eq

-- I left the old version of this theorem here as an example for an overly complicated proof.
theorem mem_power_upto_n' (T : Fintype α) (l : List α) (n : Nat) : n ≤ T.elems.length → l.length = n → l ∈ T.elems.power_upto n := by
  intro n_le l_len
  cases h : T.elems with
  | nil =>
    rw [nil_power]
    . cases l with
    | nil =>
      grind
    | cons a s =>
      cases n with
      | zero =>
        grind
      | succ n =>
        rw [List.mem_singleton]
        exfalso
        have elems_length : T.elems.length = 0 := by
          rw [List.eq_nil_iff_length_eq_zero] at h
          exact h
        rw [elems_length] at n_le
        contradiction
    . rfl
  | cons b s =>
    induction n generalizing l with
    | zero =>
      unfold List.power_upto List.power_upto.loop
      have l_eq : l = [] := by
        rw [List.eq_nil_iff_length_eq_zero]
        exact l_len
      rw [l_eq]
      grind
    | succ n ih =>
      unfold List.power_upto List.power_upto.loop
      simp only [List.map_cons, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
      have l_neq_nil : l ≠ [] := by
        have l_len_gz : l.length > 0 := by
          rw [← Nat.succ_eq_add_one] at l_len
          grind
        rw [List.ne_nil_iff_length_pos]
        exact l_len_gz
      have l_eq : ∃ a l', l = a::l' ∧ l'.length = n := by
        rw [List.ne_nil_iff_exists_cons] at l_neq_nil
        rcases l_neq_nil with ⟨a, l', l_eq⟩
        exists a, l'
        constructor
        . exact l_eq
        . grind
      rcases l_eq with ⟨a, l', l_eq, l'_len⟩
      have aux : n ≤ T.elems.length := by grind
      apply Or.inr
      exists l'
      constructor
      . apply ih l' aux l'_len
      . by_cases ha : a = b
        . apply Or.inl
          rw [← ha]
          exact l_eq
        . apply Or.inr
          exists a
          constructor
          . have a_mem : a ∈ b::s := by
              have complete := T.complete
              specialize complete a
              rw [h] at complete
              exact complete
            grind
          symm
          exact l_eq

/-- If a list l is contained in T.elems.power_upto n, then it is also an element of l ∈ T.elems.power_upto (n+1). -/
theorem inclusion_succ (T : Fintype α) (l : List α) (n : Nat) : l.length ≤ T.elems.length -> l ∈ T.elems.power_upto n -> l ∈ T.elems.power_upto (n+1) := by
  intro l_len l_mem
  unfold List.power_upto List.power_upto.loop
  simp
  apply Or.inl
  exact l_mem

theorem inclusion (T : Fintype α) (l : List α) (n : Nat) (m : Nat) : n ≤ m -> l ∈ T.elems.power_upto n -> l ∈ T.elems.power_upto m := by
  intro le l_mem
  induction le with
  | refl =>
    simp_all
  | @step k b ih =>
    unfold List.power_upto List.power_upto.loop
    simp only [List.mem_append, List.mem_flatMap, List.mem_map]
    apply Or.inl
    exact ih

/-- Now we can finally prove that the powerlist of T.elems contains all lists of length at most T.elems.length: -/
theorem powerlist (T : Fintype α) (l : List α) : l.length ≤ T.elems.length -> l ∈ T.elems.power_upto T.elems.length := by
  intro l_len
  cases ht: T.elems with
  | nil =>
    rw [List.eq_nil_iff_length_eq_zero] at ht
    simp only [List.length_nil]
    unfold List.power_upto List.power_upto.loop
    rw [ht, Nat.le_zero, ← List.eq_nil_iff_length_eq_zero] at l_len
    rw [l_len, List.mem_singleton]
  | cons b s =>
    have incl := inclusion_succ T l l.length l_len
    have mem_power := mem_power_upto_n T l l_len
    rw [ht, List.length_cons, Nat.le_add_one_iff] at l_len
    rcases l_len with inl | inr
    . have test := incl mem_power
      rw [ht] at test
      rw [List.length_cons]
      have aux3 := inclusion T l l.length s.length inl mem_power
      unfold List.power_upto List.power_upto.loop
      simp only [List.map_cons, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
      apply Or.inl
      rw [← ht]
      exact aux3
    . rw [inr, ht] at mem_power
      rw [List.length_cons]
      exact mem_power


/-! We use Finset instead of Set here because it enables easier proofs for (e.g.) DecidablePred (a ∈ X) and DecidableEq. -/

def Powertype (α : Type u) := Finset α

instance : Membership α (Powertype α) where
  mem S a := Finset.mem a S

instance Finset.instFintypeOfFintype [T : Fintype α] [DecidableEq α] : Fintype (Finset α) where
  elems := (T.elems.power_upto T.elems.length).map (fun x => Finset.mk x)
  complete := by
    intro S
    simp only [List.mem_map]
    exists T.elems.filter (fun x => decide (x ∈ S))
    constructor
    . have length : (T.elems.filter (fun x => decide (x ∈ S))).length ≤ T.elems.length := by apply List.length_filter_le
      exact powerlist T (T.elems.filter (fun x => decide (x ∈ S))) length
    . apply Finset.ext
      intro a
      have mem_iff : ∀ a, a ∈ (T.elems.filter (fun x => decide (x ∈ S))) ↔ a ∈ S := by
        intro a
        simp only [List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
        intro a_mem
        exact T.complete a
      have mem_mk : ∀ a, a ∈ (T.elems.filter (fun x => decide (x ∈ S))) ↔ a ∈ (Finset.mk (T.elems.filter (fun x => decide (x ∈ S)))) := by
        apply mem_list_iff_mem_mk
      grind

instance [T : Fintype α] [DecidableEq α] : Fintype (Powertype α) := Finset.instFintypeOfFintype
