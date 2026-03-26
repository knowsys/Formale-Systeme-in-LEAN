import FormaleSystemeInLean.List
import FormaleSystemeInLean.Powertype

/-!
Formalisation of lecture 1:
This file covers the definition of words and languages as well as
operations on words and languages and theorems about rules applying to these operations.
The slides are available at https://iccl.inf.tu-dresden.de/web/Formale_Systeme_(WS2025)#BEtabid1-2 (German)
-/


/-!
On slide 28 an alphabet is defined as a nonempty finite set of symbols.
In lean it is more convenient to just use a type here instead of a set.
The elements of Sigma could be anything: unicode characters, numbers, strings...
The only restriction we make is assuming that, given two alphabet symbols of type Sigma,
we can decide wether they are equal or not. Otherwise it would be impossible to compare words.
-/
variable {Sigma : Type u}

/-- Words are merely lists over some alphabet Sigma. -/
abbrev Word (Sigma : Type u) := List Sigma

/-- Concatenating two words u and v simpy means appending list v to list u. This typeclass instance enables us to write * as an infix operator. -/
instance : Mul (Word Sigma) where
  mul u v := List.append u v

theorem Word.mul_eq (u v : Word Sigma) : u * v = u++v := by
  trivial

/-- Concatenation of words is associative. -/
theorem Word.mul_assoc (u v w : Word Sigma) : (u * v) * w = u * (v * w) := by
  simp only [mul_eq]; rw [List.append_assoc]

-- Examples
#eval ['a','b'] * ['b','a']

def some_word : Word Char := ['S','t','a','u','b','e','c','k','e','n']
def another_word : Word Char := ['A','l','t','b','a','u','c','h','a','r','m','e']

/-! Lean's built-in list type already offers predicates for prefix, infix and suffix as defined in the lecture (slide 30) -/
#eval List.IsPrefix ['S','t','a','u','b'] some_word
#eval List.IsInfix ['t','a','u','b'] some_word
#eval List.IsSuffix ['e','c','k','e','n'] some_word

/-!
For every alphabet Sigma, there is an empty word ε. Since we defined words as Lists
with elements of type Sigma, ε is just the empty list [].
ε is the identity element for concatenation of words:
-/

/-- Example from slide 30 (follows from list lemmas) -/
theorem epsilon_prefix_infix_suffix (w : Word Sigma) : [].IsPrefix w ∧ [].IsInfix w ∧ [].IsSuffix w := by
  simp only [List.nil_prefix, List.nil_infix, List.nil_suffix, and_self]

/-- Auxiliary result for epsilon_concat -/
theorem append_nil : ∀ (L : List α), L.append [] = L := by
  intro L
  simp only [List.append_eq, List.append_nil]

/-- w * ε = w -/
theorem epsilon_concat : ∀ (w : Word Sigma), w * [] = w := by
  intro w
  cases w with
  | nil =>
    trivial
  | cons σ u =>
    apply append_nil

/-- ε * w = w -/
theorem concat_epsilon : ∀ (w : Word Sigma), [] * w = w := by
  intro w
  cases w with
  | nil =>
    trivial
  | cons σ u =>
    trivial

/-- A language is just a set of words. -/
abbrev Language (Sigma : Type u) := Set (Word Sigma)

/-- The "biggest language" Σ* contains all words over Σ -/
def sigma_star : Language Sigma := fun _ => True
/-- The empty language contains no words -/
def L_empty : Language Sigma := fun _ => False
/-- The language containing only ε is not empty -/
def L_eps : Language Sigma := fun w => w = []

/-- Every language over Σ is a subset of Σ* -/
theorem sigma_star_subset : ∀ (L : Language Sigma), L ⊆ sigma_star := by
  intro L
  unfold sigma_star
  intro w w_mem
  simp only [Membership.mem]

/-- The empty language is a subset of any language. -/
theorem L_eps_subset : ∀ (L : Language Sigma), L_empty ⊆ L := by
  intro L
  unfold L_empty
  intro w w_mem
  simp only [Membership.mem] at w_mem

/-- A word w is contained in the language {ε} iff w = ε.-/
theorem L_eps_mem : w ∈ (@L_eps Sigma) ↔ w = [] := by
  unfold L_eps
  simp only [Membership.mem]

/-- Concatenation of Languages -/
instance : Mul (Language Sigma) where
  mul L1 L2 := fun w => ∃ u ∈ L1, ∃ v ∈ L2, w = u * v

/-- Concatenation of languages is associative: -/
theorem Language.mul_assoc (L₁ L₂ L₃ : Language Sigma) : (L₁ * L₂) * L₃ = L₁ * (L₂ * L₃) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    rcases u_mem with ⟨x, x_mem, y, y_mem, u_eq⟩
    exists x
    constructor
    . exact x_mem
    . exists y*v
      constructor
      . exists y
        constructor
        . exact y_mem
        . exists v
      . rw [← Word.mul_assoc]
        subst u
        exact w_eq
  . intro w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    rcases v_mem with ⟨x, x_mem, y, y_mem, v_eq⟩
    exists u*x
    constructor
    . exists u
      constructor
      . exact u_mem
      . exists x
    . exists y
      constructor
      . exact y_mem
      . subst v
        rw [Word.mul_assoc]
        exact w_eq

/--
Defining the complement of a set only makes sense if we know the "universe" of all elements.
For languages this is the set of all words over the alphabet Sigma, sigma_star.
So we can define the complement of a language as follows:
 -/
def Language.complement (L : Language Sigma) : Language Sigma :=
  sigma_star \ L

/-- The difference between two languages can be expressed with intersection and complement. -/
theorem diff_via_inter (L₁ L₂ : Language Sigma) : L₁ \ L₂ = L₁ ∩ L₂.complement := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Language.complement
    constructor
    . exact w_mem
    . constructor
      . simp only [sigma_star, Membership.mem]
      . exact w_nmem
  . intro w_mem
    rcases w_mem with ⟨w_1, w_2⟩
    unfold Language.complement at w_2
    constructor
    . exact w_1
    . rcases w_2 with ⟨ws, nw⟩
      exact nw

/-- For languages we can also execute concatenation multiple times and define this via Powers. -/
def Language.pow (L : Language Sigma) : Nat -> Language Sigma
| .zero => fun w => w = []
| .succ n => L * L.pow n

instance : NatPow (Language Sigma) where
  pow L n := L.pow n

/-- Finally we define the Kleene Star and notation for it. -/
def Language.kstar (L : Language Sigma) : Language Sigma := fun w => ∃ n, w ∈ L^n
postfix:max "*" => Language.kstar

/-- Definition of the "⁺" operator which is basically the Kleene Star without n=0. -/
def Language.plus (L : Language Sigma) : Language Sigma := fun w => ∃ n > 0, w ∈ L^n
postfix:max "⁺" => Language.plus

/-! the first four equalities from slide 35 follow directly from set theory. Just as an example: -/
theorem language_inter (L₁ L₂ : Language Sigma) : L₁ ∩ L₂ = L₂ ∩ L₁ := by
  simp only [Set.inter_commutative]

/-! for the remaining three identities refer to Set.lean. -/

/-! Using the complement of a language, we can also prove De Morgan's laws. -/

theorem de_morgan_rule1 (L₁ L₂ : Language Sigma) : (L₁ ∪ L₂).complement = L₁.complement ∩ L₂.complement := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Language.complement
    constructor
    . constructor
      . exact w_mem
      . simp [Membership.mem] at w_nmem
        intro f
        have contra : w ∈ L₁ ∪ L₂ := Or.inl f
        contradiction
    . constructor
      . exact w_mem
      . intro f
        have contra : w ∈ L₁ ∪ L₂ := Or.inr f
        contradiction
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem1, w_mem2⟩
    unfold Language.complement
    rcases w_mem1 with ⟨w_mem, w_nmem1⟩
    rcases w_mem2 with ⟨w_mem, w_nmem2⟩
    constructor
    . exact w_mem
    . intro f
      cases f with
      | inl w_mem1 =>
        contradiction
      | inr w_mem2 =>
        contradiction

/-- note that this theorem requires classical logic. -/
theorem de_morgan_rule2 (L₁ L₂ : Language Sigma) : (L₁ ∩ L₂).complement = L₁.complement ∪ L₂.complement := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Language.complement
    have w_nmem_inter : w ∉ L₁ ∨ w ∉ L₂ := by
      false_or_by_contra
      simp_all only [not_or, Classical.not_not];
      contradiction
    rcases w_nmem_inter with inl | inr
    . apply Or.inl
      constructor
      exact w_mem; exact inl
    . apply Or.inr
      constructor
      exact w_mem; exact inr
  . intro w_mem
    rcases w_mem with w_mem1 | w_mem2
    rcases w_mem1 with ⟨w_mem1, w_nmem1⟩
    . unfold Language.complement
      constructor
      . exact w_mem1
      . intro f
        rcases f with ⟨l, r⟩
        contradiction
    rcases w_mem2 with ⟨w_mem2, w_nmem2⟩
    . unfold Language.complement
      constructor
      . exact w_mem2
      . intro f
        rcases f with ⟨l, r⟩
        contradiction

/-- We can also prove that the complement of the complement of a language L is again L (which also requires classical logic). -/
theorem double_complement (L : Language Sigma) : (L.complement).complement = L := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    unfold Language.complement at w_mem
    rcases w_mem with ⟨w_mem, w_nmem⟩
    unfold Not at w_nmem
    have not_w_nmem : w ∉ L → False := by
      intro w_nmem_L
      have w_nmem_c : w ∈ sigma_star \ L := by
        constructor
        . exact w_mem
        . exact w_nmem_L
      apply w_nmem; exact w_nmem_c
    simp_all only [imp_false, Classical.not_not]
  . intro w_mem
    unfold Language.complement
    constructor
    . unfold sigma_star
      simp only [Membership.mem]
    . intro f
      rcases f with ⟨w_mem_s, w_nmem⟩
      contradiction

/-- This theorem will come in handy for many proofs. Although it might seem trivial, it does not immediately follow from the definition. -/
theorem pow_as_concat (L : Language Sigma) : n > 0 → L^n = L * L^(n-1) := by
  intro gt
  apply Set.ext
  intro y
  constructor
  . intro y_mem
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      exact y_mem
  . intro y_mem
    rcases y_mem with ⟨p, p_mem, q, q_mem, y_eq⟩
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      exists p
      constructor
      . exact p_mem
      . exists q


/-!
In some cases, it makes sense to think about the kleene star of some language L as the language
containing words consisting of a list of words from L. We can prove that this is equivalent to our original definition.
-/

/--
We first show a stronger result: for any word from L^n, we can find a corresponding list of length n.
-/
theorem Language.mem_pow (L : Language Sigma) (w : Word Sigma) : w ∈ L^n ↔ ∃ l : (List (Word Sigma)), w = l.flatten ∧ l.length = n ∧ (∀ u ∈ l, u ∈ L) := by
  constructor
  intro w_mem
  . induction n generalizing w with
    | zero =>
      exists []
      constructor
      . rw [List.flatten_nil]; exact w_mem
      . simp only [List.length_nil, List.not_mem_nil, false_implies, implies_true, and_self]
    | succ n ih =>
      rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
      rcases ih x x_mem with ⟨l_x, x_eq, l_x_length, x_mem⟩
      exists v :: l_x
      constructor
      . rw [List.flatten_cons, ← x_eq]; exact w_eq
      constructor
      . rw [List.length_cons, l_x_length]
      . intro u u_mem
        rw [List.mem_cons] at u_mem
        cases u_mem with
        | inl u_mem => rw [u_mem]; exact v_mem
        | inr u_mem => apply x_mem; exact u_mem
  . rintro ⟨l, w_eq, w_l, u_mem⟩
    induction l generalizing n w with
    | nil =>
      rw [List.flatten_nil] at w_eq
      rw [List.length_nil] at w_l
      rw [w_eq, ← w_l]
      rfl
    | cons v l lh =>
      have v_mem : v ∈ L := by
        apply u_mem
        simp
      have gtz : n > 0 := by
        rw [List.length_cons] at w_l
        rw [← w_l]; simp
      rw [pow_as_concat _ gtz]
      exists v
      constructor
      . exact v_mem
      . exists l.flatten
        constructor
        . apply lh
          . rfl
          . rw [List.length_cons] at w_l; rw [← w_l]; simp
          . intro u u_mem'; apply u_mem; simp [u_mem']
        . exact w_eq

/--
Since the kstar operation is defined via powers, we can now use the previous result and ignore the length of the list:
If a word is in L* then it must be in some power of L. Then we can obtain the list from Language.mem_pow.
For the other direction (when we have a list of words from L and want to show that the flattened list is contained in L*),
we use the list's length as the exponent n required for membership in L* and then apply mem_pow again.
 -/
theorem Language.mem_kstar (L : Language Sigma) (w : Word Sigma) : w ∈ L* ↔ ∃ l : (List (Word Sigma)), w = l.flatten ∧ (∀ u ∈ l, u ∈ L) := by
    constructor
    . intro w_mem
      rcases w_mem with ⟨n, w_mem⟩
      rw [Language.mem_pow] at w_mem
      rcases w_mem with ⟨l, w_eq, _, u_mem⟩
      exists l
    . intro hw
      rcases hw with ⟨l, w_eq, u_mem⟩
      exists l.length
      rw [Language.mem_pow]
      exists l

/-- every power of a language L is a subset of L*. -/
theorem kstar_subset (L : Language Sigma) : ∀ (n : Nat), L^n ⊆ L* := by
  intro n w w_mem
  cases n with
  | zero =>
    exists 0
  | succ n =>
    exists n+1

/-- Another example for something seemingly obvious that needs to be proven explicitly in order to be used in theorems. -/
theorem first_power (L : Language Sigma) : L^1 = L := by
    apply Set.ext
    intro w
    constructor
    . intro w_mem
      rcases w_mem with ⟨v, v_mem, u, u_mem, w_eq⟩
      unfold Language.pow at u_mem
      rcases u_mem
      rw [epsilon_concat] at w_eq
      subst w_eq
      exact v_mem
    . intro w_mem
      exists w
      constructor
      . exact w_mem
      . exists []
        constructor
        . unfold Language.pow
          simp [Membership.mem]
        . symm
          apply epsilon_concat

theorem mul_eq_append (u v : Word Sigma) : u * v = u++v := by rfl

/-- Product rule for exponents: when concatenating powers of a language we can add the exponents as we do when multiplying numbers. -/
theorem add_exp (L : Language Sigma) (m n : Nat) : (L^n) * L^m = L^(n+m) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, u, u_mem, w_eq⟩
    rw [Language.mem_pow] at v_mem u_mem
    rcases v_mem with ⟨l_v, v_eq, v_length, l_v_mem⟩
    rcases u_mem with ⟨l_u, u_eq, u_length, l_u_mem⟩
    rw [Language.mem_pow]
    exists l_v*l_u
    constructor
    . rw [Word.mul_eq]
      subst w v u
      rw [List.flatten_append]
      rfl
    . constructor
      . rw [Word.mul_eq]
        rw [List.length_append]
        subst v_length u_length
        rfl
      . intro x x_mem
        rw [Word.mul_eq] at x_mem
        have x_mem_l : ∀ (u : Word Sigma), u ∈ l_v++l_u → u ∈ L := by
          intro y y_mem
          rw [List.mem_append] at y_mem
          rcases y_mem with inl | inr
          . apply l_v_mem; exact inl
          . apply l_u_mem; exact inr
        apply x_mem_l
        exact x_mem
  . intro w_mem
    rw [Language.mem_pow] at w_mem
    rcases w_mem with ⟨l, l_eq, l_len, b⟩
    exists (l.take n).flatten
    constructor
    . rw [Language.mem_pow]
      exists l.take n
      constructor
      . rfl
      . constructor
        . simp_all
        . intro z z_mem
          have z_mem_l : z ∈ l := by apply List.mem_of_mem_take z_mem
          apply b z z_mem_l
    . exists (l.extract n).flatten
      constructor
      . rw [Language.mem_pow]
        exists l.extract n
        constructor
        . rfl
        . constructor
          . simp_all
          . intro z z_mem
            have z_mem_l : z ∈ l := by
              simp only [List.extract_eq_drop_take] at z_mem
              have mem_drop : z ∈ (List.drop n l) := List.mem_of_mem_take z_mem
              apply List.mem_of_mem_drop mem_drop
            apply b z z_mem_l
      . subst w
        rw [Word.mul_eq]
        rw [← List.flatten_append]
        apply congrArg
        simp only [List.extract_eq_drop_take]
        rw [← List.length_drop]
        conv => right; right; rw [List.take_length]
        rw [List.take_append_drop]

/-- concatenation of languages is distributive over union (right side) -/
theorem distr_concat_union_l (L₁ L₂ L₃ : Language Sigma) : (L₁ ∪ L₂) * L₃ = (L₁ * L₃) ∪ (L₂ * L₃) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    cases u_mem with
    | inl u_mem =>
      apply Or.inl
      exists u
      constructor
      . exact u_mem
      . exists v
    | inr u_mem =>
      apply Or.inr
      exists u
      constructor
      . exact u_mem
      . exists v
  . intro w_mem
    cases w_mem with
    | inl w_mem =>
      rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
      exists u
      constructor
      . apply Or.inl
        exact u_mem
      . exists v
    | inr w_mem =>
      rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
      exists u
      constructor
      . apply Or.inr
        exact u_mem
      . exists v

/-- concatenation of languages is distributive over union (left side side) -/
theorem distr_concat_union_r (L₁ L₂ L₃ : Language Sigma) : L₁ * (L₂ ∪ L₃) = (L₁ * L₂) ∪ (L₁ * L₃) := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
    cases x_mem with
    | inl x_mem =>
      apply Or.inl
      exists v
      constructor
      . exact v_mem
      . exists x
    | inr x_mem =>
      apply Or.inr
      exists v
      constructor
      exact v_mem
      exists x
  . intro w_mem
    cases w_mem with
    | inl w_mem =>
      rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
      exists v
      constructor
      . exact v_mem
      . exists x
        constructor
        . apply Or.inl x_mem
        . exact w_eq
    | inr w_mem =>
      rcases w_mem with ⟨v, v_mem, x, x_mem, w_eq⟩
      exists v
      constructor
      . exact v_mem
      . exists x
        constructor
        . apply Or.inr
          exact x_mem
        . exact w_eq

/--!
The language containing only ε is the identity element for concatenation of languages.
Since concatenation is not a commutative operation, we need a proof for {ε} * L = L and for L * {ε} = L.
-/

theorem L_eps_mul : ∀ (L : Language Sigma), L ≠ L_empty → L_eps * L = L := by
  intro L ln
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, u, u_mem, _, _⟩
    unfold L_eps at v_mem
    cases v_mem
    rw [concat_epsilon]
    exact u_mem
  . intro w_mem
    unfold L_eps
    exists []
    constructor
    . simp only [Membership.mem]
    . exists w

theorem mul_L_eps : ∀ (L : Language Sigma), L ≠ L_empty → L * L_eps = L := by
  intro L ln
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨v, v_mem, u, u_mem, _, _⟩
    unfold L_eps at u_mem
    cases u_mem
    rw [epsilon_concat]
    exact v_mem
  . intro w_mem
    unfold L_eps
    exists w
    constructor
    . exact w_mem
    . exists []
      rw [epsilon_concat]
      simp only [Membership.mem, true_and]

/-- The empty language ∅ is an annihilating element for concatenation. (left) -/
theorem empty_mul : ∀ (L : Language Sigma), L_empty * L = L_empty := by
  intro L
  unfold L_empty
  apply funext
  intro w
  simp
  intro h
  rcases h with ⟨u, u_mem, v, v_mem, h⟩
  contradiction

/-- The empty language ∅ is an annihilating element for concatenation. (right) -/
theorem mul_empty : ∀ (L : Language Sigma), L * L_empty = L_empty := by
  intro L
  unfold L_empty
  apply funext
  intro w
  simp
  intro h
  rcases h with ⟨u, u_mem, v, v_mem, h⟩
  contradiction

/-- The kleene closure of a language is the same as applying the plus operator and adding the empty word. -/
theorem kstar_eq_plus_union_eps (L : Language Sigma) : L* = L⁺ ∪ L_eps := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨n, w_mem⟩
    cases n with
    | zero =>
      apply Or.inr
      rcases w_mem
      simp only [Membership.mem, L_eps]
    | succ n =>
      apply Or.inl
      exists n+1
      constructor
      . simp only [gt_iff_lt, Nat.zero_lt_succ]
      . exact w_mem
  . intro w_mem
    rcases w_mem with ⟨n, gtz, w_mem⟩
    . exists n
    . exists 0

/-- All powers of ∅ (except ∅⁰) are ∅. -/
theorem succ_pow_empty : ∀ n, n > 0 → Language.pow L_empty n = @L_empty Sigma := by
  intro n n₁
  unfold Language.pow
  cases n₁ with
  | refl =>
    simp
    unfold L_empty
    apply empty_mul
  | step =>
    simp
    apply empty_mul

/--
Using the two previous results first_power and add_exp, we can show that when writing the nth power of a language L
as the concatenation of L with L^(-1) the order does not matter.
-/
theorem pow_as_concat_comm (L : Language Sigma) (n : Nat) : L * L^(n-1) = (L^(n-1)) * L := by
  rw (occs := [1, 4]) [← first_power L]
  rw [add_exp L 1 (n-1)]
  rw [add_exp L (n-1) 1, Nat.add_comm]

theorem kstar_plus (L : Language Sigma) : L⁺ = L* * L := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨n, gt, w_mem⟩
    rw [pow_as_concat] at w_mem
    . rw [pow_as_concat_comm] at w_mem
      rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
      exists u
      constructor
      . unfold Language.kstar
        simp only [Membership.mem]
        exists (n-1)
      . exists v
    . exact gt
  . intro w_mem
    rcases w_mem with ⟨u, u_mem, v, v_mem, w_eq⟩
    rcases u_mem with ⟨n, u_mem⟩
    unfold Language.plus
    simp only [Membership.mem]
    exists (n+1)
    constructor
    . simp only [gt_iff_lt, Nat.zero_lt_succ]
    . rw [← add_exp L, first_power]
      exists u
      constructor
      . exact u_mem
      . exists v

/-- Removing the empty word from a language L does not change L*. -/
theorem kstar_eq_L_minus_eps [BEq Sigma] (L : Language Sigma) : L* = (L\L_eps)* := by
  apply Set.ext
  intro w

  have aux : w ∈ (L \ L_eps)* ↔ ∃ (l : List (Word Sigma)), w = (l.removeAll [[]]).flatten ∧ ∀ u, u ∈ l → u ∈ L := by
    constructor
    . intro w_mem
      rw [Language.mem_kstar] at w_mem
      rcases w_mem with ⟨l, w_eq, l_mem⟩
      exists l
      constructor
      . rw [List.removeAll_nil_flatten]
        exact w_eq
      . intro u
        have aux2 : u ∈ L \ L_eps → u ∈ L := by
          intro u_mem
          rcases u_mem with ⟨u_mem, _⟩
          exact u_mem
        have aux3 := l_mem u
        intro u_mem
        grind
    . intro h
      rcases h with ⟨l, w_eq, l_mem⟩
      rw [Language.mem_kstar]
      exists l.removeAll [[]]
      constructor
      . exact w_eq
      . intro u u_mem
        constructor
        . grind
        . rw [L_eps_mem]
          grind

  constructor
  . intro w_mem
    rw [aux]
    rw [Language.mem_kstar] at w_mem
    rcases w_mem with ⟨l, w_eq, l_mem⟩
    exists l
    constructor
    . rw [List.removeAll_nil_flatten]
      exact w_eq
    . exact l_mem
  . intro w_mem
    rw [aux] at w_mem
    rcases w_mem with ⟨l, w_eq, l_mem⟩
    rw [Language.mem_kstar]
    exists l
    constructor
    . rw [← List.removeAll_nil_flatten]
      exact w_eq
    . exact l_mem
