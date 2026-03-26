import FormaleSystemeInLean.Lecture3

/-!
This file covers selected topics from lecture 4:
- definition of an NFA, the run of an NFA and the language accepted by an NFA
- how to turn an NFA into a DFA using the powerset construction
- proof that the languages of an NFA and the resulting powerset DFA are equal
- how to turn a total DFA into an NFA and the proof that the accepted language stays the same

Slides are available at: https://iccl.inf.tu-dresden.de/w/images/c/c9/FS2025-Vorlesung-04-print.pdf
-/

/--
An NFA (Nondeterministic Finite Automaton) is a structure depending on two types Q and Sigma both of which are finite.
The transition function δ now has potentially many different values so it maps a state and a symbol to a list of states. That means when reading a symbol σ in a state q the NFA
will end up in one of the states from the list. The reason why this definition uses a list instead of a set is that defining finite sets is not as easy as one might think.
A list is always finite so it works just as well.
-/
structure NFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q → Sigma → List Q
  Q0 : List Q
  F : List Q

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma]

/--
Transition function for words mapping a word w ∈ Σ* and a list of states R to another list of states.
- w = ε: the NFA remains in one of the states from R so δ_word(R,ε) = R
- w = av: δ_word(R,av) = δ_word(R',v) where R' is the list of states reachable from some state R with a
-/
def NFA.δ_word (nfa : NFA Q Sigma) (R : List Q) : (Word Sigma) → List Q
  | .nil => R
  | .cons a v => nfa.δ_word (R.flatMap (nfa.δ · a)) v


/--
A run of an NFA on a word w is a sequence of states. We can express this using an inductive definition:
- For every state q, the sequence q is a run on the empty word ε.
- If an NFA has a run q2...qf on v and q2 is reachable with a from q1, then q1...qf is a run on av.
-/
inductive NFA.Run (nfa : NFA Q Sigma) : Q -> Q -> Word Sigma -> Type _
| self (q : Q) : nfa.Run q q []
| step {q1 q2 qf : Q} {a : Sigma} {v : Word Sigma} (r : nfa.Run q2 qf v) (q2_mem : q2 ∈ nfa.δ q1 a) : nfa.Run q1 qf (a :: v)

/-- A run beginning with a state from Q0 -/
def NFA.Run.from_start {nfa : NFA Q Sigma} (_ : nfa.Run q0 q w) : Prop := q0 ∈ nfa.Q0

/-- An accepting run for a word w ends with a final state. -/
def NFA.Run.accepts {nfa : NFA Q Sigma} (_ : nfa.Run q qf w) : Prop := qf ∈ nfa.F

/-- The language of an NFA consists of all words w that have an accepting run beginning with some state q0 ∈ Q0 and ending in a state qf ∈ F. -/
def NFA.Language (nfa : NFA Q Sigma) : Language Sigma :=
  fun w => ∃ (q0 qf : Q) (r : nfa.Run q0 qf w), r.from_start ∧ r.accepts

/-!
In lecture 3 we defined the language of a DFA M as the set of words w satisfying δ_word(q0,w) ∈ F.
We can do something similar for NFAs (using δ_word with a the list of starting states as an input)
and prove that this is equal to the previous definition using the run of an NFA.
The corresponding proof in lecture 4 can be found starting from slide 18 - feel free to compare it to the Lean version!
-/
section languageDefEq

  /-- Given a set of states R, the states reachable from a single state q ∈ R are a subset of the states reachable from R. -/
  theorem δ_subset_δ_word (nfa : NFA Q Sigma) (q : Q) (R : List Q) (a : Sigma) : q ∈ R → nfa.δ q a ⊆ nfa.δ_word R [a] := by
    intro q_mem q' q'_memd
    unfold NFA.δ_word
    have aux : q' ∈ R.flatMap (fun x => nfa.δ x a) := by
      simp only [List.mem_flatMap]
      exists q
    simp only [NFA.δ_word]
    exact aux

  /-- For every run q1...qn on a word w with q1 ∈ R, qn ∈ δ_word(R, w). -/
  theorem run_imp_mem_δ (nfa : NFA Q Sigma) (q1 qn : Q) (R : List Q) (w : Word Sigma) : nfa.Run q1 qn w → q1 ∈ R → qn ∈ nfa.δ_word R w := by
    intro r q1_mem
    induction r generalizing R with
    | self q =>
      trivial
    | @step qa qb qc a v r qb_mem hr =>
      have aux : qc ∈ nfa.δ_word (nfa.δ qa a) v := hr (nfa.δ qa a) qb_mem
      unfold NFA.δ_word
      have aux2 : ∀ q, q ∈ nfa.δ qa a → q ∈ (List.flatMap (fun x => nfa.δ x a) R) := by
        intro q q_mem
        rw [List.mem_flatMap]
        exists qa
      grind

  /-- Given a set of states R and a state qn ∈ δ(R, w) we can also construct a run for w starting with a state in R. -/
  theorem run_from_δ_word (nfa : NFA Q Sigma) (qn : Q) (R : List Q) (w : Word Sigma) : qn ∈ nfa.δ_word R w → ∃ (q1 : Q) (_ : nfa.Run q1 qn w), q1 ∈ R := by
    intro qn_mem
    induction w generalizing R with
    | nil =>
      simp only [Membership.mem] at qn_mem
      unfold NFA.δ_word at qn_mem
      exists qn
      exists NFA.Run.self qn
    | cons a v ih =>
      simp only [Membership.mem, NFA.δ_word] at qn_mem
      have aux := ih (List.flatMap (fun x => nfa.δ x a) R) qn_mem
      rcases aux with ⟨q, r', q_mem⟩
      have aux2 : ∃ q', q' ∈ R ∧ q ∈ nfa.δ q' a := by
        rw [List.mem_flatMap] at q_mem
        rcases q_mem with ⟨q', q'_mem, q_mem⟩
        exists q'
      rcases aux2 with ⟨q', q'_mem, q'_memd⟩
      exists q'
      exists NFA.Run.step r' q'_memd

  /--
  Using the two previous results, we can show that the two different definitions for the language accepted by an NFA are equal:
  An NFA has an accepting run q0...qf on a word w iff the set of states reachable from q0 ∈ Q0 contains a qf ∈ F.
  -/
  theorem acc_run_iff_δ_word_contains_final (nfa : NFA Q Sigma) (w : Word Sigma) : w ∈ nfa.Language ↔ ∃ q ∈ nfa.δ_word nfa.Q0 w, q ∈ nfa.F := by
    constructor
    . intro w_mem
      rcases w_mem with ⟨q0, qf, r, r_s, r_acc⟩
      unfold NFA.Run.accepts at r_acc
      unfold NFA.Run.from_start at r_s
      have qf_mem : qf ∈ nfa.δ_word nfa.Q0 w := run_imp_mem_δ nfa q0 qf nfa.Q0 w r r_s
      exists qf
    . intro h
      unfold NFA.Language
      simp only [Membership.mem]
      rcases h with ⟨qf, q_memd, q_memf⟩
      have run := run_from_δ_word nfa qf nfa.Q0 w q_memd
      rcases run with ⟨q0, r, q0_mem⟩
      exists q0, qf, r

end languageDefEq

/-- Every DFA can be turned into an NFA. We just need to map values of δ to singleton lists or the empty list and q0 to a singleton list as well. -/
def DFA.to_NFA (M : DFA Q Sigma) : NFA Q Sigma where
  δ := fun q a =>
    match M.δ q a with
    | none => []
    | some q => [q]
  Q0 := [M.q0]
  F := M.F

/-- Every total DFA can be turned into an NFA by mapping states to singleton lists. -/
def TotalDFA.to_NFA (M : TotalDFA Q Sigma) : NFA Q Sigma where
  δ := fun q a => [M.δ q a]
  Q0 := [M.q0]
  F := M.F

/-!
The following section deals with the conversion from DFA to NFA.
We proceed in a similar manner as we did for the proof of totalDFA_eq_DFA in lecture3 by first showing that the transition functions of M and M.to_NFA are (almost) equal
and then using this to prove the equality of M.Language and M.to_NFA.Language.
-/
section toNFA

  theorem totalDFA_NFA_δ_eq (M : TotalDFA Q Sigma) (a : Sigma) (q : Q) : q' ∈ M.to_NFA.δ q a ↔ q' = M.δ q a := by
    simp only [TotalDFA.to_NFA, List.mem_singleton]

  theorem totalDFA_NFA_δ_word_eq (M : TotalDFA Q Sigma) (w : Word Sigma) (q : Q) : q' ∈ M.to_NFA.δ_word [q] w ↔ M.δ_word q w = q' := by
    induction w generalizing q with
    | nil =>
      simp only [NFA.δ_word, TotalDFA.δ_word]
      constructor
      . intro eq
        rw [List.mem_singleton] at eq
        symm
        rw [eq]
      . intro eq
        rw [List.mem_singleton]
        symm
        rw [eq]
    | cons a v ih =>
      simp only [NFA.δ_word, TotalDFA.δ_word, Membership.mem]
      have aux := ih (M.δ q a)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact aux

  theorem totalDFA_NFA_lang_eq (M : TotalDFA Q Sigma) : M.to_NFA.Language = M.Language := by
    apply Set.ext
    intro w
    rw [acc_run_iff_δ_word_contains_final]
    unfold TotalDFA.Language
    have Q0_eq : M.to_NFA.Q0 = [M.q0] := by
      simp only [TotalDFA.to_NFA]
    constructor
    . intro hq
      rcases hq with ⟨qf, qf_memd, qf_memf⟩
      simp only [Membership.mem]
      simp only [TotalDFA.to_NFA] at qf_memf
      cases w with
      | nil =>
        simp only [NFA.δ_word] at qf_memd
        simp only [TotalDFA.δ_word]
        rw [Q0_eq, List.mem_singleton] at qf_memd
        rw [← qf_memd]
        exact qf_memf
      | cons a v =>
        rw [Q0_eq, totalDFA_NFA_δ_word_eq] at qf_memd
        rw [qf_memd]
        exact qf_memf
    . intro w_mem
      simp only [Membership.mem] at w_mem
      cases w with
      | nil =>
        simp only [TotalDFA.δ_word] at w_mem
        exists M.q0
        constructor
        . rw [Q0_eq]
          simp only [NFA.δ_word, List.mem_singleton]
        . simp only [Membership.mem]
          exact w_mem
      | cons a v =>
        simp only [TotalDFA.δ_word] at w_mem
        exists (M.δ_word (M.δ M.q0 a) v)
        constructor
        . rw [Q0_eq, totalDFA_NFA_δ_word_eq]
          rfl
        . simp only [TotalDFA.to_NFA]
          exact w_mem

end toNFA

/-!
Every NFA can be turned into a total DFA using the powerset construction.
Since we defined the states Q as some type with a Fintype instance, computing the "powerset" of Q is a bit tricky.
A Fintype is simply a type with finitely many elements. This can be expressed by requiring the existence of a list with all elements of Q.
The Powertype of Q is the list of all possible subsets of this list. We use subsets instead of lists because the powertype needs to be finite.
If you are interested in the details have a look at Powertype.lean. It is not required to understand the definitions and proofs concerning Powertype
to understand the section toDFA.
-/

section toDFA

def powerset_δ (M : NFA Q Sigma) [DecidableEq Q] : Powertype Q -> Sigma -> Powertype Q :=
  Quotient.lift
    (fun R a => Finset.mk (R.flatMap (fun q => M.δ q a)))
    (by
      intro X Y eq
      simp only
      funext a
      simp only [HasEquiv.Equiv, Setoid.r, Finset.eq] at eq
      apply Quot.sound
      simp only [Setoid.r, Finset.eq]
      intro s
      rw [List.mem_flatMap]
      constructor
      . intro h
        rcases h with ⟨t, t_mem, s_mem⟩
        rw [List.mem_flatMap]
        exists t
        constructor
        . apply (eq t).mp; exact t_mem
        . exact s_mem
      . rw [List.mem_flatMap]
        intro h
        rcases h with ⟨t, t_mem, s_mem⟩
        exists t
        constructor
        . apply (eq t).mpr; exact t_mem
        . exact s_mem
        )

  def NFA.to_TotalDFA (M : NFA Q Sigma) [DecidableEq Q] : TotalDFA (Powertype Q) Sigma where
  δ := fun R a => powerset_δ M R a
  q0 := Finset.mk M.Q0
  F := Fintype.elems.filter (fun x => (Finset.mk M.F) ∩ x != ∅)

  theorem mem_powerset_δ_iff (M : NFA Q Sigma) (a : Sigma) (R : List Q) (q : Q) [DecidableEq Q] :
    q ∈ M.δ_word R [a] ↔ q ∈ M.to_TotalDFA.δ (Finset.mk R) a := by rfl

  theorem δ_NFA_eq_δ_TotalDFA (M : NFA Q Sigma) (a : Sigma) (R : List Q) [DecidableEq Q] : M.to_TotalDFA.δ (Finset.mk R) a = Finset.mk (M.δ_word R [a]) := by
    apply Finset.ext
    intro q
    rw [← mem_list_iff_mem_mk]
    simp only [mem_powerset_δ_iff]

  theorem δ_word_eq_DFA_NFA (M : NFA Q Sigma) (w : Word Sigma) (R : List Q) [DecidableEq Q] : ∀ q, q ∈ M.δ_word R w ↔ q ∈ M.to_TotalDFA.δ_word (Finset.mk R) w := by
  intro q
  induction w generalizing q R with
  | nil =>
    simp only [NFA.δ_word, TotalDFA.δ_word, mem_list_iff_mem_mk]
  | cons a v ih =>
    simp only [NFA.δ_word]
    have aux := ih (List.flatMap (fun x => M.δ x a) R)
    simp only [TotalDFA.δ_word]
    have aux2 := mem_powerset_δ_iff M a R q
    rw [δ_NFA_eq_δ_TotalDFA]
    simp only [NFA.δ_word]
    grind

  theorem NFA_totalDFA_lang_eq (M : NFA Q Sigma) [DecidableEq Q] : M.to_TotalDFA.Language = M.Language := by
    apply Set.ext
    intro w
    unfold TotalDFA.Language
    rw [acc_run_iff_δ_word_contains_final]
    have q0_eq : M.to_TotalDFA.q0 = Finset.mk M.Q0 := rfl
    have F_eq : M.to_TotalDFA.F = Fintype.elems.filter (fun x => (Finset.mk M.F) ∩ x != ∅) := rfl
    have := δ_word_eq_DFA_NFA M w M.Q0
    rw [Set.mem_iff, F_eq, List.mem_filter, q0_eq]

    constructor
    . rintro ⟨_, h⟩
      have exists_mem := Finset.ne_empty_contains_element _ h
      rcases exists_mem with ⟨q0, q0_mem⟩
      rw [Finset.mem_inter] at q0_mem
      rcases q0_mem with ⟨mem_f, mem_start⟩
      exists q0
      constructor
      . rw [this]; exact mem_start
      . rw [mem_list_iff_mem_mk]; exact mem_f

    . rintro ⟨q, q_mem_start, q_mem_f⟩
      constructor
      . apply Fintype.complete
      . simp only [bne_iff_ne]
        rw [this] at q_mem_start
        intro contra
        have : q ∈ Finset.mk M.F ∩ M.to_TotalDFA.δ_word (Finset.mk M.Q0) w := by
          rw [Finset.mem_inter]
          constructor
          . rw [← mem_list_iff_mem_mk]; exact q_mem_f
          . exact q_mem_start
        rw [contra] at this
        simp [EmptyCollection.emptyCollection, ← mem_list_iff_mem_mk] at this

end toDFA
