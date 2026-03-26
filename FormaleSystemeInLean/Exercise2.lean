import FormaleSystemeInLean.Lecture4

/-!
This file contains the formalisation of exercise 2.3 c and d which deals with simulations between NFAs.
The exercise sheet is available at https://iccl.inf.tu-dresden.de/w/images/2/28/FS2025-Blatt-02.pdf.
-/
section Exercise3

  variable {Sigma : Type u} {Q1 : Type u1} {Q2 : Type u2} [Fintype Q1] [Fintype Q2] [Fintype Sigma]

  structure NFASimulation (nfa1 : NFA Q1 Sigma) (nfa2 : NFA Q2 Sigma) where
    rel : Set (Q1 × Q2)
    start : ∀ q01 ∈ nfa1.Q0, ∃ q02 ∈ nfa2.Q0, (q01, q02) ∈ rel
    step : ∀ {q1 : Q1} {q2 : Q2} {a : Sigma}, (q1, q2) ∈ rel -> ∀ q1' ∈ (nfa1.δ q1 a), ∃ q2' ∈ (nfa2.δ q2 a), (q1', q2') ∈ rel
    final : ∀ {q1 : Q1} {q2 : Q2}, (q1, q2) ∈ rel -> q1 ∈ nfa1.F -> q2 ∈ nfa2.F

  section d

    /--
    If there is a simulation between nfa1 and nfa2 then the language of nfa1 is a subset of the language of nfa2.
    -/
    theorem part_a {nfa1 : NFA Q1 Sigma} {nfa2 : NFA Q2 Sigma} (sim : NFASimulation nfa1 nfa2) : nfa1.Language ⊆ nfa2.Language := by
      have generalized_theorem : ∀ {q1 q1' : Q1} {q2 : Q2} {w : Word Sigma}, (q1, q2) ∈ sim.rel -> ∀ r1 : nfa1.Run q1 q1' w, ∃ q2' : Q2, (q1', q2') ∈ sim.rel ∧ ∃ r2 : nfa2.Run q2 q2' w, True := by
        intro q1 q1' q2 w q1_eq_q2 r1
        induction r1 generalizing q2 with
        | self q => exists q2; constructor; exact q1_eq_q2; exists (.self q2)
        | step r1 q2_mem ih =>
          rcases sim.step q1_eq_q2 _ q2_mem with ⟨_, q2'_mem, q1'_eq_q2'⟩
          specialize ih q1'_eq_q2'
          rcases ih with ⟨q2'', q2''_eq, r2, _⟩
          exists q2''
          constructor
          . exact q2''_eq
          . exists (.step r2 q2'_mem)

      intro w w_mem
      rcases w_mem with ⟨q01, qf1, r1, r1_start, r1_accept⟩
      rcases sim.start q01 r1_start with ⟨q02, r2_start, q01_eq_q02⟩
      exists q02
      rcases generalized_theorem q01_eq_q02 r1 with ⟨qf2, qf1_eq_qf2, r2, _⟩
      exists qf2, r2
      constructor
      . exact r2_start
      . exact sim.final qf1_eq_qf2 r1_accept


    /-!
    How about the other direction - does language inclusion also imply a simulation between the NFAs recognising the languages?
    We can show that this is not true by giving a counterexample.
    In order to define NFAs we first need Fintypes for Q and Sigma. We cannot just use strings because there are infinitely many of those.
    Instead we use a subtype of String defined by a list of strings (statesList and sigma).
    -/

    def statesList := ["q0", "q1", "q2"]
    def sigma := ['a', 'b']

    def Q := subtype_of_list statesList
    def ⅀ := subtype_of_list sigma

    deriving instance Fintype, DecidableEq for Q, ⅀

    /--
    Finally we can define the NFA 𝓜.
    -/
    def 𝓜 : NFA Q ⅀ where
      δ := fun q σ =>
        match q.val with
          | "q0" => match σ.val with
            | 'a' => [⟨"q2", by simp only [statesList]; grind⟩]
            | 'b' => [⟨"q1", by simp only [statesList]; grind⟩, ⟨"q2", by simp only [statesList]; grind⟩]
            | _ => []
          | "q1" => match σ.val with
            | 'b' => [⟨"q0", by simp only [statesList]; grind⟩, ⟨"q2", by simp only [statesList]; grind⟩]
            | _ => []
          | _ => []
      Q0 := [⟨"q0", by simp only [statesList]; grind⟩]
      F := [⟨"q2", by simp only [statesList]; grind⟩]

    /-!
    For our counterexample we will use 𝓜 and its powerset DFA 𝓜'. Their languages are equal but there is not simulation between 𝓜 and 𝓜'.
    Simulations are defined for NFAs so we convert 𝓜' back into an NFA 𝓜''.
    -/

    def 𝓜_total : TotalDFA (Powertype Q) ⅀ := 𝓜.to_TotalDFA
    def 𝓜_total' : NFA (Powertype Q) ⅀ := 𝓜_total.to_NFA

    theorem part_b : ∃ (nfa1 : NFA (Powertype Q) ⅀) (nfa2 : NFA Q ⅀), nfa1.Language ⊆ nfa2.Language ∧ ¬∃ (_ : NFASimulation nfa1 nfa2), True := by
      exists 𝓜_total', 𝓜
      constructor
      . intro w w_mem
        have lang_eq1 : 𝓜.to_TotalDFA.Language = 𝓜.Language := by
          apply NFA_totalDFA_lang_eq 𝓜
        have lang_eq2 : 𝓜_total.Language = 𝓜_total'.Language := by
          unfold 𝓜_total'
          symm
          apply totalDFA_NFA_lang_eq 𝓜_total
        unfold 𝓜_total' 𝓜_total at *
        rw [lang_eq2] at lang_eq1
        rw [← lang_eq1]
        exact w_mem
      . intro sim

        let q0 : Q := ⟨"q0", by simp only [statesList]; grind⟩
        let q1 : Q := ⟨"q1", by simp only [statesList]; grind⟩
        let q2 : Q := ⟨"q2", by simp only [statesList]; grind⟩
        let Q0 : Finset Q := Finset.mk [q0]
        let b : ⅀ := ⟨'b', by simp only [sigma]; grind⟩

        rcases sim with ⟨sim, _⟩
        rcases sim with ⟨sim, start, step, final⟩

        have q01_mem : Q0 ∈ 𝓜_total'.Q0 := by
          unfold Q0 q0 𝓜_total' TotalDFA.to_NFA 𝓜_total 𝓜 NFA.to_TotalDFA
          simp
        have q02_mem : q0 ∈ 𝓜.Q0 := by unfold q0 𝓜; simp
        have q02_eq : 𝓜.Q0 = [q0] := by unfold q0 𝓜; simp

        have start_mem : sim (Q0, q0) := by
          have aux := start Q0 q01_mem
          rcases aux with ⟨q02, q02_mem', mem_sim⟩
          rw [q02_eq, List.mem_singleton] at q02_mem'
          rw [q02_mem'] at mem_sim
          exact mem_sim

        have delta_q0_eq : 𝓜.δ q0 b = [q1, q2] := by unfold b q0 q1 q2; simp only [𝓜]

        have delta'_q0_eq : 𝓜_total'.δ Q0 b = [Finset.mk [q1, q2]] := by
          unfold 𝓜_total' TotalDFA.to_NFA
          simp only [List.cons.injEq, and_true]
          apply Finset.ext
          intro q
          unfold 𝓜_total Q0
          rw [δ_NFA_eq_δ_TotalDFA, ← mem_list_iff_mem_mk, ← mem_list_iff_mem_mk]
          unfold NFA.δ_word
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil]
          rw [delta_q0_eq]
          unfold NFA.δ_word
          grind

        have mem_step : sim (Finset.mk [q1,q2], q2) := by
          have aux := step (a := b) start_mem
          have mem_delta : Finset.mk [q1,q2] ∈ 𝓜_total'.δ Q0 b := by grind
          specialize aux (Finset.mk [q1,q2])
          have aux2 := aux mem_delta
          rcases aux2 with ⟨r, r_mem, mem_sim⟩
          rw [delta_q0_eq] at r_mem

          have nmem_q1 : ¬sim (Finset.mk [q1,q2], q1) := by
            intro contra
            have mem_F : Finset.mk [q1,q2] ∈ 𝓜_total'.F := by
              simp only [q1, q2, 𝓜_total', TotalDFA.to_NFA, 𝓜_total, NFA.to_TotalDFA, List.mem_filter, Fintype.elems, List.mem_map]
              constructor
              . exists [q1, q2]
                constructor
                . apply powerlist
                  simp
                  have : statesList.attach = Fintype.elems (α := Q) := rfl
                  rw [← this]
                  simp [statesList]
                . unfold q1 q2
                  simp
              . unfold 𝓜
                simp
                intro contra'
                let X := Finset.mk [q2]
                let Y := Finset.mk [q1, q2]
                have inter : X ∩ Y = Finset.mk [q2] := by
                  apply Finset.ext
                  intro t
                  constructor
                  . intro t_mem
                    rw [Finset.mem_inter] at t_mem
                    rcases t_mem with ⟨l, r⟩
                    simp only [X, Y, Membership.mem] at *
                    grind
                  . intro t_mem
                    rw [← mem_list_iff_mem_mk] at t_mem
                    rw [Finset.mem_inter]
                    constructor
                    . unfold X; rw [← mem_list_iff_mem_mk]; exact t_mem
                    . unfold Y; rw [← mem_list_iff_mem_mk]; grind
                simp only [X, Y] at inter
                rw [contra'] at inter
                contradiction

            have aux3 := final contra mem_F
            simp only [𝓜, List.mem_singleton] at aux3
            grind

          have r_neq : ¬r = q1 := by
            intro contra
            rw [contra] at mem_sim
            contradiction
          have r_eq : r = q2 := by
            simp at r_mem
            grind

          rw [r_eq] at mem_sim
          exact mem_sim

        have delta_undef : ∀ (a : ⅀), ¬∃ r, r ∈ 𝓜.δ q2 a := by
          intro a contra
          rcases contra with ⟨r, r_mem⟩
          simp only [q2, 𝓜] at r_mem
          simp_all

        have delta'_q1_q2 : Finset.mk [q0, q2] ∈ 𝓜_total'.δ (Finset.mk [q1, q2]) b := by
          unfold 𝓜_total'
          rw [totalDFA_NFA_δ_eq]
          unfold 𝓜_total
          rw [δ_NFA_eq_δ_TotalDFA]
          apply congrArg
          unfold NFA.δ_word
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          have δ_q1 : 𝓜.δ q1 b = [q0, q2] := by simp only [q1, q2, q0, b, 𝓜]
          have δ_q2 : 𝓜.δ q2 b = [] := by simp only [𝓜]; grind
          rw [δ_q1, δ_q2]
          rfl

        have mem_step2 := step (a := b) mem_step (Finset.mk [q0, q2]) delta'_q1_q2
        rcases mem_step2 with ⟨r, r_mem, mem_sim⟩
        specialize delta_undef b
        contradiction

  end d

end Exercise3
