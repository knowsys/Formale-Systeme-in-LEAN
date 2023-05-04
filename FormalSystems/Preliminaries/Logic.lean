
theorem Or.distrib_and : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
  (fun hpqr : p ∨ (q ∧ r) =>
    Or.elim hpqr
    (fun hp:p => show (p ∨ q) ∧ (p ∨ r) from ⟨(Or.intro_left q hp), (Or.intro_left r hp)⟩)
    (fun hqr: (q ∧ r) => show (p ∨ q) ∧ (p ∨ r) from ⟨(Or.intro_right p hqr.left), (Or.intro_right p hqr.right)⟩))
  (fun hpqpr: (p ∨ q) ∧ (p ∨ r) => 
    have hpq := hpqpr.left
    have hpr := hpqpr.right
    Or.elim hpq
    (fun hp:p => show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
    (fun hq:q =>
    Or.elim hpr
    (fun hp:p => show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
    (fun hr:r => show p ∨ (q ∧ r) from Or.intro_right p ⟨hq, hr⟩))
 )

theorem And.assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := by
  constructor
  case mp => intro ⟨⟨ha, hb⟩, hc⟩; exact ⟨ha, ⟨hb, hc⟩⟩
  case mpr => intro ⟨ha, ⟨hb, hc⟩⟩; exact ⟨⟨ha, hb⟩, hc⟩

theorem And.distrib_or : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := by
  constructor
  . intro ⟨ha, hor⟩
    cases hor with
    | inl hl => exact Or.inl ⟨ha, hl⟩
    | inr hr => exact Or.inr ⟨ha, hr⟩
  . intro h
    match h with
    | Or.inl ⟨ha, hb⟩ => exact ⟨ha, Or.inl hb⟩
    | Or.inr ⟨ha, hc⟩ => exact ⟨ha, Or.inr hc⟩

theorem Or.morgan : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (fun hnpq: ¬(p ∨ q) => 
    ⟨fun hp:p => hnpq (Or.intro_left q hp), fun hq:q => hnpq (Or.intro_right p hq)⟩)
  (fun hnpq : ¬p ∧ ¬q =>
    fun hpq : (p ∨ q) =>
      Or.elim hpq
      (fun hp:p => hnpq.left hp)
      (fun hq:q => hnpq.right hq))

theorem And.morgan : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  apply Iff.intro
  . intro h
    apply Classical.byCases
    . intro hp
      apply Classical.byCases
      . intro hq
        apply False.elim
        exact h ⟨ hp, hq ⟩
      . exact Or.inr
    . exact Or.inl
  . intro h
    cases h with
    | inl h' => exact h' ∘ (·.left)
    | inr h' => exact h' ∘ (·.right)

theorem not_or_implication: (¬p ∨ q) → (p → q) :=
  ( fun hpq : ¬p ∨ q =>
    Or.elim hpq
    (fun hnp: ¬p => fun hp:p => show q from False.elim (hnp hp))
    (fun hq: q => fun _:p => hq))

theorem np_and_p_imp_false {p : Prop}: ¬p ∧ p → False := by
  intro npp
  exact npp.left npp.right

theorem And.elimination : p ∧ (¬p ∨ q) ↔ p ∧ q := by
  apply Iff.intro
  . rw [And.distrib_or]
    intro h
    cases h with
    | inl h' =>
      apply False.elim
      rw [And.comm] at h'
      exact np_and_p_imp_false h'
    | inr h' => exact h'
  . intro h
    apply And.intro
    . exact h.left 
    . exact Or.inr h.right

theorem not_not_elim {p : Prop}: (¬¬p) → p := Classical.byContradiction

theorem Or.comm (a b:Prop) : a ∨ b ↔ b ∨ a := by
  constructor
  intro ab
  apply Or.elim ab
  intro ha
  exact Or.intro_right b ha
  intro hb
  exact Or.intro_left a hb
  intro ba 
  apply Or.elim ba 
  intro hb 
  exact Or.intro_right a hb
  intro ha 
  exact Or.intro_left b ha

theorem notExistsIffAll (p : α -> Prop) : (¬∃ x, p x) ↔ (∀ x, ¬p x) := by
  constructor
  intro h2 x px
  have existsY : ∃y, p y := by exists x
  exact h2 existsY
  intro h1 h2
  match h2 with
  | ⟨w, hw⟩ => exact ((h1 w) hw)

theorem forallNotNot { p : α -> Prop } : (∀ x, ¬¬p x) ↔ (∀ x, p x) := by
  constructor
  intro h
  exact fun x => Classical.byContradiction (h x)
  intro h
  exact fun x => not_not_intro (h x)

theorem notAllIfExists (p : α -> Prop ) : (∃ x, ¬p x) → (¬∀ x, p x) := by
  intro h h2
  match h with
  | ⟨w, hw⟩ => exact hw (h2 w)
