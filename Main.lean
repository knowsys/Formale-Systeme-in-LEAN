open Classical

----------------------------------LOGIC-----------------------------------------
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

  case mp =>
    intro ⟨ha, hor⟩
    cases hor with
    | inl hl => exact Or.inl ⟨ha, hl⟩
    | inr hr => exact Or.inr ⟨ha, hr⟩

  case mpr =>
    intro h
    match h with
    | Or.inl ⟨ha, hb⟩ => exact ⟨ha, Or.inl hb⟩
    | Or.inr ⟨ha, hc⟩ => exact ⟨ha, Or.inr hc⟩

theorem Or.morgan : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (fun hnpq: ¬(p ∨ q) => 
    ⟨fun hp:p => hnpq (Or.intro_left q hp), fun hq:q => hnpq (Or.intro_right p hq)⟩ 
 )
  (fun hnpq : ¬p ∧ ¬q =>
    fun hpq : (p ∨ q) =>
      Or.elim hpq
      (fun hp:p => hnpq.left hp)
      (fun hq:q => hnpq.right hq)
 )

theorem And.morgan : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
  Iff.intro
  (fun hpq : ¬(p ∧ q) =>
    Or.elim (em p)
    (fun hp:p =>
      Or.elim (em q)
      (fun hq : q => show ¬p ∨ ¬q from False.elim (hpq ⟨hp, hq⟩))
      (fun nq : ¬q => (Or.intro_right (¬p) nq)))
    (fun np:¬p => (Or.intro_left (¬q) np)))
  (fun hpoq : ¬p ∨ ¬q =>
    Or.elim hpoq
    (fun hp:¬p =>
      fun hpnq : p ∧ q => hp hpnq.left)
    (fun hp:¬q =>
      fun hpnq : p ∧ q => hp hpnq.right))

theorem not_or_eq_implication: (¬p ∨ q) ↔ (p → q) :=
  Iff.intro
  ( fun hpq : ¬p ∨ q =>
    Or.elim hpq
    (fun hnp: ¬p => 
      fun hp:p => show q from False.elim (hnp hp))
    (fun hq: q => 
      fun _:p => hq))
  ( fun hpq : (p → q) =>
    Or.elim (em q)
    (fun hq:q => Or.intro_right (¬p) hq)
    (fun nq:¬q =>
      Or.elim (em p)
      (fun hp:p => show (¬p ∨ q) from False.elim (nq (hpq hp)))
      (fun np:¬p => show (¬p ∨ q) from Or.intro_left q np)
   ))

theorem And.elimination : p ∧ (¬p ∨ q) ↔ p ∧ q := by
  apply Iff.intro
  intro pnpq
  rw [not_or_eq_implication] at pnpq
  exact ⟨pnpq.left, pnpq.right pnpq.left⟩ 
  intro pq
  exact ⟨pq.left, Or.intro_right (¬p) pq.right⟩ 

theorem np_and_p_imp_false {p : Prop}: ¬p ∧ p → False := by
  intro npp
  exact npp.left npp.right

theorem not_not_p {p : Prop}: (¬¬p) ↔ p := by
  apply Iff.intro
  intro nnp
  cases (Classical.em p) with 
  | inl hp => 
    exact hp
  | inr hr => 
    apply False.elim (nnp hr)
  intro hp 
  cases (Classical.em ¬ p) with 
  | inl hl => 
    apply False.elim (hl hp)
  | inr hr =>
    exact hr 

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


theorem notAllEqExists (p : α → Prop) (h: ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

theorem notExistsEqAll (p : α → Prop) : (¬∃ x, p x) → (∀ x, ¬p x) := by
  intro h2
  intro x
  intro px
  have existsY : ∃y, p y := by exists x
  exact h2 existsY

----------------------------------LISTS-----------------------------------------
theorem list_concat_empty {α :Type u} (as : List α) : as ++ [] = as := by
simp [List.cons]

theorem EmptyNotFull : (∀ x xs, list ≠ (x::xs)) → list = [] := by
      intro h
      cases (list) with
      | nil => rfl
      | cons x1 xs1 => 
        exact absurd rfl (h x1 xs1)

----------------------------------SETS------------------------------------------
def Set (α : Type u) := α -> Prop

namespace Set
def element {α : Type u} (e : α) (X : Set α) : Prop := X e
infixr:75 " ∈ " => element

def union {α : Type u} (X Y : Set α) : Set α := fun a => a ∈ X ∨ a ∈ Y
infixr:65 " ∪ " => union

def subset {α : Type u} (X Y : Set α) : Prop := ∀ e : α, e ∈ X → e ∈ Y
infixr:50 " ⊆ " => subset

def intersection {α : Type u} (X Y : Set α) : Set α := fun (e: α) => e ∈ X ∧ e ∈ Y
infixr:80 " ∩ " => intersection

def diff {α : Type u} (X Y : Set α) : Set α := fun (e: α) => e ∈ X ∧ ¬(e ∈ Y)
--infixr:80 " \\ " => intersection

def empty {α :Type u}: Set α := fun _ => False

notation (priority := high) "∅" => empty


theorem setext {α :Type u} {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
 funext (fun x => propext (h x))

theorem inter_self {α :Type u} (a : Set α) : a ∩ a = a := by
  apply setext
  intro x
  constructor
  intro n 
  rw [element, intersection] at n
  exact n.left 
  intro n 
  exact ⟨n,n⟩ 

theorem inter_empty {α :Type u} (X : Set α) : X ∩ ∅ = ∅ := by 
  apply setext
  intro n
  constructor
  intro x 
  rw [element, intersection] at x
  exact x.right 
  intro x 
  rw [element] at x 
  rw [empty] at x 
  exact False.elim x 

theorem inter_comm {α : Type u} (X Y:Set α) : X ∩ Y = Y ∩ X := by 
  apply setext 
  intro x 
  constructor 
  intro n 
  rw [element, intersection] at n
  rw [element, intersection]
  exact ⟨n.right, n.left⟩ 
  intro n 
  rw [element, intersection] at n
  rw [element, intersection]
  exact ⟨n.right, n.left⟩ 

theorem union_or {α : Type u} (X Y : Set α) (e : α) : (e ∈ (X ∪ Y)) = (e ∈ X ∨ e ∈ Y) := by rfl

theorem union_comm {α :Type u} (X Y : Set α) : X ∪ Y = Y ∪ X :=
  by
  apply funext
  intro f
  rw [union]
  rw [union]
  rw [Or.comm]

theorem empty_inter {α :Type u} (a : Set α) : ∅ ∩ a = ∅ := by 
  rw [inter_comm]
  apply inter_empty

theorem intersection_and {α : Type u} (X Y : Set α) (e:α) : (e ∈ (X ∩ Y)) = (e ∈ X ∧ e ∈ Y) := by rfl

theorem union_dist_intersection {α : Type u} (X Y Z : Set α) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  apply funext
  intro x
  rw [union, intersection]
  repeat rw [element]
  rw [union, union, intersection]
  rw [Or.distrib_and]
  rfl

theorem intersection_dist_union {α : Type u} (X Y Z : Set α) : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  apply funext
  intro x
  rw [intersection, union]
  repeat rw [element]
  rw [union, intersection, intersection,And.distrib_or]
  rfl

end Set

----------------------------------WORDS------------------------------------------
structure Word (α : Type u) where
  data : List α
  deriving Repr

def Word.concat {α : Type u} (x y : Word α) : Word α := {data := x.data ++ y.data}
infixr:70 " ∘ " => Word.concat

def Word.epsilon {α : Type u} : Word α := Word.mk List.nil
notation (priority := high) "ε" => Word.epsilon

def Word.len {α : Type u} (w:Word α) : Nat :=
  match w with 
  | Word.mk List.nil => 0
  | Word.mk (x::xs) => 1 + Word.len (Word.mk (xs))

theorem Word.objects_equal {α : Type u} (w :Word α): Word.mk w.data = w := by rfl 

@[simp] theorem Word.epsilon_eq_epsilon {α : Type u} : (@ε α)= (Word.mk List.nil) := by rfl 

def Word.AllElementsOfWordInSet {α : Type u} (w: Word α) (S: Set α) :=
  match w with 
  | Word.mk (a::as)=> a ∈ S ∧ Word.AllElementsOfWordInSet (Word.mk as) S
  | _ => True

----------------------------------LANGUAGES---------------------------------------
def Language (α : Type u) := Set (Word α)

def Language.concat {α : Type u} (X Y : Language α) : Language α := fun w : Word α => ∃ u v : Word α, u ∈ X ∧ v ∈ Y ∧ w = u ∘ v
infixr:70 " ∘ₗ " => Language.concat

def Language.epsilon {α:Type u} : Language α :=
  fun w =>
  match w with
  | Word.mk List.nil => True
  | Word.mk (_::_) => False

def Language.power {α : Type u} (n:Nat) (X: Language α) : Language α := 
  match n with
  | 0 => 
    Language.epsilon
  | (Nat.succ m) => 
    fun (w:Word α)=> 
      ∃ w1 w2 : Word α, w2 ∈ (Language.power m X) ∧ w1 ∈ X ∧ w = w1 ∘ w2

def Language.kleene {α :Type u} (X: Language α) : Language α :=
  fun w: Word α =>
    ∃ n : Nat, w ∈ Language.power n X

def Language.plus {α :Type u} (X :Language α) : Language α :=
  fun w: Word α => ∃ n:Nat, ¬ (n = 0) ∧ w ∈ Language.power n X

def Sigma.language {α : Type u}: Language α := 
  fun w: Word α =>
    match w with
    | (Word.mk (_::[])) => True
    | _ => False

def Sigma.kleene {α :Type u}: Language α :=
  fun w: Word α => (@Language.kleene _ Sigma.language) w
      
def Language.complement {α :Type u} (X: Language α) : Language α :=
  fun w: Word α =>
    ¬(w ∈ X)


theorem Lanuage.eps_element_only_element_in_eps_lang_il {α :Type u} (w : Word α) : Language.epsilon w -> w = {data := []} := by
intro n
rw [← Word.objects_equal w] at n
cases h:w.data with
| nil =>
  rw [h] at n 
  rw [← Word.objects_equal w]
  rw [h]
| cons a as =>
  rw [h] at n
  simp [Language.epsilon] at n

theorem Language.eps_element_only_element_in_eps_lang {α :Type u} {w: Word α} : w ∈ Language.epsilon ↔ (w = Word.mk []) := by
constructor
exact Lanuage.eps_element_only_element_in_eps_lang_il w
intro n 
simp [Set.element,n, Language.epsilon]

theorem Language.kleene_eq_plus_eps {α :Type u} {X: Language α} : Language.plus X ∪ Language.epsilon = Language.kleene X := by 
  apply funext
  intro w
  apply propext
  constructor
  intro x
  simp [Set.union] at x
  rw[Set.element] at x 
  rw [Language.kleene]
  cases x with 
  |inl p => 
    rw [Language.plus] at p 
    cases p with
    | intro n r =>
      exists n 
      exact r.right 
  |inr e => 
    exists 0
  intro n 
  rw [Set.union]
  simp [Language.kleene] at n 
  cases n with 
  | intro nn r => 
    cases nn with 
    | succ m => 
      apply Or.inl 
      simp [Set.element, Language.plus]
      exists (Nat.succ m)
      rw [Set.element] at r
      exact ⟨Nat.succ_ne_zero m, r⟩ 
    | zero => 
      apply Or.inr
      simp [Set.element] at r
      simp [Language.power] at r
      simp [Set.element]
      exact r 

theorem Language.lan_eps_eq_lan {α : Type u} (L : Language α): L ∘ₗ Language.epsilon = L := by
  apply funext
  intro w
  apply propext
  constructor
  rw [Language.concat]
  intro ⟨u,v, h1, h2, h3⟩
  rw [Word.concat] at h3
  rw [Set.element] at h1
  rw [Language.eps_element_only_element_in_eps_lang] at h2
  simp [h2] at h3
  rw [(Word.objects_equal u)] at h3
  simp [*]
  intro n 
  rw [Language.concat]
  exists w 
  exists Word.mk []
  apply And.intro 
  exact n 
  apply And.intro 
  rw [Set.element]
  simp [Word.epsilon, Language.epsilon]
  simp [Word.concat]

theorem Language.eps_lan_eq_lan {α : Type u} (L : Language α): Language.epsilon ∘ₗ L = L := by
  apply funext
  intro w
  apply propext
  constructor
  rw [Language.concat]
  intro ⟨u,v, h1, h2, h3⟩
  rw [Word.concat] at h3
  rw [Language.eps_element_only_element_in_eps_lang] at h1
  simp [h2] at h3
  rw [Set.element] at h2
  simp [h1,Word.objects_equal] at h3
  simp [*]
  intro n 
  rw [Language.concat]
  exists (Word.mk [])
  exists w

theorem Language.empty_lan_eq_empty {α :Type u} (L : Language α) : L ∘ₗ ∅ = ∅ := by
  apply Set.setext 
  intro w 
  constructor
  intro n 
  rw [Set.element, Language.concat] at n 
  match n with 
  | ⟨u,v,_,h2,h3⟩ =>
    rw [Set.element, Set.empty] at h2
    apply False.elim h2 
  intro n 
  rw [Set.element, Set.empty] at n
  apply False.elim n 

theorem Language.lan_empty_eq_empty {α :Type u} (L : Language α) : ∅ ∘ₗ L = ∅ := by
  apply Set.setext 
  intro w 
  constructor
  intro n 
  rw [Set.element, Language.concat] at n
  match n with 
  | ⟨u,v, h1,h2,h3⟩ => 
    rw [Set.element, Set.empty] at h1
    apply False.elim h1 
  intro n 
  rw [Set.element, Set.empty] at n 
  apply False.elim n 

theorem Language.concat_dist_union_r {α : Type u} (L1 L2 L3 : Language α) : (L1 ∪ L2) ∘ₗ L3 = (L1 ∘ₗ L3) ∪ (L2 ∘ₗ L3) := by
  apply Set.setext 
  intro w 
  constructor 
  intro n 
  rw [Set.element, Language.concat] at n
  match n with 
  | ⟨u,v,h1,h2,h3⟩ => 
    rw [Set.element,Set.union, Set.element]
    rw [Set.element, Set.union] at h1
    cases h1 with 
    | inl hl => 
      apply Or.inl
      rw [Language.concat]
      exists u
      exists v 
    | inr hr =>
      apply Or.inr 
      rw [Set.element, Language.concat]
      exists u
      exists v
  intro n 
  rw [Set.element, Set.union] at n
  cases n with 
  | inl hl =>
    rw [Set.element, Language.concat]
    rw [Set.element, Language.concat] at hl
    match hl with 
    | ⟨u,v,h1,h2,h3⟩ =>
      exists u
      exists v 
      rw [Set.element,Set.union]
      exact ⟨Or.inl h1, h2,h3⟩ 
  |inr hr => 
    rw [Set.element, Language.concat]
    rw [Set.element, Language.concat] at hr 
    match hr with 
    | ⟨u,v,h1,h2,h3⟩ => 
      exists u
      exists v
      exact ⟨Or.inr h1, h2, h3⟩ 
      
theorem Language.morgan_union {α : Type u} (L1 L2 : Language α) : (L1 ∪ L2) = Language.complement (Language.complement L1 ∩ Language.complement L2):= by
  apply Set.setext
  intro w 
  repeat (first | rw [Set.element] | rw [Set.union] | rw [Set.intersection] | rw [Set.union] |rw [Language.complement] )
  rw [← Or.morgan, not_not_p]constructor
  repeat (first | intro n | exact n)

theorem Language.morgan_inter {α : Type u} (L1 L2: Language α) : (L1 ∩ L2) = Language.complement (Language.complement L1 ∪ Language.complement L2) := by 
  apply Set.setext 
  intro w 
  repeat (first | rw [Set.element] | rw [Set.union] | rw [Set.intersection] | rw [Set.union] |rw [Language.complement] )
  rw [← And.morgan, not_not_p]
  constructor
  repeat (first | intro n | exact n)

theorem Language.concat_dist_union_l {α : Type u} (L1 L2 L3 : Language α) :
L1 ∘ₗ (L2 ∪ L3) = (L1 ∘ₗ L2) ∪ (L1 ∘ₗ L3) :=
  by
    apply funext
    intro w
    apply propext
    constructor

    case mp =>
      intro h
      cases h with | intro u pu => cases pu with | intro v pv =>
        rw [@And.comm (v ∈ (L2 ∪ L3)), ← And.assoc, Set.union_or, And.distrib_or] at pv

        cases pv with
        | inl _ =>
          apply Or.inl
          exists u, v
          rw [@And.comm (v ∈ L2), ← And.assoc]
          assumption
        | inr _ =>
          apply Or.inr
          exists u, v
          rw [@And.comm (v ∈ L3), ← And.assoc]
          assumption

    case mpr =>
      intro h
      cases h with
        | inl hl => cases hl with | intro u pu => cases pu with | intro v pv =>
          match pv with
          | ⟨h1, h2, h3⟩ =>
            exists u, v
            exact ⟨h1, Or.inl h2, h3⟩
        | inr hr => cases hr with | intro u pu => cases pu with | intro v pv =>
          match pv with
          | ⟨h1, h2, h3⟩ =>
            exists u, v
            exact ⟨h1, Or.inr h2, h3⟩

@[simp] theorem eq_rfl {a : Type α} : (a = a) ↔ True := by simp[]
  

----------------------------------GRAMMARS---------------------------------------
structure Grammar {α : Type u} where
  V : Set α 
  E : Set α 
  S: α 
  P : Set ((Word α) × (Word α))
  bed_VEdisj : V ∩ E = ∅
  bed_SinV: S ∈ V 
  bed_VarInLeft: 
    ∀ pair : (Word α) × (Word α),
    P pair -> (
      ∃ v1 v2 v3 : Word α, 
        ((pair.fst) = (v1 ∘ v2 ∘ v3)) ∧ 
        (∃ t: α, (Word.mk ([t]) = v2 ∧ t ∈ V))
   )

structure RegularGrammar {α : Type u} extends (@Grammar α) where
  bed_reg: ∀ pair : ((Word α) × (Word α)), 
    (pair ∈ P) -> 
    (
      (∃ t: α, (Word.mk [t] = pair.fst) ∧ t ∈ V) ∧ (
        (∃ t1 t2 : α, (Word.mk [t1, t2] = pair.snd) ∧ t1 ∈ E ∧ t2 ∈ V) ∨ 
        (∃ t: α, Word.mk [t] = pair.snd ∧ t ∈ E) ∨ 
        pair.snd = Word.mk []
     )
   )

structure EpsilonFreeRegularGrammar {α : Type u} extends (@RegularGrammar α) where
  epsilonFree : ∀ pair : (Word α) × (Word α), 
  ¬ (pair ∈ P) ∨ (
    pair.fst = Word.mk ([S]) ∨ ¬ (pair.snd = Word.epsilon)
 )

def OneStepDerivation {α : Type u} (G : @Grammar α) (w : Word α) (v : Word α) : Prop :=
    ∃ w1 w2 w3: Word α,
      ∃ v1 v2 v3: Word α,
      have p1 := w = w1 ∘ w2 ∘ w3
      have p2 := v = v1 ∘ v2 ∘ v3
      (v1 = w1) ∧ (v3 = w3) ∧ p1 ∧ p2 ∧ G.P ⟨w2, v2⟩
        
def NstepDerivation {α : Type u} (G : @Grammar α) (w : Word α) (v : Word α) (n:Nat) : Prop :=
  match n with
  | 0 => 
    w = v
  | (Nat.succ m) => 
      ∃ w1 : Word α, (OneStepDerivation G w w1) ∧ (NstepDerivation G w1 v m) ∧ (Word.AllElementsOfWordInSet v G.E)

def StarDerivation {α : Type u} (G : @Grammar α) (w : Word α) (v : Word α) : Prop :=
  ∃ n : Nat, NstepDerivation G w v n
  
def GeneratedLanguageGrammar {α : Type u} (G : @Grammar α): Language α :=
  fun w: Word α => 
    StarDerivation G (Word.mk [G.S]) w

def RunRegularGrammarSub {α : Type u} (ql qg : α) (G : @RegularGrammar α) (run: List (Word α × Word α))(w : Word α) : Prop :=
    match w with 
    | (Word.mk (word::ws1)) =>
      match run with 
      | (p1::xs) =>
          p1 ∈ G.P ∧ 
          p1.fst = (Word.mk [ql]) ∧ 
          (∃ t1 : α, (Word.mk [word, t1] = p1.snd)
                  ∧ RunRegularGrammarSub t1 qg G xs (Word.mk ws1) 
           )
      | _ => False 
    | _ => 
      ql = qg

def LanguageRegularGrammar {α : Type u} (G : @RegularGrammar α) : Language α :=
  fun w => ∃ qn run, (RunRegularGrammarSub G.S qn G run w ∧ ⟨Word.mk [qn], Word.mk []⟩ ∈ G.P
    ∨ ∃ w1, ∃ z : α, (w = w1 ∘ Word.mk [z]) ∧ RunRegularGrammarSub G.S qn G run w1 ∧ ⟨Word.mk [qn], Word.mk [z]⟩ ∈ G.P)

----------------------------------AUTOMATA------------------------------------------
structure NFA {α : Type u} where 
  Q : Set α 
  E : Set α 
  δ : Set ((α × α) × α)
  Q0 : Set α 
  F: Set α
  QEdisj: Q ∩ E = ∅ 
  Q0subset: Q0 ⊆ Q 
  Fsubset: F ⊆ Q
  Tfunction: 
    ∀ t : ((α × α) × α),
       ¬ (t ∈ δ) ∨ (
          t.fst.fst ∈ Q ∧ 
          t.fst.snd ∈ E ∧ 
          t.snd ∈ Q
      ) 
  
structure DFA {α : Type u} extends (@ NFA α) where 
  q0 : α 
  bed_Q0:
  (Q0 = 
    (fun a : α => 
       (q0 = a)
     )
 ) 
  uniqueness:
      ∀ t1 t2 : ((α × α) × α),
       ¬ ((t1 ∈ δ) ∧ (t2 ∈ δ)) ∨ 
        (¬ (t1.fst = t2.fst) ∨ t1.snd = t2.snd)

def nfaDerivation {α : Type u} (nfa: @ NFA α) (q1 qf: α) (w: Word α) : Prop :=
  match w with 
  | Word.mk (x::xs) => ∃ qn, nfa.δ ⟨⟨q1, x⟩,qn⟩ ∧ nfaDerivation nfa qn qf (Word.mk xs) 
  | Word.mk [] => q1 = qf

def nfaLanguage {α : Type u} (nfa: @ NFA α) : Language α :=
  fun w => ∃ qs qf, qs ∈ nfa.Q0 ∧ qf ∈ nfa.F ∧ nfaDerivation nfa qs qf w

structure TotalDFA {α : Type u} extends (@ DFA α) where 
  tot: ∀ t : ((α × α) × α),
  (¬ (t.fst.snd ∈ E ∧ t.fst.fst ∈ Q) ∨ 
    ∃ q2 : α, ⟨⟨t.fst.fst, t.fst.snd⟩, q2⟩ ∈ δ
 )

def TotalDFAConstruct {α : Type u} (dfa: @ DFA α) (fang: α) (p1: ¬fang ∈ dfa.Q ∧ ¬fang ∈ dfa.E) : @TotalDFA α :=
  let Q2: Set α := fun w => (w ∈ dfa.Q) ∨ (w=fang) 
  let δ2: Set ((α × α) × α) := fun ⟨⟨w1, w2⟩, w3⟩ => ⟨⟨w1, w2⟩, w3⟩ ∈ dfa.δ ∨ (¬ (∃ a : α,⟨⟨w1, w2⟩, a⟩ ∈ dfa.δ)∧ Q2 w1 ∧ dfa.E w2 ∧ w3 = fang)
  
  have delta_def_rfl : (fun ⟨⟨w1, w2⟩, w3⟩ => ⟨⟨w1, w2⟩, w3⟩ ∈ dfa.δ ∨ (¬ (∃ a : α,⟨⟨w1, w2⟩, a⟩ ∈ dfa.δ)∧ Q2 w1 ∧ dfa.E w2 ∧ w3 = fang)) = δ2 := 
    by rfl

  have Q2_def_rfl : ((fun w => (w ∈ dfa.Q) ∨ (w=fang)): (Set α)) = Q2 := 
    by rfl

  have setEmpty_rfl : Set.empty = (fun _ => False) := by rfl

  have QSubsetQ2: (dfa.Q ⊆ Q2) := by
    intro n
    intro w 
    simp [Set.element]
    apply Or.inl 
    exact w

  have Q2Edisj : Q2 ∩ dfa.E = Set.empty:= by
    rw [setEmpty_rfl]
    simp [Set.intersection]
    apply funext
    intro x
    simp [And.distrib_or, Set.element]
    have hq := dfa.QEdisj
    simp [Set.intersection, setEmpty_rfl] at hq
    have hp : ((fun e => e ∈ dfa.Q ∧ e ∈ dfa.E) = fun _ => False) → (∀e : α, (e ∈ dfa.Q ∧ e ∈ dfa.E) = False):= by
      intro _
      intro n
      rw [←Set.intersection, dfa.QEdisj, Set.empty]
    have hl := hp hq
    have hll := hl x
    simp [Set.element] at hll
    rw [And.comm] at hll
    simp [Set.intersection, Set.element]
    cases (Classical.em (x = fang)) with 
    | inl xfang => 
      have p2 := p1.right
      simp [xfang]
      have hv : dfa.E fang ↔ False := by
        constructor
        intro x
        apply p2
        rw [Set.element]
        exact x
        intro x
        apply False.elim x
      simp [hv]
    | inr xNotFang =>
      simp [xNotFang]
      apply propext 
      constructor 
      intro x1
      rw [And.comm, hll] at x1
      exact x1
      intro x
      apply False.elim x

  have Q0SubsetQ2: (dfa.Q0 ⊆ Q2) := by
    have dfa_subset := dfa.Q0subset
    simp [Set.subset]
    intro n 
    have hl := QSubsetQ2
    rw [Set.subset] at hl 
    have hll := hl n 
    rw [Set.subset] at dfa_subset
    have hrr := dfa_subset n 
    intro x 
    exact hll (hrr x)

  have FSubsetQ2: (dfa.F ⊆ Q2) := by
    have dfa_subset := dfa.Fsubset
    simp [Set.subset]
    intro n 
    have hl := QSubsetQ2
    rw [Set.subset] at hl 
    have hll := hl n 
    rw [Set.subset] at dfa_subset
    have hrr := dfa_subset n 
    intro x 
    exact hll (hrr x)

  have Tfunction2: (∀ t : ((α × α) × α),
       ¬ (t ∈ δ2) ∨ (
          t.fst.fst ∈ Q2 ∧ 
          t.fst.snd ∈ dfa.E ∧ 
          t.snd ∈ Q2
      )) := by
       intro triple
       rw [not_or_eq_implication]
       intro triple_in_delta2
       have triple_in_delta2_old := triple_in_delta2
       rw [Set.element,←delta_def_rfl] at triple_in_delta2
       match triple with 
       | ⟨⟨qs,b⟩, qz⟩ => 
          have hsorry2 : ⟨⟨qs, b⟩, qz⟩ ∈ dfa.toNFA.δ ∨ ((¬ (∃ a : α,⟨⟨qs, b⟩, a⟩ ∈ dfa.δ))∧ Q2 qs ∧ NFA.E dfa.toNFA b ∧  (qz = fang)) := by 
            simp [Set.element, ← delta_def_rfl] at triple_in_delta2
            exact triple_in_delta2
          have hsorry : ⟨⟨qs, b⟩, qz⟩ ∈ dfa.toNFA.δ ∨ (Q2 qs ∧ NFA.E dfa.toNFA b ∧ (qz = fang)):= by 
            apply Or.elim hsorry2
            intro x 
            apply Or.inl
            exact x
            intro x 
            apply Or.inr 
            simp [x]
          simp[Set.element]
          have dfa_tfun := dfa.Tfunction
          have dfa_tfun_w := dfa_tfun ⟨⟨qs, b⟩, qz⟩ 
          simp [Set.element] at dfa_tfun_w 
          repeat rw [←Set.element] at dfa_tfun_w
          simp [not_or_eq_implication] at dfa_tfun_w
          have k1 : Q2 qs := by
            cases (Classical.em (dfa.δ ⟨⟨qs,b⟩, qz⟩)) with 
            | inl hl =>
                have dfa_tfun_conjunctions := dfa_tfun_w hl
                have kk1 := dfa_tfun_conjunctions.left
                apply QSubsetQ2
                rw [Set.element]
                exact kk1
            | inr hr =>
              apply Or.elim (hsorry)
              intro f
              apply False.elim (hr f)
              intro rdef
              have g := rdef.left
              exact g
          have k2 : dfa.E b := by
            cases (Classical.em (dfa.δ ⟨⟨qs,b⟩, qz⟩)) with 
            | inl hl =>
              have dfa_tfun_conjunctions := dfa_tfun_w hl
              have kk1 := dfa_tfun_conjunctions.right.left
              exact kk1
            | inr hr =>
              apply Or.elim (hsorry)
              intro f
              apply False.elim (hr f)
              intro rdef
              have g := rdef.right.left
              exact g
          have k3: Q2 qz := by
            cases (Classical.em (dfa.δ ⟨⟨qs,b⟩, qz⟩)) with 
            | inl hl =>
              have dfa_tfun_conjunctions := dfa_tfun_w hl
              have kk1 := dfa_tfun_conjunctions.right.right
              apply QSubsetQ2
              exact kk1
            | inr hr =>
              apply Or.elim (hsorry)
              intro f
              apply False.elim (hr f)
              intro rdef
              have gh := rdef.right.right
              rw [gh]
              have q2_fang : Q2 fang := by
                rw [← Q2_def_rfl]
                have hqq : (fun w => w ∈ dfa.toNFA.Q ∨ w = fang) fang = (fang ∈ dfa.toNFA.Q ∨ fang = fang) := by rfl
                rw [hqq]
                apply Or.inr
                have aea : fang = fang := by rfl
                exact aea 
              exact q2_fang
          exact ⟨k1, k2, k3⟩

  have tot2: ∀ t : ((α × α) × α),
  (¬ (t.fst.snd ∈ dfa.E ∧ t.fst.fst ∈ Q2) ∨ 
    ∃ q2 : α, ⟨⟨t.fst.fst, t.fst.snd⟩, q2⟩ ∈ δ2
 ):= by 
        intro triple
        match triple with 
       | ⟨⟨qs,b⟩, qz⟩ => 
          simp [not_or_eq_implication]
          intro x
          simp [Set.element, ← delta_def_rfl]
          cases (Classical.em (∃y, dfa.δ ⟨⟨qs,b⟩, y⟩)) with 
          | inl hl =>
            match hl with 
            | ⟨y, hy⟩ => 
              exists y 
              apply Or.inl 
              exact hy 
          | inr hr => 
            exists fang
            have hfang : fang = fang := rfl 
            apply Or.inr 
            exact ⟨hr, x.right, x.left, hfang⟩

  have uniqueness2 :
      ∀ t1 t2 : ((α × α) × α),
       ¬ ((t1 ∈ δ2) ∧ (t2 ∈ δ2)) ∨ 
        (¬ (t1.fst = t2.fst) ∨ t1.snd = t2.snd) := by 
        intro triple1
        intro triple2 
        rw [not_or_eq_implication]
        intro bed1
        rw [not_or_eq_implication]
        intro bed2 
        simp[] at bed2 
        have bed11 := bed1.left 
        have bed12 := bed1.right
        have dfa_uniqueness := dfa.uniqueness triple1 triple2
        repeat rw [not_or_eq_implication] at dfa_uniqueness
        match triple1 with 
        | ⟨first1, qz1⟩ => 
          match triple2 with 
          |⟨first2, qz2⟩ => 
            simp [] at bed2
            simp [Set.element] at dfa_uniqueness
            simp [Set.element, ← delta_def_rfl] at bed11
            simp [bed2, Set.element, ← delta_def_rfl] at bed12
            simp []
            cases bed11 with 
            | inl hl1 =>
              cases bed12 with 
              | inl hl2 =>
                exact dfa_uniqueness ⟨hl1, hl2⟩ bed2 
              | inr hr2 => 
                rw [bed2] at hl1
                have hNEtransition := hr2.left
                have exa :∃ a, dfa.δ ⟨first2,a⟩ := by
                  exists qz1
                have hfalse := hNEtransition exa
                apply False.elim hfalse
            | inr hr1 => 
              cases bed12 with 
              | inl hl1 =>
                have hNEtransition := hr1.left
                rw [← bed2] at hl1
                have exa :∃ a, dfa.δ ⟨first1,a⟩ := by
                  exists qz2
                have hfalse := hNEtransition exa
                apply False.elim hfalse
 
              | inr hr2 => 
                have h_right := hr1.right.right.right
                have h_left := hr2.right.right.right
                simp [h_left, h_right]

    {tot := tot2, uniqueness := uniqueness2, Tfunction := Tfunction2, Q0 := dfa.Q0, Q:= Q2, E := dfa.E, δ := δ2, QEdisj := Q2Edisj, F := dfa.F, Q0subset := Q0SubsetQ2, Fsubset := FSubsetQ2, q0 := dfa.q0, bed_Q0 := dfa.bed_Q0 : TotalDFA}


----------------------------------GRAMMARS & AUTOMATA------------------------------
def ConstructRegularGrammarFromDFA {α : Type u} (dfa: @ DFA α) : @RegularGrammar α:= 
  let E : Set α := dfa.E
  have E_def_refl : E = dfa.E := by rfl
  
  let V : Set α := dfa.Q
  have V_def_refl : V = dfa.Q := by rfl
  
  let S : α := dfa.q0
  have S_def_refl : S = dfa.q0 := by rfl
  
  let P : Set ((Word α) × (Word α)) := 
    fun rule : (Word α) × (Word α) => 
      (∃ql a qr : α, rule.fst = Word.mk [ql] ∧ rule.snd = Word.mk [a] ∘ Word.mk [qr] ∧ ⟨⟨ql,a⟩,qr⟩ ∈ dfa.δ)
      ∨ (∃ q, rule.fst = Word.mk [q] ∧ rule.snd = Word.epsilon ∧ (q ∈ dfa.F))
  have P_def_refl : P = fun rule : (Word α) × (Word α) => 
      (∃ql a qr : α, rule.fst = Word.mk [ql] ∧ rule.snd = Word.mk [a] ∘ Word.mk [qr] ∧ ⟨⟨ql,a⟩,qr⟩ ∈ dfa.δ)
      ∨ (∃ q, rule.fst = Word.mk [q] ∧ rule.snd = Word.epsilon ∧ (q ∈ dfa.F)) := by rfl
  
  have bed_VEdisj : V ∩ E = ∅ := by
    have QEdisj := dfa.QEdisj
    simp [E_def_refl, V_def_refl]
    exact QEdisj
  
  have bed_SinV: S ∈ V := by
    simp [S_def_refl, V_def_refl, Set.element]
    have q0inQ0 : dfa.q0 ∈ dfa.Q0 := by 
      simp [Set.element]
      have bed_Q0 := dfa.bed_Q0
      rw [bed_Q0]
    have q0inQ := dfa.Q0subset dfa.q0 q0inQ0
    rw [Set.element] at q0inQ
    exact q0inQ 
  
  have bed_VarInLeft: 
    ∀ pair : (Word α) × (Word α),
    P pair -> (
      ∃ v1 v2 v3 : Word α, 
        ((pair.fst) = (v1 ∘ v2 ∘ v3)) ∧ 
        (∃ t: α, (Word.mk ([t]) = v2 ∧ t ∈ V))
   ) := by
    intro pair
    intro pairInP
    simp [P_def_refl] at pairInP
    cases pairInP with 
    | inl disj1 => 
      match disj1 with
      | ⟨ql, a, qr, disj1woE⟩ => 
        exists Word.mk []
        exists Word.mk [ql]
        exists Word.mk []
        simp [Word.concat]
        have k1 := disj1woE.left
        have k2 : ∃ t, t = ql ∧ t ∈ V := by
          exists ql
          simp []
          have disj3 := disj1woE.right.right
          rw [Set.element] at disj3
          have Tfunction := dfa.Tfunction
          have Tfunction2 := Tfunction ⟨⟨ql, a⟩,qr⟩
          rw [not_or_eq_implication] at Tfunction2
          have Tfunction3 := Tfunction2 disj3
          simp [] at Tfunction3
          have Tfunction31 := Tfunction3.left
          exact Tfunction31
        have k1Andk2 := And.intro k1 k2
        exact k1Andk2
    | inr disjB => 
        match disjB with
        | ⟨q, disjB2⟩ =>

          exists Word.mk []
          exists Word.mk [q]
          exists Word.mk []
          simp [Word.concat]
          have k2 : ∃ t, t = q ∧ t ∈ dfa.toNFA.Q := by
            exists q
            have qInQ : q ∈ dfa.Q := by
              have FsbQ := dfa.Fsubset
              have qInQ2 := FsbQ q disjB2.right.right 
              exact qInQ2
            simp [qInQ]
          simp [disjB2.left, k2]
  have bed_reg: ∀ pair : ((Word α) × (Word α)), 
    (pair ∈ P) -> 
    (
      (∃ t: α, (Word.mk [t] = pair.fst) ∧ t ∈ V) ∧ (
        (∃ t1 t2 : α, (Word.mk [t1, t2] = pair.snd) ∧ t1 ∈ E ∧ t2 ∈ V) ∨ 
        (∃ t: α, Word.mk [t] = pair.snd ∧ t ∈ E) ∨ 
        pair.snd = Word.mk []
     )
   ) := by 
      intro pair
      intro pairInP
      simp [P_def_refl] at pairInP
      cases pairInP with 
      | inl disj1 => 
        match disj1 with
        | ⟨ql, a, qr, disj1woE⟩ => 
          simp [Word.concat]
          have k1 : ∃ t, t = ql ∧ t ∈ V := by
            exists ql
            simp []
            have disj3 := disj1woE.right.right
            rw [Set.element] at disj3
            have Tfunction := dfa.Tfunction
            have Tfunction2 := Tfunction ⟨⟨ql, a⟩,qr⟩
            rw [not_or_eq_implication] at Tfunction2
            have Tfunction3 := Tfunction2 disj3
            simp [] at Tfunction3
            have Tfunction31 := Tfunction3.left
            exact Tfunction31
          have k2 : ∃ t1 t2 : α, (Word.mk [t1, t2] = pair.snd) ∧ t1 ∈ E ∧ t2 ∈ V := by
            exists a
            exists qr
            simp [Word.concat] at disj1woE
            have k21 := disj1woE.right.left
            have Tfunction := dfa.Tfunction
            have k22 : a ∈ E ∧ qr ∈ V := by
              have pInQ := disj1woE.right.right
              have Tfunction2 := Tfunction ⟨⟨ql, a⟩,qr⟩
              rw [not_or_eq_implication] at Tfunction2
              have Tfunction3 := Tfunction2 pInQ
              simp [] at Tfunction3
              have Tfunction31 := Tfunction3.right
              rw [V_def_refl, E_def_refl]
              simp [Tfunction31]
            simp [k21, k22]
          simp [k2]
          exists ql
          simp [disj1woE.left]
          match k1 with 
          | ⟨qrr, k1woE⟩ =>
          simp [←k1woE.left]
          exact k1woE.right
      | inr disjB =>
          match disjB with
          | ⟨q, disjB2⟩ =>
            have k1 : (∃ t, {data := [t]} = pair.fst ∧ t ∈ V) := by
              exists q
              have qInQ : q ∈ dfa.Q := by
                have FsbQ := dfa.Fsubset
                have qInQ2 := FsbQ q disjB2.right.right 
                exact qInQ2
              simp [qInQ, disjB2.left]
            have k2: ((∃ t1 t2, {data := [t1, t2]} = pair.snd ∧ t1 ∈ E ∧ t2 ∈ V) ∨ (∃ t, {data := [t]} = pair.snd ∧ t ∈ E) ∨ pair.snd = {data := []}) := by
              apply Or.inr
              apply Or.inr
              simp [disjB2.right]
            simp [k1, k2]

    {V := V, E := E, S := S, P := P, bed_VEdisj := bed_VEdisj, bed_SinV := bed_SinV, bed_VarInLeft := bed_VarInLeft, bed_reg := bed_reg : RegularGrammar}
       
theorem deriviationsEQ1 {α : Type u} (dfa: @ DFA α)(w: Word α) : 
     ∀ q1 q2 :α, (nfaDerivation dfa.toNFA q1 q2 w) -> (
      (∃ run, RunRegularGrammarSub q1 q2 (ConstructRegularGrammarFromDFA dfa) run w)):= by
  have hp := Word.objects_equal w 
  rw [← hp] 
  induction w.data with
  | nil => 
    intro q1
    intro q2
    intro deriviation 
    simp [nfaDerivation] at deriviation 
    exists []
  | cons x xs iv => 
    intro q11
    intro q22
    intro deriviation 
    simp [nfaDerivation] at deriviation
    match deriviation with
    | ⟨qn, abl1⟩ =>
      have hh := iv qn q22 abl1.right 
      simp [Word.concat]
      match hh with 
      | ⟨run, hhz1⟩ =>
        exists ⟨Word.mk [q11], Word.mk [x,qn]⟩::run
        simp [Word.concat]
        simp [RunRegularGrammarSub]
        have hll : ∃ t1, (t1 = qn) ∧ (RunRegularGrammarSub t1 q22 (ConstructRegularGrammarFromDFA dfa) run {data := xs}) := 
          by exists qn
        simp [hll]
        have inDelta := abl1.left
        simp [Set.element, ConstructRegularGrammarFromDFA]
        apply Or.inl
        exists q11 
        exists x 
        exists qn

theorem notExistsEqAllSpecial : (¬∃ (runx : Word α × Word α) (runxs : List (Word α × Word α)), run2 = runx::runxs) → ∀ (runx : Word α × Word α) (runxs : List (Word α × Word α)), ¬run2 = runx::runxs := by
  intro h1
  intro h2
  intro h3
  intro ab
  have existsS : ∃ (runx : Word α × Word α) (runxs : List (Word α × Word α)), run2 = runx::runxs := by 
    exists h2 
    exists h3
  exact h1 existsS

theorem deriviationsEQ2 {α : Type u} (dfa: @ DFA α) (w: Word α) : 
     ∀ q1 q2,(∃ run,
      (RunRegularGrammarSub q1 q2 (ConstructRegularGrammarFromDFA dfa) run w))-> (nfaDerivation dfa.toNFA q1 q2 w) := by
  have hp := Word.objects_equal w 
  rw [← hp] 
  induction w.data with
  | nil => 
    intro q1
    intro q2
    intro runex
    match runex with 
    | ⟨run, runwo⟩ =>
      simp [RunRegularGrammarSub] at runwo 
      simp [nfaDerivation, runwo]
  | cons x xs iv => 
    intro q11
    intro q22
    intro runex
    match runex with 
    | ⟨run2, runwo⟩ =>
      cases (Classical.em (∃ runx runxs, run2 = runx::runxs)) with 
      | inl runwoH =>
        match runwoH with 
        | ⟨runx, runxs, runwoH2⟩ =>
          simp [runwoH2, RunRegularGrammarSub] at runwo 
          simp [nfaDerivation]
          have runwo2 := runwo.right.right 
          match runwo2 with
          | ⟨qn, runwo3⟩ =>
            exists qn
            have runwo4ex : ∃ run, RunRegularGrammarSub qn q22 (ConstructRegularGrammarFromDFA dfa) run {data := xs} := by
              exists runxs 
              exact runwo3.right
            have iv2 := iv qn q22 runwo4ex
            simp [iv2]
            have pinG := runwo.left
            have runFirst := runwo.right.left 
            have runRight := runwo3.left
            simp [Set.element, ConstructRegularGrammarFromDFA] at pinG 
            cases pinG with 
            | inl hll =>
              match hll with 
              | ⟨q_1, w_1, q_r, pingnoE⟩ => 
                simp [Word.concat, runFirst, ←runRight] at pingnoE
                simp [pingnoE]
            | inr hrr =>
              match hrr with
              | ⟨q, hrr2⟩ =>
                have falseelimarg := hrr2.right.left
                simp [← runRight] at falseelimarg
      | inr hnexrun => 
        have runeqempty : run2 = [] := by
          apply EmptyNotFull
          have hn : (¬∃ runx runxs, run2 = runx::runxs) → (∀ runx runxs, ¬(run2 = runx::runxs)) := by
            intro h
            apply notExistsEqAllSpecial
            exact h
          apply hn
          exact hnexrun
        simp [runeqempty] at runwo
        simp [RunRegularGrammarSub] at runwo

theorem languageDFAeqConstructedRegularGrammar2 {α : Type u} (dfa : @DFA α) : (@nfaLanguage α dfa.toNFA) = (@LanguageRegularGrammar α (ConstructRegularGrammarFromDFA dfa)) := by 
  apply Set.setext
  intro w
  apply Iff.intro
  intro wInNFALanguage
  simp [Set.element, nfaLanguage] at wInNFALanguage
  match wInNFALanguage with
  | ⟨qs, qn, wInNFALanguage2⟩ =>
    simp [Set.element, LanguageRegularGrammar]
    exists qn
    have runExists := deriviationsEQ1 dfa w qs qn wInNFALanguage2.right.right
    match runExists with
    | ⟨run, runExists2⟩ =>
      exists run 
      have qsEqConstructedGrammarS : (ConstructRegularGrammarFromDFA dfa).toGrammar.S = qs := by
        simp [ConstructRegularGrammarFromDFA]
        have bedQ0 := dfa.bed_Q0
        have h := wInNFALanguage2.left
        rw [bedQ0] at h
        exact h
      rw [qsEqConstructedGrammarS]
      simp [runExists2]
      have qnToEpsilon : Grammar.P (ConstructRegularGrammarFromDFA dfa).toGrammar ({data := [qn]}, {data := []}) := by
        have qnInF := wInNFALanguage2.right.left
        simp [ConstructRegularGrammarFromDFA] 
        apply Or.inr
        exists qn
      simp [qnToEpsilon]
  intro wInGrammarLanguage
  simp [Set.element, LanguageRegularGrammar] at wInGrammarLanguage
  match wInGrammarLanguage with
  | ⟨qn, run, wInGrammarLanguage2⟩ =>
    have kfalse : (∃ w1 z,
    w = w1 ∘ {data := [z]} ∧
      RunRegularGrammarSub (ConstructRegularGrammarFromDFA dfa).toGrammar.S qn (ConstructRegularGrammarFromDFA dfa)
          run w1 ∧
        Grammar.P (ConstructRegularGrammarFromDFA dfa).toGrammar ({data := [qn]}, {data := [z]})) -> False := by
      
      intro kfalse2
      match kfalse2 with
      | ⟨w1, z, kfalse3⟩ =>
        have kfalse4 := kfalse3.right.right 
        simp [ConstructRegularGrammarFromDFA] at kfalse4
        cases (kfalse4) with
        | inl hl =>
          match hl with
          | ⟨ql, a, qr, hl2⟩ =>
            have hl3 := hl2.right.left
            simp [Word.concat] at hl3 
        | inr hr => 
          match hr with
          | ⟨_, hr2⟩ =>
            exact hr2
    cases (wInGrammarLanguage2) with 
    | inl hl =>
      simp [Set.element, nfaLanguage]
      have bed : (∃ run, (RunRegularGrammarSub (ConstructRegularGrammarFromDFA dfa).toGrammar.S qn (ConstructRegularGrammarFromDFA dfa) run  w)) := by
        exists run
        simp [hl.left]
      have q2 := deriviationsEQ2 dfa w (ConstructRegularGrammarFromDFA dfa).toGrammar.S qn bed
      exists (ConstructRegularGrammarFromDFA dfa).toGrammar.S 
      exists qn
      simp [q2]
      simp [ConstructRegularGrammarFromDFA]
      have hlr := hl.right
      simp [ConstructRegularGrammarFromDFA] at hlr
      cases hlr with
      | inl hl5 =>
        match hl5 with 
        | ⟨ql, a, qr, hl51⟩ => 
          have q0InQ0 := dfa.bed_Q0
          rw [q0InQ0]
          simp [hl51.left]
          have hfalse := hl51.right.left
          simp [Word.concat] at hfalse
      | inr hl6 =>
        match hl6 with
        | ⟨qz, hl7⟩ => 
          rw [Set.element] at hl7
          simp [hl7.left, hl7.right]
          have q0InQ0 := dfa.bed_Q0
          rw [q0InQ0]
    | inr hr =>
      have kfalse2 := kfalse hr
      apply False.elim
      exact kfalse2
    