open Classical


theorem Or.distrib_and : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=   
  Iff.intro
  (fun hpqr : p ∨ (q ∧ r) =>
    Or.elim hpqr
    (fun hp:p => show (p ∨ q) ∧ (p ∨ r) from ⟨(Or.intro_left q hp), (Or.intro_left r hp)⟩)
    (fun hqr:(q ∧ r) => show (p ∨ q) ∧ (p ∨ r) from ⟨(Or.intro_right p hqr.left), (Or.intro_right p hqr.right)⟩))
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
      (fun hq : q => show ¬p ∨ ¬q from False.elim (hpq ⟨hp, hq⟩ ))
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
  (  fun hpq : ¬p ∨ q =>
    Or.elim hpq
    (fun hnp: ¬p => 
      fun hp:p => show q from False.elim (hnp hp))
    (fun hq: q => 
      fun hp:p => hq))
  (  fun hpq : (p → q) =>
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





--------------------------------------------------------------------
structure Word (α : Type u) where
  data : List α
  deriving Repr

def Word.concat {α : Type u} (x y : Word α) : Word α := { data := x.data ++ y.data }
infixr:70 " ∘ " => Word.concat

def Set (α : Type u) := α -> Prop

def Set.element {α : Type u} (e : α) (X : Set α) : Prop := X e
infixr:75 " ∈ " => Set.element

def Set.union {α : Type u} (X Y : Set α) : Set α := fun a => a ∈ X ∨ a ∈ Y
infixr:65 " ∪ " => Set.union

def Set.subset {α : Type u} (X Y : Set α) : Prop := ∀ e : α, e ∈ X → e ∈ Y
infixr:50 " ⊆ " => Set.subset

def Set.intersection {α : Type u} (X Y : Set α) : Set α  := fun (e: α) => e ∈ X ∧ e ∈ Y
infixr:80 " ∩ " => Set.intersection

def Set.diff {α : Type u} (X Y : Set α) : Set α  := fun (e: α) => e ∈ X ∧ ¬(e ∈ Y)
--infixr:80 " \\ " => Set.intersection

def Set.empty {α :Type u}: Set α := fun _ => False

notation (priority := high) "∅" => Set.empty


def Language (α : Type u) := Set (Word α)

def Language.concat {α : Type u} (X Y : Language α) : Language α := fun w : Word α => ∃ u v : Word α, u ∈ X ∧ v ∈ Y ∧ w = u ∘ v
infixr:70 " ∘ₗ " => Language.concat


------------------------------------------------------------------------------------


def Word.epsilon {α : Type u} : Word α := Word.mk List.nil
notation (priority := high) "ε" => Word.epsilon

def Word.len {α : Type u} (w:Word α) : Nat :=
  match w with 
  | Word.mk List.nil => 0
  | Word.mk (x::xs) => 1 + Word.len (Word.mk (xs))

def Language.epsilon {α:Type u} : Language α :=
  fun w =>
  match w with
  | Word.mk List.nil => True
  | Word.mk (_::_) => False

def Language.power {α : Type u} (n:Nat) (X: Language α ) : Language α  := 
  match n with
  | 0 => 
    Language.epsilon
  | (Nat.succ m) => 
    fun (w:Word α)  => 
      ∃ w1 w2 : Word α , w2 ∈ (Language.power m X) ∧ w1 ∈ X ∧ w = w1 ∘ w2

def Language.kleene {α :Type u} (X: Language α ) : Language α :=
  fun w: Word α =>
    ∃ n : Nat , w ∈ Language.power n X

def Language.plus {α :Type u} (X :Language α ) : Language α :=
  fun w: Word α => ∃ n:Nat , ¬ (n = 0) ∧ w ∈ Language.power n X

def Sigma.language {α : Type u}: Language α := 
  fun w: Word α =>
    match w with
    | (Word.mk (_::[])) => True
    | _ => False

def Sigma.kleene {α :Type u}: Language α :=
  fun w: Word α => (@Language.kleene _ Sigma.language) w
      
def Language.complement {α :Type u} (X: Language α ) : Language α  :=
  fun w: Word α =>
  --braucht man sigma kleene w hier? eigentlich kann ein wort hier eh nur über sigma sein, ist das nicht schon zu limitierend ->-es sind keine wörter aus nicht alpha zugelassen , sinnvoll?
    ¬(w ∈ X)

-- inductive TypeUnion (α : Type u) (β : Type v) where
--   | first (whatever : α) : TypeUnion α β
--   | second (whatever : β) : TypeUnion α β


-- structure Grammar2 {V : Type v} {E : Type u} where 
--   P : Set ((Word (TypeUnion V E)) × (Word (TypeUnion V E)))
--   S : V
--   bed2: ∀ pair : (Word (TypeUnion V E)) × (Word (TypeUnion V E)), 
--   -- wenn pair in p folgt dass es die bedingungen hat sonst keine einschränkung
--     ¬ P pair ∨ (
--       ∃ v1 v2 v3 : Word (TypeUnion V E), 
--         ((pair.fst) = (v1 ∘ v2 ∘ v3)) 
--         -- TODO v2 soll (ein Wort) über V sein
--         ∧ ∃ t, t = TypeUnion.first v2 
--         ∧ ¬(v2 = Word.epsilon) 
--     )

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


namespace Set
theorem setext {α :Type u} {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
 funext (fun x => propext (h x))


theorem inter_self {α :Type u} (a : Set α) : a ∩ a = a := by
  apply setext
  intro x
  constructor
  intro n 
  rw [Set.element, Set.intersection] at n
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

theorem inter_comm {α : Type u} (X Y:Set α ) : X ∩ Y = Y ∩ X := by 
  apply setext 
  intro x 
  constructor 
  intro n 
  rw [Set.element, intersection] at n
  rw [Set.element, intersection]
  exact ⟨n.right, n.left ⟩ 
  intro n 
  rw [Set.element, intersection] at n
  rw [Set.element, intersection]
  exact ⟨n.right, n.left ⟩ 


theorem union_or {α : Type u} (X Y : Set α) (e : α) : (e ∈ (X ∪ Y)) = (e ∈ X ∨ e ∈ Y) := by rfl

theorem union_comm {α :Type u} (X Y : Set α ) : X ∪ Y = Y ∪ X :=
  by
  apply funext
  intro f
  rw [Set.union]
  rw [Set.union]
  rw [Or.comm]



theorem empty_inter {α :Type u} (a : Set α) : ∅ ∩ a = ∅ := by 
  rw [inter_comm]
  apply inter_empty  


end Set




theorem Set.intersection_and {α : Type u} (X Y : Set α) (e:α ) : (e ∈ (X ∩ Y)) = (e ∈ X ∧ e ∈ Y) := by rfl

theorem Set.union_dist_intersection {α : Type u} (X Y Z : Set α) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  apply funext
  intro x
  rw [Set.union, Set.intersection]
  repeat rw [Set.element]
  rw [Set.union, Set.union, Set.intersection]
  rw [Or.distrib_and]
  rfl

theorem Set.intersection_dist_union {α : Type u} (X Y Z : Set α) : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  apply funext
  intro x
  rw [Set.intersection, Set.union]
  repeat rw [Set.element]
  rw [Set.union, Set.intersection, Set.intersection,And.distrib_or]
  rfl

theorem Word.objects_equal {α : Type u} (w :Word α ): Word.mk w.data  = w := by rfl 

@[simp] theorem Word.epsilon_eq_epsilon {α : Type u} : (@ε α)  = (Word.mk List.nil)  := by rfl 


theorem eps_element_only_element_in_eps_lang_il {α :Type u} (w : Word α ) : Language.epsilon w -> w = { data := [] } := by
intro n
rw  [← Word.objects_equal w] at n
cases h:w.data with
| nil =>
  rw [h] at n 
  rw [← Word.objects_equal w]
  rw [h]
| cons a as =>
  rw [h] at n
  simp [Language.epsilon] at n



theorem eps_element_only_element_in_eps_lang {α :Type u} {w: Word α } : w ∈ Language.epsilon ↔ (w = Word.mk []) := by
constructor
exact eps_element_only_element_in_eps_lang_il w
intro n 
simp [Set.element,n, Language.epsilon]

#check Set.setext

theorem Langauge.kleene_eq_diff_eps {α :Type u} {X: Language α } :Language.kleene X = Language.kleene ( Set.diff X Language.epsilon) := by 
  apply Set.setext 
  intro x 
  apply Iff.intro
  intro n 
  repeat (first | rw [Language.kleene]| rw [Set.diff]| rw [Set.element])
  repeat (first | rw [Language.kleene] at n| rw [Set.element] at n) 
  match n with 
  | ⟨n1,h3 ⟩ =>
    cases h:n1
    rw [h] at h3
    rw [Set.element, Language.power] at h3
    exists 0
    exists n1
    rw [h]
    rw [Set.element, Language.power]
    rw [h] at h3
    rw [Set.element, Language.power] at h3
    match h3 with 
    | ⟨w1,w2, hh3 ⟩ => 
      exists w1
      exists w2
      simp [Set.element,  Set.diff]
      sorry
    sorry




--TODO : nachfragen




theorem Language.kleene_eq_plus_eps {α :Type u} {X: Language α } :  Language.plus X ∪ Language.epsilon = Language.kleene X := by 
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
      exact ⟨ Nat.succ_ne_zero m, r ⟩ 
    | zero => 
      apply Or.inr
      simp [Set.element] at r
      simp [ Language.power] at r
      simp [Set.element]
      exact r 






theorem list_concat_empty {α :Type u} (as : List α ) : as ++ [] = as := by
simp [List.cons]


theorem Language.lan_eps_eq_lan {α : Type u} (L : Language α ): L ∘ₗ Language.epsilon =  L := by
  apply funext
  intro w
  apply propext
  constructor
  rw  [Language.concat]
  intro ⟨u,v, h1, h2, h3⟩
  rw [Word.concat] at h3
  rw [Set.element] at h1
  rw [eps_element_only_element_in_eps_lang] at h2
  simp [h2] at h3
  rw [(Word.objects_equal u)] at h3
  simp [*]
  intro n 
  rw  [Language.concat]
  exists w 
  exists Word.mk []
  apply And.intro 
  exact n 
  apply And.intro 
  rw [Set.element]
  simp  [Word.epsilon, Language.epsilon ]
  simp [Word.concat]


theorem Language.eps_lan_eq_lan {α : Type u} (L : Language α ): Language.epsilon ∘ₗ L =  L := by
  apply funext
  intro w
  apply propext
  constructor
  rw  [Language.concat]
  intro ⟨u,v, h1, h2, h3⟩
  rw [Word.concat] at h3
  rw [eps_element_only_element_in_eps_lang] at h1
  simp [h2] at h3
  rw [Set.element] at h2
  simp [h1,Word.objects_equal] at h3
  simp [*]
  intro n 
  rw  [Language.concat]
  exists  (Word.mk [])
  exists w



theorem Language.empty_lan_eq_empty {α :Type u} (L : Language α ) : L ∘ₗ ∅ = ∅ := by
  apply Set.setext 
  intro w 
  constructor
  intro n 
  rw [Set.element, Language.concat] at n 
  match n with 
  | ⟨u,v,h1,h2,h3 ⟩ =>
    rw [Set.element, Set.empty] at h2
    apply False.elim h2 
  intro n 
  rw [Set.element, Set.empty] at n
  apply False.elim n 


theorem Language.lan_empty_eq_empty {α :Type u} (L : Language α ) : ∅ ∘ₗ L = ∅ := by
  apply Set.setext 
  intro w 
  constructor
  intro n 
  rw [Set.element, Language.concat] at n
  match n with 
  | ⟨u,v, h1,h2,h3⟩ => 
    rw [Set.element, Set.empty ] at h1
    apply False.elim h1 
  intro n 
  rw [Set.element, Set.empty ] at n 
  apply False.elim n 



theorem Language.concat_dist_union_r {α : Type u} (L1 L2 L3 : Language α) : (L1 ∪ L2) ∘ₗ L3 = (L1 ∘ₗ L3) ∪ (L2 ∘ₗ L3) := by
  apply Set.setext 
  intro w 
  constructor 
  intro n 
  rw [Set.element, Language.concat] at n
  match n with 
  | ⟨u,v,h1,h2,h3 ⟩ => 
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
    | ⟨u,v,h1,h2,h3 ⟩ =>
      exists u
      exists v 
      rw [Set.element,Set.union]
      exact ⟨ Or.inl h1, h2,h3 ⟩ 
  |inr hr => 
    rw [Set.element, Language.concat]
    rw [Set.element, Language.concat] at hr 
    match hr with 
    | ⟨u,v,h1,h2,h3 ⟩ =>     
      exists u
      exists v
      exact ⟨ Or.inr h1, h2, h3 ⟩ 
      

theorem Language.morgan_union {α : Type u} (L1 L2 : Language α) : (L1 ∪ L2) = Language.complement (Language.complement L1 ∩ Language.complement L2):= by
  apply Set.setext
  intro w 
  repeat (first | rw [Set.element ] | rw [Set.union] | rw [Set.intersection] | rw [Set.union] |rw [Language.complement]  )
  rw [← Or.morgan, not_not_p]  constructor
  repeat (first | intro n | exact n)

theorem Language.morgan_inter {α : Type u} (L1 L2: Language α ) : (L1 ∩ L2) = Language.complement (Language.complement L1 ∪ Language.complement L2) := by 
  apply Set.setext 
  intro w 
  repeat (first | rw [Set.element ] | rw [Set.union] | rw [Set.intersection] | rw [Set.union] |rw [Language.complement]  )
  rw [← And.morgan, not_not_p]
  constructor
  repeat (first | intro n | exact n)



----------------------------------------------------------------------------
      





theorem concat_dist_union_l {α : Type u} (L1 L2 L3 : Language α) :
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
  -- constructor
  -- intro _
  -- simp []
  -- intro _
  -- simp []
  

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
      ∃ v1 v2 v3 : Word α , 
        ((pair.fst) = (v1 ∘ v2 ∘ v3)) ∧ 
        (∃ t: α  , (Word.mk ([t]) = v2 ∧ t ∈ V ))
    )

structure RegularGrammar {α  : Type u} extends (@Grammar α) where
  bed_reg: ∀ pair : ((Word α) × (Word α)), 
    (pair  ∈ P) -> 
    (
      (∃ t: α  , (Word.mk [t] = pair.fst) ∧ t ∈ V ) ∧ (
        (∃ t1 t2 : α , (Word.mk [t1, t2] = pair.snd) ∧ t1 ∈ E ∧ t2 ∈ V) ∨ 
        (∃ t: α  , Word.mk [t] = pair.snd ∧ t ∈ E ) ∨ 
        pair.snd = Word.mk []
      )
    )


-- structure RegularGrammar2 {V : Type v} {E : Type u} extends (@Grammar V E) where
--   bed1 : ∀ pair : (Word (TypeUnion V E)) × (Word (TypeUnion V E)), pair.first ∈ V
--   bed3 : ∀ pair : (Word (TypeUnion V E)) × (Word (TypeUnion V E)), 
--     (∃ v1 v2: TypeUnion V E, 
--       ((pair.second) = ({data := List.cons v1 List.nil}) ∘ ({data := List.cons v2 List.nil}))
--       ∧ (v1 ∈ E) ∧ (v2 ∈ V))
--     ∨ (pair.second ∈ E) 
--     ∨ (pair.second = {data := []}) 


structure EpsilonFreeRegularGrammar {α  : Type u} extends (@RegularGrammar α ) where
  epsilonFree : ∀ pair : (Word α ) × (Word α), 
  ¬ (pair  ∈ P) ∨ (
    pair.fst = Word.mk ([S]) ∨ ¬ (pair.snd = Word.epsilon)
  )

def AllElementsOfWordInSet {α : Type u} (w: Word α) (S: Set α ) :=
  match w with 
  | Word.mk (a::as)  => a ∈ S ∧ AllElementsOfWordInSet (Word.mk as) S
  | _ => True

def EinSchrittableitungsregel {α : Type u} (G : @Grammar α) (w : Word α) (v : Word α) : Prop :=
    ∃ w1 w2 w3: Word α ,
      ∃ v1 v2 v3: Word α ,
      have p1 := w = w1 ∘ w2 ∘ w3
      have p2 := v = v1 ∘ v2 ∘ v3
      (v1 = w1) ∧ (v3 = w3) ∧ p1 ∧ p2 ∧ G.P ⟨w2, v2⟩
        
def NSchrittableitungsregel {α : Type u} (G : @Grammar α ) (w : Word α ) (v : Word α ) (n:Nat) : Prop :=
  match n with
  | 0 => 
    w = v
  | (Nat.succ m) => 
      ∃ w1 : Word α , (EinSchrittableitungsregel G w w1) ∧ (NSchrittableitungsregel G w1 v m) ∧ (AllElementsOfWordInSet v G.E)


def SternSchrittableitungsregel {α : Type u} (G : @Grammar α ) (w : Word α ) (v : Word α ) : Prop :=
  ∃ n : Nat , NSchrittableitungsregel G w v n
  



def ErzeugteSpracheGrammar {α : Type u} (G : @Grammar α): Language α  :=
  fun w: Word α  => 
    SternSchrittableitungsregel G (Word.mk [G.S]) w 


structure NFA {α : Type u} where 
  Q : Set α 
  E : Set α 
  δ : Set ((α × α) × α)
  Q0 : Set α 
  F: Set α
  QEdisj: Q ∩ E = ∅ 
  Q0subset: Q0 ⊆  Q 
  Fsubset: F ⊆ Q
  Tfunction: 
    ∀ t : ((α × α) × α),
       ¬ (t ∈ δ) ∨ (
          t.fst.fst ∈ Q ∧ 
          t.fst.snd ∈ E ∧ 
          t.snd ∈ Q
       ) 
  

structure DFA {α : Type u} extends (@ NFA α ) where 
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
        (¬ ( t1.fst = t2.fst) ∨ t1.snd = t2.snd)

def nfaAbleitung {α : Type u} (nfa: @ NFA α ) (q1 qf: α) (w: Word α ) : Prop :=
  match w with 
  | Word.mk (x::xs) =>  ∃ qn , nfa.δ ⟨⟨q1 , x ⟩,qn ⟩ ∧ nfaAbleitung nfa qn qf (Word.mk xs) 
  | Word.mk [] => q1 = qf

def nfaSprache {α : Type u} (nfa: @ NFA α ) : Language α :=
  fun w => ∃ qs qf, qs ∈ nfa.Q0 ∧ qf ∈ nfa.F ∧ nfaAbleitung nfa qs qf w  




def EinSchrittableitungsregelNFA {α : Type u} {dfa: @ NFA α } (q1 : α) (q2 : α ) (w : Word α) (v: Word α) : Prop :=
      q1 ∈ dfa.Q  ∧ q1 ∈ dfa.Q ∧ 
      ∃ w1: Word α , 
      (AllElementsOfWordInSet w1 dfa.E ∧ 
      ∃ a : α, 
        w = w1 ∘ (Word.mk [a]) ∧ v = w1 ∧ ⟨⟨q1, a⟩, q2⟩ ∈ dfa.δ 
      )
      ∨ (q1 = q2 ∧ w = Word.epsilon ∧ v = Word.epsilon)

def NSchrittableitungsregelNFA {α : Type u} {dfa: @ NFA α } (q1 : α) (q2 : α ) (w : Word α) (v: Word α) (n:Nat) : Prop :=
  match n with 
  | (Nat.succ m) => 
    ∃wz : Word α, 
      ∃qz : α ,  qz ∈ dfa.Q ∧ 
    @EinSchrittableitungsregelNFA α dfa q1 qz  w wz ∧ 
    @NSchrittableitungsregelNFA α dfa qz q2 wz v m 
  | _ => w = v ∧ q1 = q2

def SternSchrittableitungsregelNFA {α : Type u} {dfa: @ NFA α } (q1 : α) (q2 : α ) (w : Word α) (v: Word α): Prop :=
  ∃ n:Nat,
    @NSchrittableitungsregelNFA α dfa q1 q2 w v n

def NFASprache {α : Type u} (dfa: @ NFA α ) : Language α :=
  fun w: Word α => 
    ∃ f s, f ∈ dfa.F ∧ s ∈ dfa.Q0 ∧ 
    @SternSchrittableitungsregelNFA α dfa s f w Word.epsilon

structure TotalerDFA {α : Type u} extends (@ DFA α) where 
  tot: ∀ t : ((α × α) × α),
  ( ¬ (t.fst.snd ∈ E ∧ t.fst.fst ∈ Q) ∨ 
    ∃ q2 : α , ⟨⟨t.fst.fst, t.fst.snd ⟩,  q2⟩ ∈ δ
  )


def ConstructRegularGrammarOutOfDFA {α : Type u} (dfa: @ DFA α ) : @RegularGrammar α:= 
  let E : Set α := dfa.E
  have E_def_refl : E = dfa.E := by rfl
  
  let V : Set α := dfa.Q
  have V_def_refl : V = dfa.Q := by rfl
  
  let S : α := dfa.q0
  have S_def_refl : S = dfa.q0 := by rfl
  
  let P : Set ((Word α) × (Word α)) := 
    fun rule : (Word α) × (Word α) => 
      (∃ql a qr : α , rule.fst = Word.mk [ql] ∧ rule.snd = Word.mk [a] ∘ Word.mk [qr] ∧ ⟨⟨ql,a⟩,qr⟩ ∈ dfa.δ)
      ∨ (∃q a qf : α , rule.fst = Word.mk [q] ∧ rule.snd = Word.mk [a] ∧ qf ∈ dfa.F ∧ ⟨⟨q,a⟩,qf⟩ ∈ dfa.δ)
      ∨ (rule.fst = Word.mk [S] ∧ rule.snd = Word.epsilon ∧ S ∈ dfa.F)
  have P_def_refl : P = fun rule : (Word α) × (Word α) => 
      (∃ql a qr : α , rule.fst = Word.mk [ql] ∧ rule.snd = Word.mk [a] ∘ Word.mk [qr] ∧ ⟨⟨ql,a⟩,qr⟩ ∈ dfa.δ)
      ∨ (∃q a qf : α , rule.fst = Word.mk [q] ∧ rule.snd = Word.mk [a] ∧ qf ∈ dfa.F ∧ ⟨⟨q,a⟩,qf⟩ ∈ dfa.δ)
      ∨ (rule.fst = Word.mk [S] ∧ rule.snd = Word.epsilon ∧ S ∈ dfa.F) := by rfl
  
  have bed_VEdisj : V ∩ E = ∅ := by
    have QEdisj := dfa.QEdisj
    simp [E_def_refl, V_def_refl]
    exact QEdisj
  
  have bed_SinV: S ∈ V := by
    -- exact adf
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
      ∃ v1 v2 v3 : Word α , 
        ((pair.fst) = (v1 ∘ v2 ∘ v3)) ∧ 
        (∃ t: α  , (Word.mk ([t]) = v2 ∧ t ∈ V ))
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
          -- have ql_refl : (ql = ql) ↔ True := by rfl
          -- simp [ql_refl]
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
      cases disjB with
      | inl disj2 =>
        match disj2 with
        | ⟨q, a, qf, disj2woE⟩ => 
          exists Word.mk []
          exists Word.mk [q]
          exists Word.mk []
          simp [Word.concat]
          have k1 := disj2woE.left
          have k2 : ∃ t, t = q ∧ t ∈ V := by
            exists q
            -- have q_refl : (q = q) ↔ True := by rfl
            -- simp [q_refl]
            simp []
            have disj3 := disj2woE.right.right
            rw [Set.element] at disj3
            have Tfunction := dfa.Tfunction
            have Tfunction2 := Tfunction ⟨⟨q, a⟩,qf⟩
            rw [not_or_eq_implication] at Tfunction2
            have Tfunction3 := Tfunction2 disj3.right
            simp [] at Tfunction3
            have Tfunction31 := Tfunction3.left
            exact Tfunction31
          have k1Andk2 := And.intro k1 k2
          exact k1Andk2
      | inr disj3 =>
        exists Word.mk []
        exists Word.mk [S]
        exists Word.mk []
        simp [Word.concat]
        have k1 := disj3.left
        have k2 : ∃ t, t = S ∧ t ∈ V := by
          exists S
        have k1Andk2 := And.intro k1 k2
        exact k1Andk2

  have bed_reg: ∀ pair : ((Word α) × (Word α)), 
    (pair ∈ P) -> 
    (
      (∃ t: α  , (Word.mk [t] = pair.fst) ∧ t ∈ V ) ∧ (
        (∃ t1 t2 : α , (Word.mk [t1, t2] = pair.snd) ∧ t1 ∈ E ∧ t2 ∈ V) ∨ 
        (∃ t: α  , Word.mk [t] = pair.snd ∧ t ∈ E ) ∨ 
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
            -- have ql_refl : (ql = ql) ↔ True := by rfl
            -- simp [ql_refl]
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
          have k2 : ∃ t1 t2 : α , (Word.mk [t1, t2] = pair.snd) ∧ t1 ∈ E ∧ t2 ∈ V := by
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
        cases disjB with
        | inl disj2 =>
          match disj2 with
          | ⟨ql, a, qr, disj2woE⟩ => 
            simp [Word.concat]
            have k1 : ∃ t, t = ql ∧ t ∈ V := by
              exists ql
              -- have ql_refl : (ql = ql) ↔ True := by rfl
              -- simp [ql_refl]
              simp []
              have disj3 := disj2woE.right.right
              rw [Set.element] at disj3
              have Tfunction := dfa.Tfunction
              have Tfunction2 := Tfunction ⟨⟨ql, a⟩,qr⟩
              rw [not_or_eq_implication] at Tfunction2
              have Tfunction3 := Tfunction2 disj3.right
              simp [] at Tfunction3
              have Tfunction31 := Tfunction3.left
              exact Tfunction31
            have k2 : ∃ t: α , Word.mk [t] = pair.snd ∧ t ∈ E := by 
              exists a
              have disj3 := disj2woE.right.right
              have Tfunction := dfa.Tfunction
              have Tfunction2 := Tfunction ⟨⟨ql, a⟩,qr⟩
              rw [not_or_eq_implication] at Tfunction2
              have Tfunction3 := Tfunction2 disj3.right
              simp [] at Tfunction3
              have Tfunction31 := Tfunction3.right.left
              rw [E_def_refl]
              simp [disj2woE.right.left, Tfunction31]
            simp [k2]
            exists ql
            simp [disj2woE.left]
            match k1 with 
            | ⟨qrr, k2woE⟩ =>
            simp [←k2woE.left, k2woE.right]
        | inr disj3 =>
          have k1 : (∃ t, { data := [t] } = pair.fst ∧ t ∈ V) := by
            exists S
            simp [disj3.left, bed_SinV]
          have k2 : pair.snd = { data := [] } := by 
            simp [disj3.right.left]
          simp [k1, k2]

    { V := V, E := E, S := S, P := P, bed_VEdisj := bed_VEdisj, bed_SinV := bed_SinV, bed_VarInLeft := bed_VarInLeft, bed_reg := bed_reg : RegularGrammar}


#check NSchrittableitungsregel

theorem RGwordlengthEQn {α : Type u} (G : RegularGrammar α ) (w1 w2 : Word α) (n : Nat) : 
  NSchrittableitungsregel G w1 w2 n → (n = (Word.len w2 - Word.len w1) + 1) ∨ (n = (Word.len w2 - Word.len w1) + 2) := sorry
  -- S-> eps  n = 1 diff = -1
  -- S-> a    n = 1 diff = 0
  -- S ->* abcd diff = 3

theorem languageDFAeqConstructedRegularGrammar {α : Type u} (dfa : @DFA α) : (@ErzeugteSpracheGrammar α (ConstructRegularGrammarOutOfDFA dfa).toGrammar) = (@NFASprache α dfa.toNFA) := by 
  apply Set.setext
  intro word
  apply Iff.intro
  intro wees
  rw [Set.element, ErzeugteSpracheGrammar, SternSchrittableitungsregel] at wees
   match wees.left with
  | ⟨n1, weesn1⟩ =>
    cases (Classical.em (n1 = 0)) with
    | inl n0 => 
      simp [n0, NSchrittableitungsregel, ConstructRegularGrammarOutOfDFA] at weesn1
      simp [Set.element, NFASprache]
      exists dfa.q0, dfa.q0
      have weesr := wees.right
      simp [← weesn1, AllElementsOfWordInSet, ConstructRegularGrammarOutOfDFA] at weesr
      have qoinQ := dfa.bed_Q0
      have nfa := dfa.toNFA
      have QEdisj :=  dfa.QEdisj
      have Q0sbQ :=  dfa.Q0subset
      have q0inQ0 : dfa.q0 ∈ dfa.Q0 := by
        simp [qoinQ, Set.element]
      have q0inQ : dfa.q0 ∈ dfa.Q := by
        simp [Set.element]
        apply Q0sbQ
        exact q0inQ0
      have setEmpty_rfl : @Set.empty α = (fun _ => False) := by rfl
      have hff : (dfa.toNFA.Q ∩ dfa.toNFA.E) dfa.q0 →  False := by
        intro n 
        rw [QEdisj, setEmpty_rfl] at n
        exact n 
      simp [Set.intersection, q0inQ] at hff
      apply False.elim (hff weesr)
    | inr nsucc =>
      simp [Set.element, NFASprache]
      let (Nat.succ m) := n1
      simp [nsucc, NSchrittableitungsregel] at weesn1
      
      

def TotalerDFAConstruct {α : Type u} (dfa: @ DFA α ) (fang: α ) (p1: ¬fang ∈ dfa.Q ∧ ¬fang ∈ dfa.E) : @TotalerDFA α :=
  let Q2: Set α  := fun w => (w ∈ dfa.Q) ∨ (w=fang) 
  let δ2: Set ((α × α) × α) := fun ⟨⟨ w1, w2⟩ , w3⟩  => ⟨ ⟨ w1, w2⟩ , w3⟩  ∈ dfa.δ ∨ (¬ (∃ a : α ,⟨ ⟨ w1, w2⟩ , a⟩ ∈ dfa.δ )∧ Q2 w1 ∧ dfa.E w2 ∧ w3 = fang)
  
  have delta_def_rfl : ( fun ⟨⟨ w1, w2⟩ , w3⟩  => ⟨ ⟨ w1, w2⟩ , w3⟩  ∈ dfa.δ ∨ (¬ (∃ a : α ,⟨ ⟨ w1, w2⟩ , a⟩ ∈ dfa.δ )∧ Q2 w1 ∧ dfa.E w2 ∧ w3 = fang) ) = δ2 := 
    by rfl

  have Q2_def_rfl : ((fun w => (w ∈ dfa.Q) ∨ (w=fang)):(Set α )) = Q2 := 
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
    -- rw [@And.comm]
    simp [And.distrib_or, Set.element]
    have hq := dfa.QEdisj
    simp [Set.intersection, setEmpty_rfl] at hq
    have hp : ((fun e => e ∈ dfa.Q ∧ e ∈ dfa.E) = fun x => False) → (∀e : α, (e ∈ dfa.Q ∧ e ∈ dfa.E) = False):= by
      intro _
      intro n
      rw [←Set.intersection, dfa.QEdisj, Set.empty]
    have hl := hp hq
    have hll := hl x
    simp [Set.element] at hll
    rw [And.comm] at hll
    -- simp [hll]
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
    have dfa_subset :=  dfa.Q0subset
    simp [Set.subset]
    intro n 
    have hl := QSubsetQ2
    rw [Set.subset ] at hl 
    have hll := hl n 
    rw [Set.subset ] at dfa_subset
    have hrr := dfa_subset n 
    intro x 
    exact hll (hrr x)



  have FSubsetQ2: (dfa.F ⊆ Q2) := by
    have dfa_subset :=  dfa.Fsubset
    simp [Set.subset]
    intro n 
    have hl := QSubsetQ2
    rw [Set.subset ] at hl 
    have hll := hl n 
    rw [Set.subset ] at dfa_subset
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
       | ⟨⟨qs,b⟩ , qz⟩ => 
          have hsorry2 : ⟨ ⟨ qs, b⟩ , qz⟩ ∈ dfa.toNFA.δ ∨ ((¬ (∃ a : α ,⟨ ⟨ qs, b⟩ , a⟩ ∈ dfa.δ ) )∧ Q2 qs ∧ NFA.E dfa.toNFA b ∧  (qz = fang)) := by 
            simp [Set.element, ← delta_def_rfl] at triple_in_delta2
            exact triple_in_delta2
          have hsorry : ⟨ ⟨ qs, b⟩ , qz⟩ ∈ dfa.toNFA.δ ∨ (Q2 qs ∧ NFA.E dfa.toNFA b ∧  (qz = fang)):= by 
            apply Or.elim hsorry2
            intro x 
            apply Or.inl
            exact x
            intro x 
            apply Or.inr 
            simp [x]
          simp[Set.element]
          have dfa_tfun := dfa.Tfunction
          have dfa_tfun_w := dfa_tfun ⟨ ⟨ qs, b⟩ , qz⟩ 
          simp [Set.element] at dfa_tfun_w 
          repeat rw [←Set.element] at dfa_tfun_w
          simp [not_or_eq_implication] at dfa_tfun_w
          have k1 : Q2 qs := by
            cases (Classical.em (dfa.δ ⟨⟨qs,b⟩ , qz⟩)) with 
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
            cases (Classical.em (dfa.δ ⟨⟨qs,b⟩ , qz⟩)) with 
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
            cases (Classical.em (dfa.δ ⟨⟨qs,b⟩ , qz⟩)) with 
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
          exact ⟨k1, k2 , k3 ⟩

  have tot2: ∀ t : ((α × α) × α),
  ( ¬ (t.fst.snd ∈ dfa.E ∧ t.fst.fst ∈ Q2) ∨ 
    ∃ q2 : α , ⟨⟨t.fst.fst, t.fst.snd ⟩,  q2⟩ ∈ δ2
  ):= by 
        intro triple
        match triple with 
       | ⟨⟨qs,b⟩ , qz⟩ => 
          simp [not_or_eq_implication]
          intro x
          simp [Set.element, ← delta_def_rfl]
          cases (Classical.em ( ∃y, dfa.δ ⟨⟨qs,b⟩ , y⟩) ) with 
          | inl hl =>
            match hl with 
            | ⟨y, hy ⟩ => 
              exists  y 
              apply Or.inl 
              exact hy 
          | inr hr => 
            exists fang
            have hfang : fang = fang := rfl 
            apply Or.inr 
            exact ⟨hr, x.right, x.left, hfang ⟩

  have uniqueness2 :
      ∀ t1 t2 : ((α × α) × α),
       ¬ ((t1 ∈ δ2) ∧ (t2 ∈ δ2)) ∨ 
        (¬ ( t1.fst = t2.fst) ∨ t1.snd = t2.snd) := by 
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
                have  exa :∃ a , dfa.δ ⟨first2,a ⟩ := by
                  exists qz1
                have hfalse := hNEtransition  exa
                apply False.elim hfalse

            | inr hr1 => 
              cases bed12 with 
              | inl hl1 =>
                have hNEtransition := hr1.left
                rw [← bed2] at hl1
                have  exa :∃ a , dfa.δ ⟨first1,a ⟩ := by
                  exists qz2
                have hfalse := hNEtransition exa
                apply False.elim hfalse
 
              | inr hr2 => 
                have h_right := hr1.right.right.right
                have h_left := hr2.right.right.right
                simp [h_left, h_right]


    {tot := tot2, uniqueness := uniqueness2, Tfunction := Tfunction2, Q0 := dfa.Q0,  Q:= Q2, E := dfa.E, δ := δ2, QEdisj := Q2Edisj, F := dfa.F, Q0subset := Q0SubsetQ2, Fsubset := FSubsetQ2, q0 := dfa.q0, bed_Q0 := dfa.bed_Q0  : TotalerDFA}


def LaufRegularGrammarSub {α : Type u} (ql qg : α) (G : @RegularGrammar α) (lauf: List (Word α × Word α))  (w : Word α) : Prop :=

    match w with 
    | (Word.mk (word::ws1)) =>
      match lauf with 
      | (p1 ::xs) =>
          p1 ∈ G.P ∧ 
          p1.fst = (Word.mk [ql]) ∧ 
          (∃ t1 : α , (Word.mk [word, t1] = p1.snd)   
                  ∧ LaufRegularGrammarSub t1 qg G xs (Word.mk ws1) 
            )
          
      | _ => False 


    | _ => 
      ql = qg
        --  (let p := ⟨Word.mk [ql],  Word.mk [] ⟩
        --  lauf = [p] ∧ G.P p   )
        

theorem ableitungenEQ1 {α : Type u} (dfa: @ DFA α )   (w: Word α ) :  
     ∀ q1 q2 :α , (nfaAbleitung dfa.toNFA q1 q2 w ) -> (
      (∃ lauf, LaufRegularGrammarSub q1 q2 (ConstructRegularGrammarOutOfDFA dfa) lauf  w )):= by
  have hp := Word.objects_equal w 
  rw [← hp] 
  induction w.data with
  | nil => 
    intro q1
    intro q2
    intro ableitung 
    simp [nfaAbleitung] at ableitung 
    exists []
  | cons x xs iv => 
    intro q11
    intro q22
    intro ableitung 
    simp [nfaAbleitung] at ableitung
    match ableitung with
    | ⟨qn, abl1 ⟩ =>
      have hh := iv qn q22 abl1.right 
      simp [ Word.concat]
      match hh with 
      | ⟨lauf, hhz1 ⟩ =>
        exists  ⟨Word.mk [q11] , Word.mk [x,qn]⟩ ::lauf
        simp [Word.concat]
        simp [LaufRegularGrammarSub]
        have hll : ∃ t1, (t1 = qn) ∧ (LaufRegularGrammarSub t1 q22 (ConstructRegularGrammarOutOfDFA dfa) lauf { data := xs }) := 
          by exists qn
        simp [hll]
        have inDelta := abl1.left
        simp [Set.element, ConstructRegularGrammarOutOfDFA]
        apply Or.inl 
        exists q11 
        exists x 
        exists qn


theorem ableitungenEQ2 {α : Type u} (dfa: @ DFA α )   (w: Word α ) :  
     ∀ q1 q2 ,( ∃ lauf,
      ( LaufRegularGrammarSub q1 q2 (ConstructRegularGrammarOutOfDFA dfa) lauf  w ))  -> (nfaAbleitung dfa.toNFA q1 q2 w ) := by
  have hp := Word.objects_equal w 
  rw [← hp] 
  induction w.data with
  | nil => 
    intro q1
    intro q2
    intro laufex
    match laufex with 
    | ⟨ lauf, laufwo ⟩ =>
      simp [LaufRegularGrammarSub] at laufwo 
      simp [nfaAbleitung, laufwo]
  | cons x xs iv => 
    intro q11
    intro q22
    intro laufex
    match laufex with 
    | ⟨ lauf2, laufwo ⟩ =>
      cases (Classical.em ( ∃ laufx laufxs,  lauf2 = laufx:: laufxs )) with 
      | inl laufwoH =>
        match laufwoH with 
        | ⟨laufx, laufxs, laufwoH2 ⟩ =>
          simp [laufwoH2, LaufRegularGrammarSub] at laufwo 
          simp [nfaAbleitung]
          have laufwo2 := laufwo.right.right 
          match laufwo2 with
          | ⟨qn, laufwo3 ⟩ =>
            exists qn
            have laufwo4ex : ∃ lauf,  LaufRegularGrammarSub qn q22 (ConstructRegularGrammarOutOfDFA dfa) lauf { data := xs } := by
              exists laufxs 
              exact laufwo3.right
            have iv2 := iv qn q22 laufwo4ex
            simp [iv2]
            have pinG := laufwo.left
            have laufFirst := laufwo.right.left 
            have laufRight := laufwo3.left
            simp [Set.element, ConstructRegularGrammarOutOfDFA] at pinG 
            cases pinG with 
            | inl hll =>
              match hll with 
              | ⟨q_1, w_1, q_r, pingnoE ⟩ => 
                simp [Word.concat, laufFirst, ←laufRight] at pingnoE
                simp [pingnoE]
            | inr hrr =>
              cases hrr with 
              | inl hrl => 
                match hrl with
                | ⟨q_1, w_1, q_r, pingnoE ⟩ => 
                  have falseelimarg := pingnoE.right.left
                  simp [← laufRight] at falseelimarg
              | inr hrr => 
                have falseelimarg := hrr.right.left
                simp [← laufRight] at falseelimarg
      | inr hnexlauf => 
        have laufeqempty : lauf2 = [] := sorry
        simp [laufeqempty] at laufwo
        simp [LaufRegularGrammarSub] at laufwo
        
   

