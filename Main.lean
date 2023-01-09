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

def Set.intersection {α : Type u} (X Y : Set α) : Set α  := fun (e: α) => e ∈ X ∧  e ∈ Y
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

inductive TypeUnion (α : Type u) (β : Type v) where
  | first (whatever : α) : TypeUnion α β
  | second (whatever : β) : TypeUnion α β


structure Grammar2 {V : Type v} {E : Type u} where 
  P : Set ((Word (TypeUnion V E)) × (Word (TypeUnion V E)))
  S : V
  bed2: ∀ pair : (Word (TypeUnion V E)) × (Word (TypeUnion V E)), 
  -- wenn pair in p folgt dass es die bedingungen hat sonst keine einschränkung
    ¬ P pair ∨ (
      ∃ v1 v2 v3 : Word (TypeUnion V E), 
        ((pair.fst) = (v1 ∘ v2 ∘ v3)) 
        -- TODO v2 soll (ein Wort) über V sein
        ∧ ∃ t, t = TypeUnion.first v2 
        ∧ ¬(v2 = Word.epsilon) 
    )

structure Grammar {α : Type u} where
  V : Set α 
  E : Set α 
  S: α 
  P : Set ((Word α) × (Word α))
  bed : V ∩ E = ∅ ∧ S ∈ V ∧ 
    ¬ P pair ∨ (
      ∃ v1 v2 v3 : Word α , 
        ((pair.fst) = (v1 ∘ v2 ∘ v3)) ∧ 
        (∃ t: α  , (Word.mk ([t]) = v2 ∧ t ∈ E ))
        ∧ ¬(v2 = Word.epsilon) 
    )

structure RegularGrammar {α  : Type u} extends (@Grammar α) where
  bed1 : ∀ pair : ((Word α) × (Word α)), 
    ¬ (pair  ∈ P) ∨ (
      (∃ t: α  , Word.mk ([t]) = pair.fst ∧ t ∈ V ) ∧ 
      (∃ t1 t2 : α , Word.mk ([t1, t2]) = pair.snd ∧ t1 ∈ E ∧ t2 ∈ V) ∧ 
      (∃ t: α  , Word.mk ([t]) = pair.snd ∧ t ∈ E ) ∧ 
      pair.snd = Word.epsilon
    )


structure RegularGrammar2 {V : Type v} {E : Type u} extends (@Grammar V E) where
  bed1 : ∀ pair : (Word (TypeUnion V E)) × (Word (TypeUnion V E)), pair.first ∈ V
  bed3 : ∀ pair : (Word (TypeUnion V E)) × (Word (TypeUnion V E)), 
    (∃ v1 v2: TypeUnion V E, 
      ((pair.second) = ({data := List.cons v1 List.nil}) ∘ ({data := List.cons v2 List.nil}))
      ∧ (v1 ∈ E) ∧ (v2 ∈ V))
    ∨ (pair.second ∈ E) 
    ∨ (pair.second = {data := []}) 


structure EpsilonFreeRegularGrammar {α  : Type u} extends (@RegularGrammar α ) where
  epsilonFree : ∀ pair : (Word α ) × (Word α), 
  ¬ (pair  ∈ P) ∨ (
    pair.fst = Word.mk ([S]) ∨ ¬ (pair.snd = Word.epsilon)
  )


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
      ∃ w1 : Word α , (EinSchrittableitungsregel G w w1) ∧ (NSchrittableitungsregel G w1 v m)


def SternSchrittableitungsregel {α : Type u} (G : @Grammar α ) (w : Word α ) (v : Word α ) : Prop :=
  ∃ n : Nat , NSchrittableitungsregel G w v n


def ErzeugtSprache {α : Type u} (G : @Grammar α): Language α  :=
  fun w: Word α  => 
    SternSchrittableitungsregel G (Word.mk [G.S]) w

structure NFA {α : Type u} where 
  Q : Set α 
  E : Set α 
  δ : Set ((α × α) × α)
  Q0 : Set α 
  F: Set α 
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
  q0: 
  (∃ t : α , Q = 
    (fun a : α => 
       (t = a)
      )
  ) 
  uniqueness:
      ∀ t1 t2 : ((α × α) × α),
       ¬ ((t1 ∈ δ) ∧ (t1 ∈ δ)) ∨ 
        (¬ ( t1.fst = t2.fst) ∨ t1.snd = t2.snd)

def AllElementsOfWordInSet {α : Type u} (w: Word α) (S: Set α ) :=
  match w with 
  | Word.mk (a::as)  => a ∈ S ∧ AllElementsOfWordInSet (Word.mk as) S
  | _ => True

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

def NFASprache {α : Type u} {dfa: @ NFA α } : Language α :=
  fun w: Word α => 
    ∃ f s, f ∈ dfa.F ∧ s ∈ dfa.Q0 ∧ 
    @SternSchrittableitungsregelNFA α dfa s f w Word.epsilon


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


theorem Set.union_or {α : Type u} (X Y : Set α) (e : α) : (e ∈ (X ∪ Y)) = (e ∈ X ∨ e ∈ Y) := by rfl

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

theorem Word.epsilon_eq_epsilon {α : Type u} : (@ε α)  = (Word.mk List.nil)  := by rfl 


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

 
