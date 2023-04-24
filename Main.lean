import Logic
import Set
import Monoid
import FinSet

----------------------------------ALPHABETS--------------------------------------

class Alphabet (α : Type u) where
  (non_empty : α)
  (elems : FinSet α)
  (complete : ∀ x : α, x ∈ elems)

----------------------------------WORDS------------------------------------------
structure Word (α : Type u) [Alphabet α] where
  data : List α
  deriving Repr

def Word.epsilon [Alphabet α] : Word α := Word.mk List.nil
notation (priority := high) "ε" => Word.epsilon

instance [Alphabet α] : Monoid (Word α) where
  mident := ε
  mconcat u v := { data := u.data ++ v.data }
  identity := {
    left := fun w => by simp [Word.epsilon]
    right := fun w => by simp [Word.epsilon]
  }
  assoc := by 
    simp [Associative]
    intro u v w
    exact List.append_assoc u.data v.data w.data

def Word.len [Alphabet α] (w:Word α) : Nat :=
  match w with 
  | Word.mk List.nil => 0
  | Word.mk (x::xs) => 1 + Word.len (Word.mk (xs))

def Word.AllElementsOfWordInSet [Alphabet α] (w: Word α) (S: Set α) :=
  match w with 
  | Word.mk (a::as)=> a ∈ S ∧ Word.AllElementsOfWordInSet (Word.mk as) S
  | _ => True

----------------------------------LANGUAGES---------------------------------------
def Language (α : Type u) [Alphabet α] := Set (Word α)

instance [Alphabet α] : Membership (Word α) (Language α) where
  mem x L := Set.contains L x

def Language.concat [Alphabet α] (X Y : Language α) : Language α := 
  Set.mk fun w : Word α => ∃ u v : Word α, u ∈ X ∧ v ∈ Y ∧ w = u ∘ₘ v
infixr:70 " ∘ₗ " => Language.concat

def Language.epsilon [Alphabet α] : Language α :=
  Set.mk fun w => w = ε

def Language.power [Alphabet α] (n:Nat) (X: Language α) : Language α := 
  match n with
  | 0 => Language.epsilon
  | (Nat.succ m) => Set.mk fun (w:Word α) => 
      ∃ w1 w2 : Word α, w2 ∈ (Language.power m X) ∧ w1 ∈ X ∧ w = w1 ∘ₘ w2

def Language.kleene [Alphabet α] (X : Language α) : Language α :=
  Set.mk fun w: Word α =>
    ∃ n : Nat, w ∈ Language.power n X

def Language.plus [Alphabet α] (X: Language α) : Language α :=
  Set.mk fun w: Word α => 
    ∃ n:Nat, ¬ (n = 0) ∧ w ∈ Language.power n X

def Sigma.language [Alphabet α] : Language α := 
  Set.mk fun w: Word α =>
    match w with
    | (Word.mk (_::[])) => True
    | _ => False

def Sigma.kleene [Alphabet α] : Language α :=
  Set.mk fun _: Word α => True

def Language.complement [Alphabet α] (L : Language α) := Set.complement L

theorem Language.kleene_eq_plus_eps [Alphabet α] {L: Language α} 
: Language.plus L ∪ Language.epsilon = Language.kleene L := by 
  apply Set.equ ∘ funext
  intro w
  apply propext
  constructor

  case a.mp =>
    intro l_as_union
    simp [Set.union] at l_as_union
    rw [Language.kleene]
    cases l_as_union with 
    |inl p => 
      rw [Language.plus] at p 
      cases p with
      | intro n r =>
        exists n 
        exact r.right 
    |inr e => 
      exists 0

  case a.mpr =>
    intro n
    rw [Set.union]
    simp [Language.kleene] at n 
    cases n with 
    | intro nn r => 
      cases nn with 
      | succ m => 
        apply Or.inl 
        simp [Language.plus]
        exists (Nat.succ m)
        exact ⟨Nat.succ_ne_zero m, r⟩ 
      | zero => 
        apply Or.inr
        simp [Language.power] at r
        exact r 

theorem Language.lan_eps_eq_lan [Alphabet α] (L : Language α): L ∘ₗ Language.epsilon = L := by
  apply Set.equ ∘ funext
  intro w
  apply propext
  constructor

  case a.mp =>
    rw [Language.concat]
    intro ⟨u,v, h1, h2, h3⟩
    simp [Language.epsilon, Membership.mem, Word.epsilon] at h2
    simp [h2, Monoid.mconcat, Monoid.identity.right] at h3
    simp [h3]
    exact h1

  case a.mpr =>
    intro h
    simp [Language.concat]
    exists w ; exists ε
    apply And.intro
    simp [Membership.mem, h]
    apply And.intro
    simp [Language.epsilon, Membership.mem]
    simp [Word.epsilon, Monoid.mconcat]

theorem Language.eps_lan_eq_lan [Alphabet α] (L : Language α): Language.epsilon ∘ₗ L = L := by
  apply Set.equ ∘ funext
  intro w
  apply propext
  constructor

  case a.mp =>
    rw [Language.concat]
    intro ⟨u,v, h1, h2, h3⟩
    simp [Language.epsilon, Membership.mem] at h1
    simp [Monoid.mconcat, h1, Word.epsilon] at h3
    simp [h3]
    exact h2

  case a.mpr =>
    intro h
    simp [Language.concat]
    exists ε ; exists w
  
theorem Language.empty_lan_eq_empty [Alphabet α] (L : Language α) : L ∘ₗ ∅ = ∅ := by
  apply Set.setext 
  intro w 
  constructor
  intro n
  rw [Language.concat] at n
  match n with 
  | ⟨u,v,_,h2,h3⟩ =>
    rw [Set.empty] at h2
    apply False.elim h2 
  intro n 
  rw [Set.empty] at n
  apply False.elim n 

theorem Language.lan_empty_eq_empty [Alphabet α] (L : Language α) : ∅ ∘ₗ L = ∅ := by
  apply Set.setext 
  intro w 
  constructor
  intro n 
  rw [Language.concat] at n
  match n with 
  | ⟨u,v, h1,h2,h3⟩ => 
    rw [Set.empty] at h1
    apply False.elim h1 
  intro n 
  rw [Set.empty] at n 
  apply False.elim n 

theorem Language.concat_dist_union_r [Alphabet α] (L1 L2 L3 : Language α) : (L1 ∪ L2) ∘ₗ L3 = (L1 ∘ₗ L3) ∪ (L2 ∘ₗ L3) := by
  apply Set.setext 
  intro w 
  constructor 
  intro n 
  rw [Language.concat] at n
  match n with 
  | ⟨u,v,h1,h2,h3⟩ => 
    rw [Set.union]
    rw [Set.union] at h1
    cases h1 with 
    | inl hl => 
      apply Or.inl
      rw [Language.concat]
      exists u
      exists v 
    | inr hr =>
      apply Or.inr 
      rw [Language.concat]
      exists u
      exists v
  intro n 
  rw [Set.union] at n
  cases n with 
  | inl hl =>
    rw [Language.concat]
    rw [Language.concat] at hl
    match hl with 
    | ⟨u,v,h1,h2,h3⟩ =>
      exists u
      exists v 
      rw [Set.union]
      exact ⟨Or.inl h1, h2,h3⟩ 
  |inr hr => 
    rw [Language.concat]
    rw [Language.concat] at hr 
    match hr with 
    | ⟨u,v,h1,h2,h3⟩ => 
      exists u
      exists v
      exact ⟨Or.inr h1, h2, h3⟩

theorem Language.concat_dist_union_l [Alphabet α] (L1 L2 L3 : Language α) : L1 ∘ₗ (L2 ∪ L3) = (L1 ∘ₗ L2) ∪ (L1 ∘ₗ L3) := by
  apply Set.equ ∘ funext
  intro w
  apply propext
  constructor

  case a.mp =>
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

  case a.mpr =>
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

----------------------------------GRAMMARS---------------------------------------
structure Grammar [Alphabet α] where
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

structure RegularGrammar [Alphabet α] extends (@Grammar α _) where
  bed_reg: ∀ pair : ((Word α) × (Word α)), 
    (pair ∈ P) -> 
    (
      (∃ t: α, (Word.mk [t] = pair.fst) ∧ t ∈ V) ∧ (
        (∃ t1 t2 : α, (Word.mk [t1, t2] = pair.snd) ∧ t1 ∈ E ∧ t2 ∈ V) ∨ 
        (∃ t: α, Word.mk [t] = pair.snd ∧ t ∈ E) ∨ 
        pair.snd = Word.mk []
     )
   )

structure EpsilonFreeRegularGrammar [Alphabet α] extends (@RegularGrammar α _) where
  epsilonFree : ∀ pair : (Word α) × (Word α), 
  ¬ (pair ∈ P) ∨ (
    pair.fst = Word.mk ([S]) ∨ ¬ (pair.snd = Word.epsilon)
 )

def OneStepDerivation [Alphabet α] (G : @Grammar α _) (w : Word α) (v : Word α) : Prop :=
    ∃ w1 w2 w3: Word α,
      ∃ v1 v2 v3: Word α,
      have p1 := w = w1 ∘ w2 ∘ w3
      have p2 := v = v1 ∘ v2 ∘ v3
      (v1 = w1) ∧ (v3 = w3) ∧ p1 ∧ p2 ∧ G.P ⟨w2, v2⟩
        
def NstepDerivation [Alphabet α] (G : @Grammar α _) (w : Word α) (v : Word α) (n:Nat) : Prop :=
  match n with
  | 0 => 
    w = v
  | (Nat.succ m) => 
      ∃ w1 : Word α, (OneStepDerivation G w w1) ∧ (NstepDerivation G w1 v m) ∧ (Word.AllElementsOfWordInSet v G.E)

def StarDerivation [Alphabet α] (G : @Grammar α _) (w : Word α) (v : Word α) : Prop :=
  ∃ n : Nat, NstepDerivation G w v n
  
def GeneratedLanguageGrammar [Alphabet α] (G : @Grammar α _): Language α :=
  fun w: Word α => 
    StarDerivation G (Word.mk [G.S]) w

def RunRegularGrammarSub [Alphabet α] (ql qg : α) (G : @RegularGrammar α _) (run: List (Word α × Word α))(w : Word α) : Prop :=
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

def LanguageRegularGrammar [Alphabet α] (G : @RegularGrammar α _) : Language α :=
  fun w => ∃ qn run, (RunRegularGrammarSub G.S qn G run w ∧ ⟨Word.mk [qn], Word.mk []⟩ ∈ G.P
    ∨ ∃ w1, ∃ z : α, (w = w1 ∘ Word.mk [z]) ∧ RunRegularGrammarSub G.S qn G run w1 ∧ ⟨Word.mk [qn], Word.mk [z]⟩ ∈ G.P)

----------------------------------AUTOMATA------------------------------------------
structure NFA { q } [Alphabet α] where 
  Q : FinSet q 
  δ : (q × α) -> Option q
  Q₀ : FinSet q
  F : FinSet q
  Q0subset: Q₀ ⊆ Q 
  Fsubset: F ⊆ Q
  Tfunction: 
    ∀ t : ((α × α) × α),
       ¬ (t ∈ δ) ∨ (
          t.fst.fst ∈ Q ∧ 
          t.fst.snd ∈ E ∧ 
          t.snd ∈ Q
      ) 
  
structure DFA [Alphabet α] extends (@ NFA α _) where 
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

def nfaDerivation [Alphabet α] (nfa: @ NFA α _) (q1 qf: α) (w: Word α) : Prop :=
  match w with 
  | Word.mk (x::xs) => ∃ qn, nfa.δ ⟨⟨q1, x⟩,qn⟩ ∧ nfaDerivation nfa qn qf (Word.mk xs) 
  | Word.mk [] => q1 = qf

def nfaLanguage [Alphabet α] (nfa: @ NFA α _) : Language α :=
  fun w => ∃ qs qf, qs ∈ nfa.Q0 ∧ qf ∈ nfa.F ∧ nfaDerivation nfa qs qf w

structure TotalDFA [Alphabet α] extends (@ DFA α _) where 
  tot: ∀ t : ((α × α) × α),
  (¬ (t.fst.snd ∈ E ∧ t.fst.fst ∈ Q) ∨ 
    ∃ q2 : α, ⟨⟨t.fst.fst, t.fst.snd⟩, q2⟩ ∈ δ
 )

def TotalDFAConstruct [Alphabet α] (dfa: @ DFA α _) (fang: α) (p1: ¬fang ∈ dfa.Q ∧ ¬fang ∈ dfa.E) : @TotalDFA α _ :=
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

  have Q2Edisj : Q2 ∩ dfa.E = Set.empty := by
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
def ConstructRegularGrammarFromDFA [Alphabet α] (dfa: @ DFA α _) : @RegularGrammar α _:= 
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
          exact disjB2.left
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
          rw [disj1woE.left]
          simp
          match k1 with 
          | ⟨qrr, k1woE⟩ =>
            rw [← k1woE.left]
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
              rw [disjB2.left]
              simp [qInQ, disjB2.left]
            have k2: ((∃ t1 t2, {data := [t1, t2]} = pair.snd ∧ t1 ∈ E ∧ t2 ∈ V) ∨ (∃ t, {data := [t]} = pair.snd ∧ t ∈ E) ∨ pair.snd = {data := []}) := by
              apply Or.inr
              apply Or.inr
              rw [disjB2.right.left]
            simp [k1, k2]

    {V := V, E := E, S := S, P := P, bed_VEdisj := bed_VEdisj, bed_SinV := bed_SinV, bed_VarInLeft := bed_VarInLeft, bed_reg := bed_reg : RegularGrammar}
       
theorem deriviationsEQ1 [Alphabet α] (dfa: @ DFA α _)(w: Word α) : 
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

theorem deriviationsEQ2 [Alphabet α] (dfa: @ DFA α _) (w: Word α) : 
     ∀ q1 q2,(∃ run,
      (RunRegularGrammarSub q1 q2 (ConstructRegularGrammarFromDFA dfa) run w))-> (nfaDerivation dfa.toNFA q1 q2 w) := by
  have hp := Word.objects_equal w 
  rw [← hp] 
  induction w.data with
  | nil => 
    intro _ _ runex
    match runex with 
    | ⟨run, runwo⟩ =>
      simp [RunRegularGrammarSub] at runwo 
      simp [nfaDerivation, runwo]
  | cons x xs iv => 
    intro _ q22 runex
    match runex with 
    | ⟨run2, runwo⟩ =>
      cases run2 with 
      | nil => 
        simp [RunRegularGrammarSub] at runwo
      | cons runx runxs =>
        simp [RunRegularGrammarSub] at runwo 
        simp [nfaDerivation]
        have runwo2 := runwo.right.right 
        match runwo2 with
        | ⟨qn, runwo3⟩ =>
          exists qn
          have runwo4ex : ∃ run, RunRegularGrammarSub qn _ (ConstructRegularGrammarFromDFA dfa) run {data := xs} := by
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

theorem languageDFAeqConstructedRegularGrammar2 [Alphabet α] (dfa : @DFA α _) : (@nfaLanguage α _ dfa.toNFA) = (@LanguageRegularGrammar α _ (ConstructRegularGrammarFromDFA dfa)) := by 
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
    