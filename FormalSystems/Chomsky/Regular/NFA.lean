import FormalSystems.Chomsky.Regular.RegularGrammar

import Mathlib.Data.Finset.Option

structure NFA (α qs: Type) where
  Z: Finset α
  Q: Finset qs
  δ: (Q × Z) → Finset Q
  Q₀: Finset Q
  F: Finset Q

namespace NFA

inductive Run (M: NFA α qs) : M.Q → Word M.Z → Type
  | final (q: M.Q) (h: w = ε) : M.Run q w
  | step (q₁: M.Q) (q₂: M.δ (q₁, a)) (r: M.Run q₂ w) : M.Run q₁ (a :: w)

def Run.last {M: NFA α qs} {w: Word M.Z} {q: M.Q} : (r: M.Run q w) → M.Q
  | final q _ => q
  | step _ _ r => r.last

def GeneratedLanguage (M: NFA α qs) : Language M.Z :=
  fun w => ∃(q₀ : M.Q₀) (run: M.Run q₀ w), run.last ∈ M.F

end NFA

variable { Z: Finset α } [DecidableEq α]
variable { V: Finset nt } [DecidableEq nt]

def RegularProduction.nextState (a: Z) (current: V):
  RegularProduction Z V → Option (V ⊕ ({ "qₐ" }: Finset _))
  | RegularProduction.eps _ => .none
  | RegularProduction.alpha l r => if l = current ∧ r = a then .some (.inr ⟨"qₐ", by simp⟩) else .none
  | RegularProduction.cons l ⟨ r1, r2 ⟩ => if l = current ∧ r1 = a then .some (.inl r2) else .none

def Fintype.wrap [inst: Fintype t] (a: t) : inst.elems := ⟨ a, Fintype.complete _ ⟩

def RegularGrammar.toNFA (G: RegularGrammar α nt) : NFA α (G.V ⊕ ({ "qₐ" }: Finset _)) where
  Z := G.Z

  Q := Fintype.elems
  Q₀ := { ⟨ .inl G.start, Fintype.complete _ ⟩ }

  F := { ⟨ .inr ⟨"qₐ", by simp⟩, Fintype.complete _ ⟩ } ∪
    (G.productions.filter (·.isEps)).image (Fintype.wrap ∘ .inl ∘ (·.lhs))

  δ := fun (q, a) =>
    match q.val with
    | .inr _ => {}
    | .inl q => Finset.eraseNone $ 
        G.productions.image ((Fintype.wrap <$> .) ∘ RegularProduction.nextState a q)

variable {G: RegularGrammar α nt}
