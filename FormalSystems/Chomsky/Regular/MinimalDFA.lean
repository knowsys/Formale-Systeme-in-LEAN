import FormalSystems.Chomsky.Regular.TotalDFA

variable (M: TotalDFA α qs)

def M_equiv: Setoid (M.Q) where
  r q₁ q₂ := ∀w, M.del_star' (q₁, w) ∈ M.F ↔ M.del_star' (q₂, w) ∈ M.F
  iseqv := {
    refl := fun _ _ => Iff.rfl,
    symm := fun h w => Iff.symm $ h w,
    trans := fun h₁ h₂ w => Iff.trans (h₁ w) (h₂ w)
  }

instance [i: Fintype α] [s: Setoid α] [DecidableEq (Quotient s)]: Fintype (Quotient s) where
  elems := i.elems.image (Quotient.mk s)
  complete q := by
    rw [Finset.mem_image]
    apply Quotient.rec (motive := fun q => ∃a ∈ Fintype.elems, Quotient.mk s a = q)
    intros; simp
    intro x; exists x
    exact ⟨Fintype.complete _, rfl⟩

instance : DecidableEq (Quotient (M_equiv M)) := sorry

def TotalDFA.shrunk (M: TotalDFA α qs): TotalDFA α (Quotient (M_equiv M)) where
  Z := M.Z
  Q := Fintype.elems
  q₀ := ⟨ Quotient.mk (M_equiv M) M.q₀, Fintype.complete _ ⟩
  F := M.F.image (fun q => ⟨ Quotient.mk (M_equiv M) q, Fintype.complete _ ⟩ )
  δ := fun (q, a) => q.val.lift
    (fun q => some ⟨Quotient.mk _ $ M.δ' (q, a), Fintype.complete _⟩)
    (fun x y => by simp; intro h; apply Quot.sound; exact h)

  totality := sorry
