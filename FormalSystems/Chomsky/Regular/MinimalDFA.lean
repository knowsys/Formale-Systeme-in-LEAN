import FormalSystems.Chomsky.Regular.Nerode
import FormalSystems.Chomsky.Regular.TotalDFA
import Mathlib.Order.Hom.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.Lattice
import Mathlib.Logic.Function.Iterate

variable {M: TotalDFA α qs} [DecidableEq qs]

instance M_equiv (M: TotalDFA α qs): Setoid (M.Q) where
  r q₁ q₂ := ∀w, M.del_star' (q₁, w) ∈ M.F ↔ M.del_star' (q₂, w) ∈ M.F
  iseqv := {
    refl := fun _ _ => Iff.rfl,
    symm := fun h w => Iff.symm $ h w,
    trans := fun h₁ h₂ w => Iff.trans (h₁ w) (h₂ w)
  }

theorem M_right_congruent (h: q ≈ p) (a: M.Z): M.δ' (q, a) ≈ M.δ' (p, a) :=
  fun w => h (a :: w)

section M_equiv_computation

def rule1: Finset (M.Q × M.Q) := { x | (x.1 ∈ M.F) ≠ (x.2 ∈ M.F) }.toFinset

def shift (orig: Finset (M.Q × M.Q)): Finset (M.Q × M.Q) :=
  { x | ∃a, ⟨M.δ' (x.1, a), M.δ' (x.2, a)⟩ ∈ orig }.toFinset

def rule2 (approx: Finset (M.Q × M.Q)): Finset (M.Q × M.Q) := approx ∪ shift approx
theorem rule2_increasing: s ⊆ rule2 (M:=M) s := fun _ h => Finset.mem_union_left _ h

def rule2_closure (approx: Finset (M.Q × M.Q)): Finset (M.Q × M.Q) :=
  if H: approx = rule2 approx
    then approx
    else
      have : (rule2 approx)ᶜ.card < approxᶜ.card := by
        apply Finset.card_lt_card ∘ Finset.ssubset_iff_subset_ne.mpr
        constructor
        apply Finset.compl_subset_compl.mpr
        apply rule2_increasing
        simp; intro h; exact H h.symm
      rule2_closure (rule2 approx)
termination_by _ a => aᶜ.card

section closure

variable [Fintype α] [sls: SemilatticeSup α] [DecidableEq α]
def closure (f: α → α): α → α := fun x =>
  if H: x = x ⊔ f x
    then x
    else
      have : x ⊔ f x > x := sorry
      closure f (x ⊔ f x)

end closure

section uneeded
theorem rule2_unfold: (rule2 (M:=M)) a = a ∪ shift a := rfl

def m_not_equiv_n (n: ℕ): Finset (M.Q × M.Q) := (rule2^[n]) rule1

theorem monotone_shift: Monotone (shift (M:=M)) := fun _ _ h _ H =>
  have ⟨x, H⟩ := Set.mem_toFinset.mp H
  Set.mem_toFinset.mpr ⟨x, h H⟩

theorem monotone_rule2: Monotone (rule2 (M:=M)) := fun _ _ h _ H => by
  cases Finset.mem_union.mp H
  apply Finset.mem_union_left; apply h; assumption
  apply Finset.mem_union_right; apply monotone_shift h; assumption


theorem Iterate.monotone [Preorder α] {f: α → α} (h: Monotone f) (h': start ≤ f start): Monotone (λn ↦ f^[n] start) := by
  intro a b H; simp
  induction' b with _ ih generalizing a
  simp at H; simp [H]
  cases a
  rw [Function.iterate_succ', Function.comp]
  apply Preorder.le_trans _ (f start) _
  assumption
  apply h
  apply ih (Nat.zero_le _)
  simp_rw [Function.iterate_succ', Function.comp]
  apply h; apply ih
  apply Nat.succ_le_succ_iff.mp H

theorem m_not_equiv_n_monotone: Monotone (m_not_equiv_n (M:=M)) := by
  apply Iterate.monotone
  apply monotone_rule2
  rw [rule2_unfold]
  intro; apply Finset.mem_union_left

theorem iterate_lim (f: α → α) (a: α) (h: f^[n] a = f^[n + 1] a):
  ∀ k ≥ n, f^[n] a = f^[k] a := by
  intro k _
  let m := k - n; have : m = k - n := rfl
  rw [← Nat.sub_add_cancel ‹k ≥ n›, ← ‹m = k-n›, Nat.add_comm]
  induction' m with _ ih; rfl
  rw [Nat.add_succ, Function.iterate_succ]
  unfold m_not_equiv_n at ih
  rw [Nat.iterate] at h
  rw [ih]; conv => congr <;> rw [Nat.add_comm]; rfl
  rw [Function.iterate_add, Function.comp_apply]
  congr
end uneeded

def m_not_equiv: Finset (M.Q × M.Q) := rule2_closure rule1
def m_equiv: Finset (M.Q × M.Q) := (rule2_closure rule1)ᶜ

theorem not_equiv_imp_exist_w (h: ⟨q, p⟩ ∈ m_not_equiv):
  ∃w, (M.del_star' (q, w) ∈ M.F) ≠ (M.del_star' (q, w) ∈ M.F) := by
  unfold m_not_equiv rule2_closure at h

  sorry

theorem equiv_iff_mem: a ≈ b ↔ ⟨a, b⟩ ∈ m_equiv (M:=M) := by
  sorry

end M_equiv_computation

instance [i: Fintype α] [s: Setoid α] [DecidableEq (Quotient s)]: Fintype (Quotient s) where
  elems := i.elems.image (Quotient.mk s)
  complete q := by
    rw [Finset.mem_image]
    apply Quotient.rec (motive := fun q => ∃a ∈ Fintype.elems, Quotient.mk s a = q)
    intros; simp
    intro x; exists x
    exact ⟨Fintype.complete _, rfl⟩

instance {a b: M.Q}: Decidable (a ≈ b) := by
  rw [equiv_iff_mem]
  exact inferInstance

def TotalDFA.shrunk (M: TotalDFA α qs): TotalDFA α (Quotient (M_equiv M)) where
  Z := M.Z
  Q := Fintype.elems
  q₀ := ⟨ Quotient.mk (M_equiv M) M.q₀, Fintype.complete _ ⟩
  F := M.F.image (fun q => ⟨ Quotient.mk (M_equiv M) q, Fintype.complete _ ⟩ )
  δ := fun (q, a) => q.val.lift
    (fun q => some ⟨Quotient.mk _ $ M.δ' (q, a), Fintype.complete _⟩)
    (fun x y H => by simp; exact M_right_congruent H _)

  totality q a := by simp; refine' q.val.recOn _ _ <;> intros <;> simp

variable {M: TotalDFA α qs}

instance : Setoid (Word M.Z) := myhillNerodeEquivalence M.GeneratedLanguage

def TotalDFA.shrunk_on (M: TotalDFA α qs) (w: Word M.Z): M.shrunk.Q :=
  M.shrunk.del_star' (M.shrunk.q₀, w)

theorem shrunk_eq_iff_equiv {M: TotalDFA α qs} {v w: _}:
  M.shrunk_on w = M.shrunk_on v ↔ w ≈ v := by
  sorry
