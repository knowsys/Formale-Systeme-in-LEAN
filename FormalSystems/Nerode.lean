import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite
import FormalSystems.Preliminaries.Language

def Nerode.right_congruence (L : Language α) (u v : Word α) : Prop :=
  ∀w, u * w ∈ L ↔ v * w ∈ L

notation:60 u:60 " ≃( " L:61 " ) " v:61 => Nerode.right_congruence L u v

theorem Nerode.not_right_congruent (L : Language α) (u v : Word α) (pre: u ≠ v):
  (∃w, Language.isSingleton ({u*w, v*w} ∩ L)) → ¬ u ≃(L) v := by
  intro ⟨ w, singl, singl_inter, h ⟩
  intro contra
  have h2 := contra w
  cases singl_inter.left
  case inl e =>
    have uw_in_l := singl_inter.right
    rw [e] at uw_in_l
    have vw_in_l := h2.mp uw_in_l
    have vw_in_union : v*w ∈ ({u*w, v*w} : Set (Word α)) := by simp
    have vw_eq_uw := h (v*w) ⟨ vw_in_union, vw_in_l ⟩
    rw [e] at vw_eq_uw
    exact pre <| Eq.symm <| Word.mul_right_cancel vw_eq_uw
  case inr e =>
    have vw_in_l := singl_inter.right
    rw [e] at vw_in_l
    have uw_in_l := h2.mpr vw_in_l
    have uw_in_union : u*w ∈ ({u*w, v*w} : Set (Word α)) := by simp
    have uw_eq_vw := h (u*w) ⟨ uw_in_union, uw_in_l ⟩
    rw [e] at uw_eq_vw
    exact pre <| Word.mul_right_cancel uw_eq_vw