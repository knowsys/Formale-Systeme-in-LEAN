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
    have vw_in_l := h2.mp $ e ▸ singl_inter.right
    have vw_eq_uw := e ▸ h (v*w) ⟨ Or.inr rfl, vw_in_l ⟩
    exact pre <| Eq.symm <| Word.mul_right_cancel vw_eq_uw
  case inr e =>
    have uw_in_l := h2.mpr $ e ▸ singl_inter.right
    have uw_eq_vw := e ▸ h (u*w) ⟨ Or.inl rfl, uw_in_l ⟩
    exact pre <| Word.mul_right_cancel uw_eq_vw

theorem Nerode.not_right_congruent1 (L : Language α) (u v : Word α):
  (∃w, u*w ∈ L ∧ v*w ∉ L) → ¬ u ≃(L) v := by
  intro ⟨ w, uw_in_l, vw_nin_l ⟩ contra
  apply vw_nin_l
  apply (contra w).mp
  exact uw_in_l
