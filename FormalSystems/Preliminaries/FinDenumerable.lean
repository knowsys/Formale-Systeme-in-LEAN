import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Countable

class FinDenumerable (α : Type u) extends Fintype α, Encodable α where
  encode_lt_card: ∀(a : α), encode a < card 

def FinDenumerable.encode_fin [inst: FinDenumerable α] (a : α) : Fin inst.card := 
  ⟨ inst.encode a, inst.encode_lt_card a ⟩

theorem FinDenumerable.encode_fin_eq_encode [inst: FinDenumerable α] :
  ∀(a : α), encode_fin a = inst.encode a := by simp [encode_fin]

theorem FinDenumerable.encode_fin_injective [inst: FinDenumerable α] : Function.Injective inst.encode_fin := by
  intro x y; simp [Fin.eq_iff_veq, encode_fin]

def FinDenumerable.encode_embedding [inst: FinDenumerable α] : α ↪ Fin inst.card :=
  ⟨ encode_fin, encode_fin_injective ⟩

def FinDenumerable.encode_fin_bijective [inst: FinDenumerable α] : Function.Bijective inst.encode_fin := by
  apply (Fintype.bijective_iff_injective_and_card encode_fin).2
  simp; exact encode_fin_injective

theorem FinDenumerable.decode_partial_inv [inst: FinDenumerable α] (n : Fin inst.card): 
  ∃a ∈ inst.decode n, inst.encode a = n := by
  have ⟨ a, pa, _ ⟩  := encode_fin_bijective.existsUnique n
  exists a; simp [Fin.eq_iff_veq, encode_fin] at pa;
  simp [pa]; simp [<- pa]

theorem FinDenumerable.decode_fin_is_some [inst: FinDenumerable α] (n : Fin inst.card): 
  (inst.decode n.1).isSome := by
  apply Option.isSome_iff_exists.2
  apply (decode_partial_inv n).imp
  intro _ h
  exact h.1

def FinDenumerable.decode_fin [inst: FinDenumerable α] (n : Fin inst.card) : α :=
  Option.get (inst.decode n.1) (decode_fin_is_some n)

theorem FinDenumerable.decode_fin_eq_option_get [inst: FinDenumerable α] (n : Fin inst.card) :
  Option.get (inst.decode n.1) (decode_fin_is_some n) = decode_fin n := by simp [decode_fin]

def FinDenumerable.fin_preimage_exists [inst: FinDenumerable α] (n: Fin inst.card) :
  ∃a, inst.encode a = n := by
  apply (inst.decode_partial_inv n).imp
  intro _ h; exact h.2

theorem FinDenumerable.fin_decode_eq_decode₂ [inst: FinDenumerable α] (n : Fin inst.card) :
  inst.decode n = inst.decode₂ n := by
  rw [← Option.some_get (decode_fin_is_some n)]
  apply Eq.symm
  rw [Encodable.decode₂_is_partial_inv]
  have ⟨ _, h ⟩ := fin_preimage_exists n
  simp [<- h]

theorem FinDenumerable.decode_fin_inj [inst: FinDenumerable α] {n m : Fin inst.card}
  (h₁: a = FinDenumerable.decode_fin n)
  (h₂: b = FinDenumerable.decode_fin m) :
  a = b ↔ n = m := by
  have ⟨ _, p₁ ⟩ := fin_preimage_exists n  
  simp [FinDenumerable.decode_fin, <- p₁] at h₁
  have ⟨ _, p₂ ⟩ := fin_preimage_exists m  
  simp [FinDenumerable.decode_fin, <- p₂] at h₂
  rw [h₁, h₂, Fin.eq_iff_veq, ← p₁, ← p₂]
  apply Iff.symm; apply Encodable.encode_inj

theorem FinDenumerable.decode_fin_injective [inst: FinDenumerable α] :
  Function.Injective (@FinDenumerable.decode_fin _ inst) :=
  fun a b => (FinDenumerable.decode_fin_inj 
    (@rfl α $ @decode_fin _ inst a)
    (@rfl α $ @decode_fin _ inst b)).1

def FinDenumerable.decode_embedding [inst: FinDenumerable α] : Fin inst.card ↪ α :=
  ⟨ decode_fin, decode_fin_injective ⟩

theorem FinDenumerable.encodek_fin_left_inverse [FinDenumerable α] :
  Function.LeftInverse (@decode_fin α _) encode_fin := by
  intro _; simp [encode_fin, decode_fin]

theorem FinDenumerable.decodenk [inst: FinDenumerable α] :
  ∀(n : Fin inst.card), encode_fin (decode_fin n) = n := by
  simp [encode_fin, Fin.eq_iff_veq, decode_fin]; intro n
  have ⟨ a, ph ⟩ := fin_preimage_exists n
  simp [<- ph]

theorem Set.univ_eq_type { α : Type _ } : ↑(@Set.univ α) ≃ α := by
  let f : Subtype (λ _ : α ↦ True) -> α := λ a ↦ a.val
  have inj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    simp [h]
  have sur : Function.Surjective f := by
    intro b
    let a : Subtype (λ _ : α ↦ True) := { val := b, property := True.intro }
    exists a
  have bij : Function.Bijective f := by constructor; exact inj; exact sur
  exact Equiv.ofBijective f bij

theorem FinDenumerable.encode_fin_range [inst: FinDenumerable α] :
  ↑(Set.range inst.encode_fin) ≃ Fin inst.card := by
  rw [Function.Surjective.range_eq _]
  exact Set.univ_eq_type
  exact encode_fin_bijective.surjective

theorem FinDenumerable.equiv_fin [inst: FinDenumerable α] : α ≃ Fin inst.card := by
  have tmp := Equiv.ofLeftInverse encode_fin (fun _ => inst.decode_fin) (fun _ => encodek_fin_left_inverse)
  apply Equiv.trans tmp encode_fin_range
