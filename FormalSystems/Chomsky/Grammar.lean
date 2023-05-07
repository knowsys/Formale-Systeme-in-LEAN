
structure Grammar (α : Type _) where
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
        (∃ t: α, ([t] = v2 ∧ t ∈ V))
   )

