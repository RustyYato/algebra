import Algebra.Fintype.Basic

instance {P: α -> Prop} [as: Fintype α] [DecidablePred P] : Fintype { x // P x } where
  all := as.all.filterMap fun x => if h:P x then .some ⟨x, h⟩ else .none
  all_nodups := by
    apply List.nodup_filterMap
    apply as.all_nodups
    intro x y h g
    split at h <;> rename_i Px
    split at h <;> rename_i Py
    cases h
    rfl
    contradiction
    rw [dif_neg Px] at g
    contradiction
  all_spec := by
    intro x
    apply List.mem_filterMap.mpr
    exists x.val
    apply And.intro
    apply as.all_spec
    rw [dif_pos x.property]
