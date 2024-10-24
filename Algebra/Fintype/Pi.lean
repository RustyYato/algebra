import Algebra.Fintype.Basic

variable {β: α -> Type u} {F: ∀x: α, β x}

instance [f: Fintype α] [∀x, Fintype (β x)] : Fintype (∀x, β x) where
  all :=
    let rec all' : list (∀x, β x) :=
      f.all.flat_map
      sorry
    all'
  all_nodups := sorry
  all_spec := sorry
