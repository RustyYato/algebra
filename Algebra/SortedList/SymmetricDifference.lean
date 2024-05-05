import Algebra.SortedList.Basic

def List.sorted_symm_difference
  { α: Sort _ }
  [LE α] [TrustedLE α]
  [LE α] [tle: TrustedLE α]:
  (xs ys: List α) -> List α := by
  apply @sorted_induction α _ _ (SortedIndCtx.mk (fun _ _ => List α) _ _ _ _ _)
  {
    intro ys
    exact ys
  }
  {
    intro x xs
    exact x::xs
  }
  {
    intro x y xs ys x_le_y x_ne_y prev
    exact x::prev
  }
  {
    intro x y xs ys x_ge_y x_ne_y prev
    exact y::prev
  }
  {
    intro x y xs ys x_eq_y prev
    exact prev
  }

