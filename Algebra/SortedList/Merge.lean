import Algebra.SortedList.Basic

def List.sorted_merge
  { α: Sort _ }
  [Ord α] [TotalOrder α]:
  (xs ys: List α) -> List α := by
  apply @sorted_induction α _ _ (SortedIndCtx.mk (fun _ _ => List α) _ _ _ _ _)
  {
    intro ys
    exact ys
  }
  {
    intro x xs
    exact xs
  }
  {
    intro x y xs ys x_lt_y prev
    exact x::prev
  }
  {
    intro x y xs ys x_gt_y x_prev
    exact y::prev
  }
  {
    intro x y xs ys x_eq_y prev
    exact x::y::prev
  }
