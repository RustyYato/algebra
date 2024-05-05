import Algebra.SortedList.Basic

def sorted_union
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (xs ys: List α) -> List α := by
  apply @sorted_induction α _ _ (SortedIndCtx.mk (fun _ _ => List α) _ _ _ _ _)
  {
    intro _
    exact []
  }
  {
    intro _ _
    exact []
  }
  {
    intro x y _ _ _ _ prev
    exact x::prev
  }
  {
    intro _ y _ _ _ _ prev
    exact y::prev
  }
  {
    intro x y xs ys x_eq_y prev
    exact x::prev
  }

def sorted_union.left_empty
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (ys: List α) -> sorted_union [] ys = [] := by
  intro ys
  unfold sorted_union
  rw [sorted_induction.left_empty]

#print axioms sorted_union.left_empty

def sorted_union.right_empty
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (xs: List α) -> sorted_union xs [] = [] := by
  intro xs
  match xs with
  | [] => rfl
  | x::xs =>
  unfold sorted_union
  rw [sorted_induction.right_empty]

#print axioms sorted_union.right_empty

def sorted_union.if_lt
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x ≤ y) ->
  (x_ne_y: x ≠ y) ->
  sorted_union (x::xs) (y::ys) = x::sorted_union xs (y::ys) := by
  intro x y xs ys x_le_y x_ne_y
  unfold sorted_union
  rw [sorted_induction.if_lt]
  repeat assumption

#print axioms sorted_union.if_lt

def sorted_union.if_gt
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_ge_y: x ≥ y) ->
  (x_ne_y: x ≠ y) ->
  sorted_union (x::xs) (y::ys) = y::sorted_union (x::xs) ys := by
  intro x y xs ys x_ge_y x_ne_y
  unfold sorted_union
  rw [sorted_induction.if_gt]
  repeat assumption
  

#print axioms sorted_union.if_gt

def sorted_union.if_eq
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_eq_y: x = y) ->
  sorted_union (x::xs) (y::ys) = x::sorted_union xs ys := by
  intro x y xs ys x_eq_y
  unfold sorted_union
  rw [sorted_induction.if_eq]
  repeat assumption

#print axioms sorted_union.if_eq

def sorted_union.comm
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (xs ys: List α) ->
  sorted_union xs ys = sorted_union ys xs := by
  apply sorted_induction'
  {
    intro ys
    rw [left_empty, right_empty]
  }
  {
    intro x xs
    rw [left_empty, right_empty]
  }
  {
    intro x y xs ys x_le_y x_ne_y ih
    rw [if_lt, if_gt]
    congr
    any_goals assumption
    exact x_ne_y.symm
  }
  {
    intro x y xs ys x_ge_y x_ne_y ih
    rw [if_gt, if_lt]
    congr
    any_goals assumption
    exact x_ne_y.symm
  }
  {
    intro x y xs ys x_eq_y ih
    rw [if_eq, if_eq]
    congr
    exact x_eq_y.symm
    assumption
  }

#print axioms sorted_union.comm

def sorted_union.idempotent_left
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (xs ys: List α) ->
  sorted_union (sorted_union xs ys) ys = sorted_union xs ys := by
  apply sorted_induction'
  {
    intro ys
    rw [left_empty, left_empty]
  }
  {
    intro x xs
    rw [right_empty, right_empty]
  }
  {
    intro x y xs ys x_le_y x_ne_y ih
    rw [if_lt, if_lt]
    congr
    repeat assumption
  }
  {
    intro x y xs ys x_ge_y x_ne_y ih
    rw [if_gt, if_eq]
    congr
    rfl
    repeat assumption
  }
  {
    intro x y xs ys x_eq_y ih
    rw [if_eq, if_eq]
    congr
    repeat assumption
  }
 
 #print axioms sorted_union.idempotent_left

def sorted_union.idempotent_right
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]:
  (xs ys: List α) ->
  sorted_union xs (sorted_union xs ys) = sorted_union xs ys := by
  intro xs ys
  rw [sorted_union.comm, sorted_union.comm xs, sorted_union.idempotent_left]
 
 #print axioms sorted_union.idempotent_right
