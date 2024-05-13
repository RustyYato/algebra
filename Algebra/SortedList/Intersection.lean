import Algebra.SortedList.Basic

def sorted_intersection
  { α: Sort _ }
  [Ord α] [TotalOrder α]:
  (xs ys: List α) -> List α := by
  apply @sorted_induction α _ _ (SortedIndCtx.mk (fun _ _ => List α) _ _ _ _ _)
  {
    intro ys
    exact []
  }
  {
    intro x xs
    exact []
  }
  {
    intro x y xs ys x_lt_y prev
    exact prev
  }
  {
    intro x y xs ys x_gt_y prev
    exact prev
  }
  {
    intro x y xs ys x_eq_y prev
    exact x::prev
  }

def sorted_intersection.left_empty
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (ys: List α) -> sorted_intersection [] ys = [] := by
  intro ys
  rfl

#print axioms sorted_intersection.left_empty

def sorted_intersection.right_empty
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs: List α) -> sorted_intersection xs [] = [] := by
  intro xs
  match xs with
  | [] => rfl
  | _::_ => rfl

#print axioms sorted_intersection.right_empty

def sorted_intersection.if_lt
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x < y) ->
  sorted_intersection (x::xs) (y::ys) = sorted_intersection xs (y::ys) := by
  intro x y xs ys x_lt_y
  unfold sorted_intersection
  rw [sorted_induction.if_lt]
  repeat assumption

def sorted_intersection.if_gt
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_ge_y: x > y) ->
  sorted_intersection (x::xs) (y::ys) = sorted_intersection (x::xs) ys := by
  intro x y xs ys x_gt_y
  unfold sorted_intersection
  rw [sorted_induction.if_gt]
  repeat assumption

def sorted_intersection.if_lt'
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs ys: List α) ->
  (z: α) ->
  (∀y', y' ∈ ys -> y' > z) ->
  sorted_intersection (z::xs) ys = sorted_intersection xs ys := by
  intro xs ys z prf
  match ys with
  | [] => rw [right_empty, right_empty]
  | .cons y ys =>
    have  := prf y (.head _)
    rw [if_lt]
    repeat assumption

#print axioms sorted_intersection.if_lt'

def sorted_intersection.if_gt'
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs ys: List α) ->
  (z: α) ->
  (∀x', x' ∈ xs -> x' > z)->
  sorted_intersection xs (z::ys) = sorted_intersection xs ys := by
  intro xs ys y prf
  match xs with
  | [] => rw [left_empty, left_empty]
  | .cons x xs =>
    have _ := prf x (.head _)
    rw [if_gt]
    repeat assumption

#print axioms sorted_intersection.if_gt'

def sorted_intersection.if_eq
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_eq_y: x = y) ->
  sorted_intersection (x::xs) (y::ys) = x::sorted_intersection xs ys := by
  intro x y xs ys x_eq_y
  unfold sorted_intersection
  rw [sorted_induction.if_eq]
  repeat assumption
 
 def sorted_intersection.comm
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs ys: List α) ->
  sorted_intersection xs ys = sorted_intersection ys xs := by
  apply sorted_induction'
  {
    intro ys
    rw [right_empty, left_empty]
  }
  {
    intro x xs
    rw [left_empty, right_empty]
  }
  {
    intro x y xs ys x_lt_y ih
    rw [if_lt, if_gt]
    exact ih
    any_goals assumption
  }
  {
    intro x y xs ys x_gt_y ih
    rw [if_gt, if_lt]
    exact ih
    any_goals assumption
  }
  {
    intro x y xs ys x_eq_y ih
    rw [if_eq, if_eq]
    congr
    exact x_eq_y.symm
    exact x_eq_y
  }

#print axioms sorted_intersection.comm

def sorted_intersection.refl
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs: List α) -> sorted_intersection xs xs = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => 
    rw [if_eq]
    congr
    rfl

#print axioms sorted_intersection.refl

def sorted_intersection.contains
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  ∀{xs ys: List α},
  ∀{z}, z ∈ sorted_intersection xs ys -> z ∈ xs ∧ z ∈ ys := by
  sorry
  
def sorted_union.of_contains
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  ∀{xs ys: List α},
  ∀{z}, z ∈ xs -> z ∈ ys -> z ∈ sorted_intersection xs ys := by
  sorry

def sorted_intersection.idempotent_left
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs ys: List α) ->
  sorted_intersection (sorted_intersection xs ys) ys = sorted_intersection xs ys := by
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
    intro x y xs ys x_lt_y ih
    rw [if_lt]
    exact ih
    repeat assumption
  }
  {
    intro x y xs ys x_gt_y ih
    rw [if_gt, if_gt']
    exact ih
    any_goals assumption
    intro x' x_in_intersection
    have ⟨ x'_in_xs, x'_in_ys ⟩  := contains x_in_intersection

    admit
  }
  {
    intro x y xs ys x_eq_y ih
    rw [if_eq, if_eq]
    congr
    repeat assumption
  }

#print axioms sorted_intersection.idempotent_left
