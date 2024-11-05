import Algebra.SortedList.Basic

variable { α: Sort _ } [LT α] [LE α] [IsLinearOrder α] [@DecidableRel α (· ≤ ·)]

set_option linter.unusedVariables false in
def sorted_difference:
  (xs ys: List α) -> List α := by
  apply sorted_induction (ctx := SortedIndCtx.mk (fun _ _ => List α) _ _ _ _ _)
  {
    intro ys
    exact []
  }
  {
    intro x xs
    exact x::xs
  }
  {
    intro x y xs ys x_lt_y prev
    exact x::prev
  }
  {
    intro x y xs ys x_gt_y prev
    exact prev
  }
  {
    intro x y xs ys x_eq_y prev
    exact prev
  }

def sorted_difference.left_empty:
  (ys: List α) -> sorted_difference [] ys = [] := by
  intros; rfl

def sorted_difference.right_empty:
  (xs: List α) -> sorted_difference xs [] = xs := by
  intros xs
  cases xs <;> rfl

def sorted_difference.if_lt:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x < y) ->
  sorted_difference (x::xs) (y::ys) = x::sorted_difference xs (y::ys) := by
  intros
  unfold sorted_difference
  rw [sorted_induction.if_lt]
  assumption

def sorted_difference.if_gt:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x > y) ->
  sorted_difference (x::xs) (y::ys) = sorted_difference (x::xs) ys := by
  intros
  unfold sorted_difference
  rw [sorted_induction.if_gt]
  assumption

def sorted_difference.if_eq:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x = y) ->
  sorted_difference (x::xs) (y::ys) = sorted_difference xs ys := by
  intros
  unfold sorted_difference
  rw [sorted_induction.if_eq]
  assumption

def sorted_difference.refl:
  (xs: List α) -> sorted_difference xs xs = [] := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [if_eq]
    congr
    rfl

def sorted_difference.contains:
  ∀{xs ys: List α},
  ∀{z}, z ∈ sorted_difference xs ys -> z ∈ xs := by
  apply sorted_induction'
  {
    intros ys z z_in_difference
    contradiction
  }
  {
    intros
    assumption
  }
  {
    intros x y xs ys x_lt_y ih z z_in_difference
    rw [if_lt] at z_in_difference
    any_goals assumption
    cases z_in_difference with
    | head _ => apply List.Mem.head
    | tail _ z_in_difference =>
      apply List.Mem.tail
      exact ih z_in_difference
  }
  {
    intros x y xs ys x_gt_y ih z z_in_difference
    rw [if_gt] at z_in_difference
    any_goals assumption
    exact ih z_in_difference
  }
  {
    intros x y xs ys x_eq_y ih z z_in_difference
    rw [if_eq] at z_in_difference
    any_goals assumption
    apply List.Mem.tail
    apply ih
    assumption
  }

def sorted_difference.sorted:
  (xs ys: List α) ->
  is_sorted xs ->
  is_sorted (sorted_difference xs ys) := by
  apply sorted_induction'
  {
    intro _ _
    trivial
  }
  {
    intro x xs sorted_xs
    assumption
  }
  {
    intros x y xs ys x_lt_y ih sorted_xs
    rw [if_lt]
    apply is_sorted.push
    apply ih
    exact sorted_xs.pop
    intro z z_in_difference
    have := contains z_in_difference
    apply is_sorted.contains
    assumption
    apply List.Mem.tail
    assumption
    assumption
  }
  {
    intros x y xs ys x_gt_y ih sorted_xs
    rw [if_gt]
    apply ih
    assumption
    assumption
  }
  {
    intros x y xs ys x_eq_y ih sorted_xs
    rw [if_eq]
    apply ih
    exact sorted_xs.pop
    assumption
  }

def SortedList.difference
  (xs ys: SortedList α) : SortedList α := SortedList.mk (sorted_difference xs.items ys.items) <| by
  apply sorted_difference.sorted
  exact xs.is_sorted
