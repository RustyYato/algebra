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
  apply sorted_induction'
  {
    intro ys z z_in_intersection
    contradiction
  }
  {
    intro x xs z z_in_intersection
    contradiction
  }
  {
    intro x y xs ys x_lt_y ih z z_in_intersection
    rw [if_lt] at z_in_intersection
    have ⟨ z_in_xs, z_in_ys ⟩ := ih z_in_intersection
    apply And.intro
    apply List.Mem.tail
    repeat assumption
  }
  {
    intro x y xs ys x_gt_y ih z z_in_intersection
    rw [if_gt] at z_in_intersection
    have ⟨ z_in_xs, z_in_ys ⟩ := ih z_in_intersection
    apply And.intro
    assumption
    apply List.Mem.tail
    repeat assumption
  }
  {
    intro x y xs ys x_eq_y ih z z_in_intersection
    rw [if_eq] at z_in_intersection
    any_goals assumption
    cases z_in_intersection with
    | head _ =>
      apply And.intro
      apply List.Mem.head
      rw [x_eq_y]
      apply List.Mem.head
    | tail _ z_in_intersection =>
      have ⟨ z_in_xs, z_in_ys ⟩ := ih z_in_intersection
      apply And.intro <;> (apply List.Mem.tail; assumption)
  }

#print axioms sorted_intersection.contains

def sorted_intersection.of_contains
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  ∀{xs ys: List α},
  is_sorted xs ->
  is_sorted ys ->
  ∀{z}, z ∈ xs -> z ∈ ys -> z ∈ sorted_intersection xs ys := by
  apply sorted_induction'
  {
    intros; contradiction
  }
  {
    intros; contradiction
  }
  {
    intros x y xs ys x_lt_y ih sorted_xs sorted_ys z z_in_xs z_in_ys
    rw [if_lt]
    any_goals assumption
    cases z_in_ys with
    | head _ =>
      cases z_in_xs with
      | head _ =>
        have := TotalOrder.lt_irrefl  x_lt_y
        contradiction
      | tail _ z_in_xs => 
        apply ih
        exact sorted_xs.pop
        assumption
        assumption
        apply List.Mem.head
    | tail _ z_in_ys =>
      cases z_in_xs with
      | tail _ z_in_xs =>
        apply ih
        exact sorted_xs.pop
        assumption
        assumption
        apply List.Mem.tail
        assumption
      | head _ => 
        have x_ge_y := (sorted_ys.first) x z_in_ys
        have := TotalOrder.not_lt_and_ge x_lt_y x_ge_y
        contradiction
  }
  {
    intros x y xs ys x_gt_y ih sorted_xs sorted_ys z z_in_xs z_in_ys
    rw [if_gt]
    any_goals assumption
    cases z_in_xs with
    | head _ =>
      cases z_in_ys with
      | head _ => 
          have := TotalOrder.lt_irrefl x_gt_y
          contradiction
      | tail _ z_in_ys => 
        apply ih
        assumption
        exact sorted_ys.pop
        apply List.Mem.head
        assumption
    | tail _ z_in_xs =>
      cases z_in_ys with
      | tail _ z_in_ys => 
        apply ih
        assumption
        exact sorted_ys.pop
        apply List.Mem.tail
        assumption
        assumption
      | head _ =>
        have y_ge_x := (sorted_xs.first) y z_in_xs
        have := TotalOrder.not_lt_and_ge x_gt_y y_ge_x
        contradiction
  }
  {
    intro x y xs ys x_eq_y ih sorted_xs sorted_ys z z_in_xs z_in_ys
    rw [if_eq]
    any_goals assumption
    cases z_in_xs with
    | head _ => apply List.Mem.head
    | tail _ z_in_xs =>
      cases z_in_ys with
      | head _ =>
        rw [x_eq_y]
        apply List.Mem.head
      | tail _ z_in_ys =>
        apply List.Mem.tail
        apply ih
        exact sorted_xs.pop
        exact sorted_ys.pop
        repeat assumption
  }

#print axioms sorted_intersection.of_contains

def sorted_intersection.idempotent_left
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs ys: List α) ->
  is_sorted xs ->
  sorted_intersection (sorted_intersection xs ys) ys = sorted_intersection xs ys := by
  apply sorted_induction'
  {
    intro ys _
    rw [left_empty, left_empty]
  }
  {
    intro x xs _
    rw [right_empty, right_empty]
  }
  {
    intro x y xs ys x_lt_y ih sorted_xs
    rw [if_lt]
    exact ih sorted_xs.pop
    repeat assumption
  }
  {
    intro x y xs ys x_gt_y ih sorted_xs
    rw [if_gt, if_gt']
    apply ih
    exact sorted_xs
    any_goals assumption
    intro x' x_in_sorted_intersection
    have ⟨ x'_in_xs, _ ⟩  := contains x_in_sorted_intersection
    have := sorted_xs.contains x' x xs x'_in_xs
    apply TotalOrder.lt_of_lt_and_le <;> assumption
  }
  {
    intro x y xs ys x_eq_y ih sorted_xs
    rw [if_eq, if_eq]
    rw [ih]
    exact sorted_xs.pop
    repeat assumption
  }

#print axioms sorted_intersection.idempotent_left

def sorted_intersection.idempotent_right
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs ys: List α) ->
  is_sorted ys ->
  sorted_intersection xs (sorted_intersection xs ys) = sorted_intersection xs ys := by
  intro xs ys sorte_ys
  rw [comm, comm xs ys]
  apply idempotent_left <;> assumption

#print axioms sorted_intersection.idempotent_right

