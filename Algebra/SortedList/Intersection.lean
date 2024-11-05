import Algebra.SortedList.Basic

variable { α: Sort _ } [LT α] [LE α] [IsLinearOrder α] [@DecidableRel α (· ≤ ·)]

set_option linter.unusedVariables false in
def sorted_intersection:
  (xs ys: List α) -> List α := by
  apply sorted_induction (ctx := SortedIndCtx.mk (fun _ _ => List α) _ _ _ _ _)
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

def sorted_intersection.left_empty:
  (ys: List α) -> sorted_intersection [] ys = [] := by
  intro ys
  rfl

def sorted_intersection.right_empty:
  (xs: List α) -> sorted_intersection xs [] = [] := by
  intro xs
  match xs with
  | [] => rfl
  | _::_ => rfl

def sorted_intersection.if_lt:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x < y) ->
  sorted_intersection (x::xs) (y::ys) = sorted_intersection xs (y::ys) := by
  intro x y xs ys x_lt_y
  unfold sorted_intersection
  rw [sorted_induction.if_lt]
  repeat assumption

def sorted_intersection.if_gt:
  (x y: α) ->
  (xs ys: List α) ->
  (x_ge_y: x > y) ->
  sorted_intersection (x::xs) (y::ys) = sorted_intersection (x::xs) ys := by
  intro x y xs ys x_gt_y
  unfold sorted_intersection
  rw [sorted_induction.if_gt]
  repeat assumption

def sorted_intersection.if_lt':
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

def sorted_intersection.if_gt':
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

def sorted_intersection.if_eq:
  (x y: α) ->
  (xs ys: List α) ->
  (x_eq_y: x = y) ->
  sorted_intersection (x::xs) (y::ys) = x::sorted_intersection xs ys := by
  intro x y xs ys x_eq_y
  unfold sorted_intersection
  rw [sorted_induction.if_eq]
  repeat assumption

 def sorted_intersection.comm:
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

def sorted_intersection.refl:
  (xs: List α) -> sorted_intersection xs xs = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [if_eq]
    congr
    rfl

def sorted_intersection.contains:
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

def sorted_intersection.of_contains:
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
        have := lt_irrefl  x_lt_y
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
        have := not_lt_of_le x_ge_y x_lt_y
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
          have := lt_irrefl x_gt_y
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
        have := not_lt_of_le y_ge_x x_gt_y
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

def sorted_intersection.idempotent_left:
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
    apply lt_of_lt_of_le <;> assumption
  }
  {
    intro x y xs ys x_eq_y ih sorted_xs
    rw [if_eq, if_eq]
    rw [ih]
    exact sorted_xs.pop
    repeat assumption
  }

def sorted_intersection.idempotent_right:
  (xs ys: List α) ->
  is_sorted ys ->
  sorted_intersection xs (sorted_intersection xs ys) = sorted_intersection xs ys := by
  intro xs ys sorted_ys
  rw [comm, comm xs ys]
  apply idempotent_left <;> assumption

def sorted_intersection.sorted:
  (xs ys: List α) ->
  is_sorted xs ->
  is_sorted ys ->
  is_sorted (sorted_intersection xs ys) := by
  apply sorted_induction'
  {
    intros
    trivial
  }
  {
    intros
    trivial
  }
  {
    intros x y xs ys x_lt_y ih sorted_xs sorted_ys
    rw [if_lt]
    apply ih
    exact sorted_xs.pop
    assumption
    assumption
  }
  {
    intros x y xs ys x_gt_y ih sorted_xs sorted_ys
    rw [if_gt]
    apply ih
    assumption
    exact sorted_ys.pop
    assumption
  }
  {
    intros x y xs ys x_eq_y ih sorted_xs sorted_ys
    rw [if_eq]
    apply is_sorted.push
    apply ih
    exact sorted_xs.pop
    exact sorted_ys.pop
    {
      intro z z_in_interesction
      have ⟨ z_in_xsk, _ ⟩  := contains z_in_interesction
      apply is_sorted.contains
      exact sorted_xs
      apply List.Mem.tail
      assumption
    }
    assumption
  }

def SortedList.intersection (xs ys: SortedList α) : SortedList α := SortedList.mk (sorted_intersection xs.items ys.items) <| by
  apply sorted_intersection.sorted
  exact xs.is_sorted
  exact ys.is_sorted
