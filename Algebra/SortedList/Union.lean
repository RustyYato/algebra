import Algebra.SortedList.Basic

variable { α: Sort _ } [LT α] [LE α] [IsLinearOrder α] [@DecidableRel α (· ≤ ·)]

set_option linter.unusedVariables false in
def sorted_union:
  (xs ys: List α) -> List α := by
  apply sorted_induction (ctx := SortedIndCtx.mk (fun _ _ => List α) _ _ _ _ _)
  {
    intro ys
    exact ys
  }
  {
    intro x xs
    exact x::xs
  }
  {
    intro x y _ _ _ prev
    exact x::prev
  }
  {
    intro x y _ _ _ prev
    exact y::prev
  }
  {
    intro x _ _ _ _ prev
    exact x::prev
  }

def sorted_union.left_empty:
  (ys: List α) -> sorted_union [] ys = ys := by
  intro ys
  unfold sorted_union
  rw [sorted_induction.left_empty]

def sorted_union.right_empty:
  (xs: List α) -> sorted_union xs [] = xs := by
  intro xs
  match xs with
  | [] => rfl
  | x::xs =>
  unfold sorted_union
  rw [sorted_induction.right_empty]

def sorted_union.if_lt:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x < y) ->
  sorted_union (x::xs) (y::ys) = x::sorted_union xs (y::ys) := by
  intro x y xs ys x_le_y
  unfold sorted_union
  rw [sorted_induction.if_lt]
  repeat assumption

def sorted_union.if_gt:
  (x y: α) ->
  (xs ys: List α) ->
  (x_gt_y: x > y) ->
  sorted_union (x::xs) (y::ys) = y::sorted_union (x::xs) ys := by
  intro x y xs ys x_gt_y
  unfold sorted_union
  rw [sorted_induction.if_gt]
  repeat assumption

def sorted_union.if_eq:
  (x y: α) ->
  (xs ys: List α) ->
  (x_eq_y: x = y) ->
  sorted_union (x::xs) (y::ys) = x::sorted_union xs ys := by
  intro x y xs ys x_eq_y
  unfold sorted_union
  rw [sorted_induction.if_eq]
  repeat assumption

def sorted_union.comm:
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
    intro x y xs ys x_lt_y ih
    rw [if_lt, if_gt]
    congr
    any_goals assumption
  }
  {
    intro x y xs ys x_gt_y ih
    rw [if_gt, if_lt]
    congr
    any_goals assumption
  }
  {
    intro x y xs ys x_eq_y ih
    rw [if_eq, if_eq]
    congr
    exact x_eq_y.symm
    assumption
  }

def sorted_union.refl:
  (xs: List α) -> sorted_union xs xs = xs := by
  intro xs
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    rw [if_eq]
    congr
    rfl

def sorted_union.idempotent_left:
  (xs ys: List α) ->
  sorted_union (sorted_union xs ys) ys = sorted_union xs ys := by
  apply sorted_induction'
  {
    intro ys
    rw [left_empty, sorted_union.refl]
  }
  {
    intro x xs
    rw [right_empty]
  }
  {
    intro x y xs ys x_le_y ih
    rw [if_lt, if_lt]
    congr
    repeat assumption
  }
  {
    intro x y xs ys x_ge_y ih
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

def sorted_union.idempotent_right:
  (xs ys: List α) ->
  sorted_union xs (sorted_union xs ys) = sorted_union xs ys := by
  intro xs ys
  rw [sorted_union.comm, sorted_union.comm xs, sorted_union.idempotent_left]

def sorted_union.contains:
  ∀{xs ys: List α},
  ∀{z}, z ∈ sorted_union xs ys -> z ∈ xs ∨ z ∈ ys := by
    apply sorted_induction'
    {
      intros
      apply Or.inr
      assumption
    }
    {
      intros
      apply Or.inl
      assumption
    }
    {
      intro x y xs ys x_lt_y ih z z_in_sorted_union
      rw [if_lt] at z_in_sorted_union
      any_goals assumption
      cases z_in_sorted_union with
      | head rest =>
        apply Or.inl
        apply List.Mem.head
      | tail head mem =>
        cases ih mem with
        | inl _ =>
          apply Or.inl
          apply List.Mem.tail
          assumption
        | inr _ =>
          apply Or.inr
          assumption
    }
    {
      intro x y xs ys x_gt_y ih z z_in_sorted_union
      rw [if_gt] at z_in_sorted_union
      any_goals assumption
      cases z_in_sorted_union with
      | head rest =>
        apply Or.inr
        apply List.Mem.head
      | tail head mem =>
        cases ih mem with
        | inl _ =>
          apply Or.inl
          assumption
        | inr _ =>
          apply Or.inr
          apply List.Mem.tail
          assumption
    }
    {
      intro x y xs ys x_eq_y ih z z_in_sorted_union
      rw [if_eq] at z_in_sorted_union
      any_goals assumption
      cases z_in_sorted_union with
      | head rest =>
        apply Or.inl
        apply List.Mem.head
      | tail head mem =>
        cases ih mem with
        | inl _ =>
          apply Or.inl
          apply List.Mem.tail
          assumption
        | inr _ =>
          apply Or.inr
          apply List.Mem.tail
          assumption
    }

def sorted_union.of_contains:
  ∀{xs ys: List α},
  ∀{z}, z ∈ xs ∨ z ∈ ys -> z ∈ sorted_union xs ys := by
    apply sorted_induction'
    {
      intros ys z contains
      cases contains
      contradiction
      assumption
    }
    {
      intros x xs z contains
      cases contains
      assumption
      contradiction
    }
    {
      intro x y xs s x_lt_y ih z z_in_source
      rw [if_lt]
      any_goals assumption
      cases z_in_source with
      | inl z_in_xs =>
        cases z_in_xs with
        | head _ => apply List.Mem.head
        | tail _ _ =>
          apply List.Mem.tail
          apply ih
          apply Or.inl
          assumption
      | inr z_in_ys =>
        apply List.Mem.tail
        apply ih
        apply Or.inr
        assumption
    }
    {
      intro x y xs ys x_gt_y ih z z_in_source
      rw [if_gt]
      any_goals assumption
      cases z_in_source with
      | inl z_in_xs =>
        apply List.Mem.tail
        apply ih
        apply Or.inl
        assumption
      | inr z_in_ys =>
        cases z_in_ys with
        | head _ => apply List.Mem.head
        | tail _ _ =>
          apply List.Mem.tail
          apply ih
          apply Or.inr
          assumption
    }
    {
      intro x y xs ys x_eq_y ih z z_in_source
      rw [if_eq]
      any_goals assumption
      cases z_in_source with
      | inl z_in_xs =>
        cases z_in_xs with
        | head _ => apply List.Mem.head
        | tail _ _ =>
          apply List.Mem.tail
          apply ih
          apply Or.inl
          assumption
      | inr z_in_ys =>
        cases z_in_ys with
        | head _ =>
          rw [x_eq_y]
          apply List.Mem.head
        | tail _ _ =>
          apply List.Mem.tail
          apply ih
          apply Or.inr
          assumption
    }

def sorted_union.lower_bound
  (x z: α) (xs: List α)
  (z_in_xs: z ∈ xs)
  (sorted_xs: is_sorted (x::xs)) :
  x ≤ z
:= by
  apply is_sorted.contains
  assumption
  apply List.Mem.tail
  assumption

 def sorted_union.sorted:
  ∀(xs ys: List α),
  is_sorted xs ->
  is_sorted ys ->
  is_sorted (sorted_union xs ys) := by
    apply sorted_induction'
    {
      intros
      rw [left_empty]
      trivial
    }
    {
      intros
      rw [right_empty]
      trivial
    }
    {
      intro x y xs ys x_lt_y ih sorted_xs sorted_ys
      rw [if_lt]
      any_goals assumption
      apply is_sorted.push
      apply ih
      exact sorted_xs.pop
      exact sorted_ys
      intro z z_in_sorted_union
      cases sorted_union.contains z_in_sorted_union with
      | inl z_in_xs =>
        clear ih
        apply lower_bound
        exact z_in_xs
        assumption
      | inr z_in_ys =>
        clear ih
        apply le_trans
        apply le_of_lt
        assumption
        apply lower_bound
        exact z_in_ys
        apply And.intro
        apply le_refl
        assumption
    }
    {
      intro x y xs ys x_gt_y ih sorted_xs sorted_ys
      rw [if_gt]
      any_goals assumption
      apply is_sorted.push
      apply ih
      exact sorted_xs
      exact sorted_ys.pop
      intro z z_in_sorted_union
      cases sorted_union.contains z_in_sorted_union with
      | inl z_in_xs =>
        clear ih
        apply le_trans
        apply le_of_lt
        assumption
        apply lower_bound
        exact z_in_xs
        apply And.intro
        apply le_refl
        assumption
      | inr z_in_ys =>
        apply lower_bound
        exact z_in_ys
        assumption
    }
    {
      intro x y xs ys x_eq_y ih sorted_xs sorted_ys
      rw [if_eq]
      any_goals assumption
      apply is_sorted.push
      apply ih
      exact sorted_xs.pop
      exact sorted_ys.pop
      intro z z_in_sorted_union
      cases sorted_union.contains z_in_sorted_union with
      | inl z_in_xs =>
        apply lower_bound
        exact z_in_xs
        exact sorted_xs
      | inr z_in_ys =>
        rw [x_eq_y]
        apply lower_bound
        exact z_in_ys
        exact sorted_ys
    }

def SortedList.union
  (xs ys: SortedList α) : SortedList α := SortedList.mk (sorted_union xs.items ys.items) <| by
  apply sorted_union.sorted
  exact xs.is_sorted
  exact ys.is_sorted
