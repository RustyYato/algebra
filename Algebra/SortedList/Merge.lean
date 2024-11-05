import Algebra.SortedList.Basic

def sorted_merge
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
    exact x::xs
  }
  {
    intro x y xs ys x_lt_y prev
    exact x::prev
  }
  {
    intro x y xs ys x_gt_y prev
    exact y::prev
  }
  {
    intro x y xs ys x_eq_y prev
    exact x::y::prev
  }

def sorted_merge.left_empty
  { α: Sort _ }
  [Ord α] [TotalOrder α]:
  (ys: List α) -> sorted_merge [] ys = ys := by
  intros; rfl

def sorted_merge.right_empty
  { α: Sort _ }
  [Ord α] [TotalOrder α]:
  (xs: List α) -> sorted_merge xs [] = xs := by
  intros xs
  cases xs <;> rfl

def sorted_merge.if_lt
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x < y) ->
  sorted_merge (x::xs) (y::ys) = x::sorted_merge xs (y::ys) := by
  intros
  unfold sorted_merge
  rw [sorted_induction.if_lt]
  assumption

def sorted_merge.if_gt
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x > y) ->
  sorted_merge (x::xs) (y::ys) = y::sorted_merge (x::xs) ys := by
  intros
  unfold sorted_merge
  rw [sorted_induction.if_gt]
  assumption

def sorted_merge.if_eq
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x = y) ->
  sorted_merge (x::xs) (y::ys) = x::y::sorted_merge xs ys := by
  intros
  unfold sorted_merge
  rw [sorted_induction.if_eq]
  assumption

def sorted_merge.contains
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  ∀{xs ys: List α},
  ∀{z}, z ∈ sorted_merge xs ys -> z ∈ xs ∨ z ∈ ys := by
  apply sorted_induction'
  {
    intros ys z z_in_merge
    apply Or.inr
    assumption
  }
  {
    intros x xs z z_in_merge
    apply Or.inl
    assumption
  }
  {
    intros x y xs ys x_lt_y ih z z_in_merge
    rw [if_lt] at z_in_merge
    any_goals assumption
    cases z_in_merge with
    | head _ =>
      apply Or.inl
      apply List.Mem.head
    | tail _ z_in_merge=>
      cases ih z_in_merge with
      | inl z_in_xs =>
        apply Or.inl
        apply List.Mem.tail
        assumption
      | inr z_in_ys =>
        apply Or.inr
        assumption
  }
  {
    intros x y xs ys x_gt_y ih z z_in_merge
    rw [if_gt] at z_in_merge
    any_goals assumption
    cases z_in_merge with
    | head _ =>
      apply Or.inr
      apply List.Mem.head
    | tail _ z_in_merge=>
      cases ih z_in_merge with
      | inl z_in_xs =>
        apply Or.inl
        assumption
      | inr z_in_ys =>
        apply Or.inr
        apply List.Mem.tail
        assumption
  }
  {
    intros x y xs ys x_gt_y ih z z_in_merge
    rw [if_eq] at z_in_merge
    any_goals assumption
    cases z_in_merge with
    | head _ =>
      apply Or.inl
      apply List.Mem.head
    | tail _ z_in_merge =>
    cases z_in_merge with
    | head _ =>
      apply Or.inr
      apply List.Mem.head
    | tail _ z_in_merge =>
    cases ih z_in_merge with
    | inl z_in_xs =>
      apply Or.inl
      apply List.Mem.tail
      assumption
    | inr z_in_xs =>
      apply Or.inr
      apply List.Mem.tail
      assumption
  }

 def sorted_merge.sorted
  { α: Sort _ }
  [Ord α] [tle:TotalOrder α]:
  ∀(xs ys: List α),
  is_sorted xs ->
  is_sorted ys ->
  is_sorted (sorted_merge xs ys) := by
    apply sorted_induction'
    {
      intros
      assumption
    }
    {
      intros
      assumption
    }
    {
      intros x y xs ys x_lt_y ih sorted_xs sorted_ys
      rw [if_lt]
      any_goals assumption
      apply is_sorted.push
      apply ih
      exact sorted_xs.pop
      assumption
      intro z z_in_merge
      cases contains z_in_merge with
      | inl z_in_xs =>
        apply is_sorted.contains
        assumption
        apply List.Mem.tail
        assumption
      | inr z_in_ys =>
        apply le_trans
        apply le_of_lt
        assumption
        apply is_sorted.contains <;> assumption
    }
    {
      intros x y xs ys x_lt_y ih sorted_xs sorted_ys
      rw [if_gt]
      any_goals assumption
      apply is_sorted.push
      apply ih
      assumption
      exact sorted_ys.pop
      intro z z_in_merge
      cases contains z_in_merge with
      | inl z_in_xs =>
        apply le_trans
        apply le_of_lt
        assumption
        apply is_sorted.contains <;> assumption
      | inr z_in_ys =>
        apply is_sorted.contains
        assumption
        apply List.Mem.tail
        assumption
    }
    {
      intros x y xs ys x_eq_y ih sorted_xs sorted_ys
      rw [if_eq]
      any_goals assumption
      apply And.intro
      rw [x_eq_y]
      apply le_refl
      apply is_sorted.push
      apply ih
      exact sorted_xs.pop
      exact sorted_ys.pop
      intro z z_in_merge
      cases contains z_in_merge with
      | inl z_in_xs =>
        rw [←x_eq_y]
        apply is_sorted.contains
        assumption
        apply List.Mem.tail
        assumption
      | inr z_in_ys =>
        apply is_sorted.contains
        assumption
        apply List.Mem.tail
        assumption
    }

def SortedList.merge
  [Ord α] [TotalOrder α]
  (xs ys: SortedList α) : SortedList α := SortedList.mk (sorted_merge xs.items ys.items) <| by
  apply sorted_merge.sorted
  exact xs.is_sorted
  exact ys.is_sorted
