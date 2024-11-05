import Algebra.SortedList.Basic

def sorted_symm_difference
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
    exact prev
  }

def sorted_symm_difference.left_empty
  { α: Sort _ }
  [Ord α] [TotalOrder α]:
  (ys: List α) -> sorted_symm_difference [] ys = ys := by
  intros; rfl

def sorted_symm_difference.right_empty
  { α: Sort _ }
  [Ord α] [TotalOrder α]:
  (xs: List α) -> sorted_symm_difference xs [] = xs := by
  intros xs
  cases xs <;> rfl

def sorted_symm_difference.if_lt
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x < y) ->
  sorted_symm_difference (x::xs) (y::ys) = x::sorted_symm_difference xs (y::ys) := by
  intros
  unfold sorted_symm_difference
  rw [sorted_induction.if_lt]
  assumption

def sorted_symm_difference.if_gt
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x > y) ->
  sorted_symm_difference (x::xs) (y::ys) = y::sorted_symm_difference (x::xs) ys := by
  intros
  unfold sorted_symm_difference
  rw [sorted_induction.if_gt]
  assumption

def sorted_symm_difference.if_eq
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (x y: α) ->
  (xs ys: List α) ->
  (x_le_y: x = y) ->
  sorted_symm_difference (x::xs) (y::ys) = sorted_symm_difference xs ys := by
  intros
  unfold sorted_symm_difference
  rw [sorted_induction.if_eq]
  assumption

def sorted_symm_difference.comm
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs ys: List α) -> sorted_symm_difference xs ys = sorted_symm_difference ys xs := by
  apply sorted_induction'
  {
    intros ys
    rw [left_empty, right_empty]
  }
  {
    intros x xs
    rw [left_empty, right_empty]
  }
  {
    intros x y xs ys x_lt_y ih
    rw [if_lt, if_gt]
    congr
    repeat assumption
  }
  {
    intros x y xs ys x_gt_y ih
    rw [if_gt, if_lt]
    congr
    repeat assumption
  }
  {
    intros x y xs ys x_eq_y ih
    rw [if_eq, if_eq]
    exact ih
    exact x_eq_y.symm
    assumption
  }

def sorted_symm_difference.refl
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  (xs: List α) -> sorted_symm_difference xs xs = [] := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [if_eq]
    congr
    rfl

def sorted_symm_difference.contains
  { α: Sort _ }
  [Ord α] [tle: TotalOrder α]:
  ∀{xs ys: List α},
  ∀{z}, z ∈ sorted_symm_difference xs ys -> z ∈ xs ∨ z ∈ ys := by
  apply sorted_induction'
  {
    intros ys z z_in_difference
    apply Or.inr
    assumption
  }
  {
    intros x xs z z_in_difference
    apply Or.inl
    assumption
  }
  {
    intros x y xs ys x_lt_y ih z z_in_difference
    rw [if_lt] at z_in_difference
    any_goals assumption
    cases z_in_difference with
    | head _ =>
      apply Or.inl
      apply List.Mem.head
    | tail _ z_in_difference =>
    cases ih z_in_difference with
    | inl h =>  apply Or.inl; apply List.Mem.tail; assumption
    | inr h => apply Or.inr ; assumption
  }
  {
    intros x y xs ys x_gt_y ih z z_in_difference
    rw [if_gt] at z_in_difference
    any_goals assumption
    cases z_in_difference with
    | head _ =>
      apply Or.inr
      apply List.Mem.head
    | tail _ z_in_difference =>
    cases ih z_in_difference with
    | inl h =>  apply Or.inl; assumption
    | inr h => apply Or.inr ; apply List.Mem.tail; assumption
  }
  {
    intros x y xs ys x_eq_y ih z z_in_difference
    rw [if_eq] at z_in_difference
    any_goals assumption
    cases ih z_in_difference with
    | inl h =>  apply Or.inl; apply List.Mem.tail; assumption
    | inr h => apply Or.inr ; apply List.Mem.tail; assumption
  }

def sorted_symm_difference.sorted
  { a: Sort _ }
  [Ord α] [TotalOrder α]:
  (xs ys: List α) ->
  is_sorted xs ->
  is_sorted ys ->
  is_sorted (sorted_symm_difference xs ys) := by
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
    exact sorted_ys
    intro z z_in_difference
    cases contains z_in_difference with
    | inl z_in_xs  =>
      apply is_sorted.contains
      assumption
      apply List.Mem.tail
      assumption
    | inr z_in_ys =>
      apply le_trans
      apply le_of_lt
      assumption
      apply is_sorted.contains
      assumption
      assumption
  }
  {
    intros x y xs ys x_gt_y ih sorted_xs sorted_ys
    rw [if_gt]
    any_goals assumption
    apply is_sorted.push
    apply ih
    exact sorted_xs
    exact sorted_ys.pop
    intro z z_in_difference
    cases contains z_in_difference with
    | inl z_in_xs  =>
      apply le_trans
      apply le_of_lt
      assumption
      apply is_sorted.contains
      assumption
      assumption
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
    apply ih
    exact sorted_xs.pop
    exact sorted_ys.pop
  }

def SortedList.symm_difference
  [Ord α] [TotalOrder α]
  (xs ys: SortedList α) : SortedList α := SortedList.mk (sorted_symm_difference xs.items ys.items) <| by
  apply sorted_symm_difference.sorted
  assumption
  exact xs.is_sorted
  exact ys.is_sorted
