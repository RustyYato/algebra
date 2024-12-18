def List.allP (list: List α) (f: α -> Prop) : Prop := match list with
   | [] => True
   | x::xs => f x ∧ xs.allP f

def List.anyP (list: List α) (f: α -> Prop) : Prop := match list with
   | [] => False
   | x::xs => f x ∨ xs.anyP f

def List.allP.dec (list : List α) (f: α -> Prop) [decf: ∀x, Decidable (f x)] : Decidable (list.allP f) := by
  cases list with
  | nil => exact (inferInstance: Decidable True)
  | cons x xs => cases List.allP.dec xs f with
    | isTrue h =>
      cases decf x with
      | isTrue g =>
        apply Decidable.isTrue
        apply And.intro <;> assumption
      | isFalse g =>
        apply Decidable.isFalse
        intro and; exact g and.left
    | isFalse h =>
      apply Decidable.isFalse
      intro and; exact h and.right

instance List.allP.instDec (list : List α) (f: α -> Prop) [∀x, Decidable (f x)] : Decidable (list.allP f) := List.allP.dec list f

def List.anyP.dec (list : List α) (f: α -> Prop) [decf: ∀x, Decidable (f x)] : Decidable (list.anyP f) := by
  cases list with
  | nil => exact (inferInstance: Decidable False)
  | cons x xs =>
  cases decf x with
  | isTrue g =>
    apply Decidable.isTrue
    apply Or.inl
    assumption
  | isFalse g =>
  cases List.anyP.dec xs f with
    | isTrue h =>
      apply Decidable.isTrue
      apply Or.inr
      assumption
    | isFalse h =>
      apply Decidable.isFalse
      intro or
      cases or <;> contradiction

instance List.anyP.instDec (list : List α) (f: α -> Prop) [∀x, Decidable (f x)] : Decidable (list.anyP f) := List.anyP.dec list f

def List.allP.of_contains (list: List α) (f: α -> Prop) (h: ∀x, x ∈ list -> f x) : list.allP f := match list with
  | [] => trivial
  | x::xs => by
    apply And.intro
    exact h x (.head _)
    apply List.allP.of_contains
    intro x elem
    apply h
    apply List.Mem.tail _ elem

def List.allP.contains (list: List α) (f: α -> Prop) : list.allP f -> ∀x, x ∈ list -> f x := by
  intro list_all x x_in_list
  induction x_in_list with
  | head _ => exact list_all.left
  | tail _ _ ih =>
    apply ih
    exact list_all.right
