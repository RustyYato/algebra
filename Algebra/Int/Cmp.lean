import Algebra.Order.Basic
import Algebra.Int.Basic
import Algebra.Nat.Cmp

@[simp]
def int.cmp (a b: int): Ordering := match a, b with
  | .zero, .zero => .eq
  | .pos_succ _, .zero => .gt
  | .neg_succ _, .zero => .lt
  | .zero, .pos_succ _ => .lt
  | .zero, .neg_succ _ => .gt
  | .neg_succ _, .pos_succ _ => .lt
  | .pos_succ _, .neg_succ _ => .gt
  | .pos_succ a, .pos_succ b => compare a b
  | .neg_succ a, .neg_succ b => compare b a

instance int.instOrd : Ord int := ⟨ int.cmp ⟩

def int.cmp.def { a b: int } : compare a b = a.cmp b := rfl

instance int.instTotalOrder : TotalOrder int where
  compare_transitive := by
    intro a b c o a_cmp_b b_cmp_c
    cases a <;> cases b
    any_goals assumption
    any_goals (simp [int.instOrd] at a_cmp_b)
    any_goals try (
      cases a_cmp_b
      match c with
      | .pos_succ _ => (rfl; done)
    )
    any_goals try (
      cases a_cmp_b
      match c with
      | .neg_succ _ => (rfl; done)
    )
    {
      rename_i a b
      cases c
      any_goals assumption
      simp [int.instOrd]
      apply TotalOrder.compare_transitive <;> assumption
    }
    {
      rename_i a b
      cases c
      any_goals assumption
      simp [int.instOrd]
      apply TotalOrder.compare_transitive <;> assumption
    }
  compare_eq_refl := by
    intro a
    cases a
    rfl
    simp [int.instOrd]; apply TotalOrder.compare_eq_refl
    simp [int.instOrd]; apply TotalOrder.compare_eq_refl
  eq_of_compare_eq := by
    intro a b a_eq_b
    cases a <;> cases b
    any_goals contradiction
    rfl
    congr
    apply TotalOrder.eq_of_compare_eq <;> assumption
    congr
    simp [int.instOrd] at a_eq_b
    exact (TotalOrder.eq_of_compare_eq a_eq_b).symm
  compare_antisymm := by
    intro a b
    cases a <;> cases b
    any_goals rfl
    repeat (simp [int.instOrd]; apply TotalOrder.compare_antisymm)


#print axioms int.instTotalOrder

def int.neg_lt_zero : int.neg_succ n < 0 := rfl
def int.pos_gt_zero : int.pos_succ n > 0 := rfl
def int.neg_lt_pos : int.neg_succ n < int.pos_succ m := rfl

def int.of_nat.compare (a b: nat) : compare (int.of_nat a) (int.of_nat b) = compare a b := by
  cases a with
  | zero => cases b <;> rfl
  | succ a =>
    cases b with
    | zero => rfl
    | succ b =>
      rw [←int.of_nat.pos, ←int.of_nat.pos]
      rfl
