import Algebra.Int.Abs
import Algebra.Int.Add
import Algebra.Nat.Mul

def int.mul (a b: int) : int := a.sign * b.sign * (a.abs * b.abs)

#print axioms int.mul

instance int.mul.inst : Mul int := ⟨ int.mul ⟩ 

def int.mul.def { a b: int } : a * b = int.mul a b := rfl

def int.mul.zero_left { b: int } :  0 * b = 0 := by
  rw [mul.def]
  unfold mul
  rw [int.sign.zero, int.Sign.zero_left, int.Sign.int_zero]

#print axioms int.mul.zero_left

def int.mul.zero_right { b: int } :  b * 0 = 0 := by
  rw [mul.def]
  unfold mul
  rw [int.sign.zero, int.Sign.zero_right, int.Sign.int_zero]

#print axioms int.mul.zero_right

def int.mul.one_left { b: int } :  1 * b = b := by
  rw [mul.def]
  unfold mul
  rw [←one_eq, sign.pos, int.Sign.pos_left]
  conv => {
    lhs; rhs; lhs
    unfold abs
    simp
  }
  rw [nat.one_eq, nat.one_mul, abs.sign]

def int.mul.neg_one_left { b: int } :  -1 * b = -b := by
  rw [mul.def]
  unfold mul
  rw [←one_eq, neg.pos_succ, sign.neg, int.Sign.neg_left]
  conv => {
    lhs; rhs; lhs
    unfold abs
    simp
  }
  rw [nat.one_eq, nat.one_mul, abs.flip_sign]

def int.mul.neg_left { a b: int } : -(a * b) = -a * b := by
  cases a <;> cases b <;> rfl

#print axioms int.mul.neg_left

def int.mul.neg_right { a b: int } : -(a * b) = a * -b := by
  cases a <;> cases b <;> rfl

#print axioms int.mul.neg_right

def int.mul.comm { a b: int } : a * b = b * a := by
  rw [mul.def, mul.def]
  unfold mul
  rw [nat.mul.comm]
  congr 1
  cases a <;> cases b <;> rfl

#print axioms int.mul.comm

def int.mul.assoc { a b c: int } : a * b * c = a * (b * c) := by
  repeat rw [mul.def]
  unfold mul
  rw [int.abs.sign_mul]
  rw [int.sign.of_sign_mul]
  rw [int.sign.of_sign_mul]
  congr 1
  { -- sign eq
    cases a <;> cases b <;> cases c <;> rfl
  }
  rw [int.abs.sign_mul]
  apply nat.mul.assoc
  {
    cases b <;> cases c
    any_goals (apply Or.inr; rfl)
    any_goals (apply Or.inl; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }
  {
    cases b <;> cases c
    any_goals (apply Or.inl; rfl)
    any_goals (apply Or.inr; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }
  {
    cases a <;> cases b
    any_goals (apply Or.inl; rfl)
    any_goals (apply Or.inr; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }
  {
    cases a <;> cases b
    any_goals (apply Or.inr; rfl)
    any_goals (apply Or.inl; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }

#print axioms int.mul.assoc
  
def int.mul.abs_sign_mul_pos : ∀(x: nat) (y: int), y.sign * (nat.succ x * y.abs) = (int.pos_succ x) * y := by intro x y; cases y <;> rfl
def int.mul.abs_sign_mul_neg : ∀(x: nat) (y: int), y.sign.flip * (nat.succ x * y.abs) = (int.neg_succ x) * y := by intro x y; cases y <;> rfl

def int.mul.add_left { a b k: int } : (a + b) * k = a * k + b * k := by
  cases a with
  | zero => rw [zero_eq, add.zero_left, zero_left, add.zero_left]
  | pos_succ a =>
    cases b with
    | zero => rw [zero_eq, add.zero_right, zero_left, add.zero_right]
    | pos_succ b =>
      rw [int.add.lift_pos_pos_to_nat, mul.def]
      unfold mul
      rw [sign.pos, int.Sign.pos_left, int.abs.pos_succ]
      rw [←nat.add_succ, ←nat.succ_add, nat.add_mul, int.add.sign_mul]
      congr 1 <;> apply int.mul.abs_sign_mul_pos
    | neg_succ b =>
      cases h:compare a b with
      | lt => 
        rw [int.add.lift_pos_neg_lt_to_nat]
        any_goals assumption
        rw [mul.def]
        unfold mul
        rw [sign.neg, int.Sign.neg_left, abs.neg_succ, ←nat.succ_sub, nat.sub_mul, int.sub.sign_mul]
        rw [sub.def, neg.sign_mul, Sign.flip_flip]
        rw [int.mul.abs_sign_mul_neg, int.mul.abs_sign_mul_pos]
        apply add.comm
        apply nat.mul.of_le_cancel_right
        apply TotalOrder.le_of_lt
        assumption
        apply nat.succ_le_of_lt h
      | eq =>
        cases TotalOrder.eq_of_compare_eq h
        clear h
        rw [←neg_neg (.neg_succ a), ←sub.def, neg.neg_succ, sub.refl, zero_left]
        rw [←neg_left, add.neg_self]
      | gt =>
        rw [int.add.lift_pos_neg_gt_to_nat]
        any_goals (apply TotalOrder.gt_of_compare; assumption)
        rw [mul.def]
        unfold mul
        rw [sign.pos, int.Sign.pos_left, abs.pos_succ, ←nat.succ_sub, nat.sub_mul, int.sub.sign_mul]
        rw [sub.def, neg.sign_mul]
        rw [int.mul.abs_sign_mul_neg, int.mul.abs_sign_mul_pos]
        apply nat.mul.of_le_cancel_right
        apply TotalOrder.le_of_lt
        apply TotalOrder.gt_of_compare
        assumption
        apply nat.succ_le_of_lt
        apply TotalOrder.gt_of_compare
        assumption
  | neg_succ a =>
    cases b with
    | zero => rw [zero_eq, add.zero_right, zero_left, add.zero_right]
    | pos_succ b =>
      rw [add.comm, @add.comm (_ * k)]

      cases h:compare b a with
      | lt => 
        rw [int.add.lift_pos_neg_lt_to_nat]
        any_goals assumption
        rw [mul.def]
        unfold mul
        rw [sign.neg, int.Sign.neg_left, abs.neg_succ, ←nat.succ_sub, nat.sub_mul, int.sub.sign_mul]
        rw [sub.def, neg.sign_mul, Sign.flip_flip]
        rw [int.mul.abs_sign_mul_neg, int.mul.abs_sign_mul_pos]
        apply add.comm
        apply nat.mul.of_le_cancel_right
        apply TotalOrder.le_of_lt
        assumption
        apply nat.succ_le_of_lt h
      | eq =>
        cases TotalOrder.eq_of_compare_eq h
        clear h
        rw [←neg_neg (.neg_succ a), ←sub.def, neg.neg_succ, sub.refl, zero_left]
        rw [←neg_left, add.neg_self]
      | gt =>
        rw [int.add.lift_pos_neg_gt_to_nat]
        any_goals (apply TotalOrder.gt_of_compare; assumption)
        rw [mul.def]
        unfold mul
        rw [sign.pos, int.Sign.pos_left, abs.pos_succ, ←nat.succ_sub, nat.sub_mul, int.sub.sign_mul]
        rw [sub.def, neg.sign_mul]
        rw [int.mul.abs_sign_mul_neg, int.mul.abs_sign_mul_pos]
        apply nat.mul.of_le_cancel_right
        apply TotalOrder.le_of_lt
        apply TotalOrder.gt_of_compare
        assumption
        apply nat.succ_le_of_lt
        apply TotalOrder.gt_of_compare
        assumption
    | neg_succ b =>
      apply int.neg.inj
      rw [neg_left, add.neg, add.neg, neg_left, neg_left, neg.neg_succ, neg.neg_succ]
      rw [int.add.lift_pos_pos_to_nat, mul.def]
      unfold mul
      rw [sign.pos, int.Sign.pos_left, int.abs.pos_succ]
      rw [←nat.add_succ, ←nat.succ_add, nat.add_mul, int.add.sign_mul]
      congr 1 <;> apply int.mul.abs_sign_mul_pos

#print axioms int.mul.add_left

def int.mul.add_right { a b k: int } : k * (a + b) = k * a + k * b := by
  repeat rw [@int.mul.comm k]
  apply int.mul.add_left

#print axioms int.mul.add_right

def int.mul.sub_left { a b k: int } : (a - b) * k = a * k - b * k := by
  rw [sub.def, add_left, ←neg_left, ←sub.def]

#print axioms int.mul.sub_left

def int.mul.sub_right { a b k: int } : k * (a - b) = k * a - k * b := by
  rw [sub.def, add_right, ←neg_right, ←sub.def]

#print axioms int.mul.sub_right

