import Algebra.Int.Add
import Algebra.Int.Abs
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

def int.mul.pos_pos_is_pos { a b: int } : 0 < a -> 0 < b -> 0 < a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  rfl

#print axioms int.mul.pos_pos_is_pos

def int.mul.neg_neg_is_pos { a b: int } : 0 > a -> 0 > b -> 0 < a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  rfl

#print axioms int.mul.neg_neg_is_pos

def int.mul.pos_neg_is_neg { a b: int } : 0 < a -> 0 > b -> 0 > a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  rfl

#print axioms int.mul.pos_neg_is_neg

def int.mul.neg_pos_is_neg { a b: int } : 0 > a -> 0 < b -> 0 > a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  rfl

#print axioms int.mul.neg_pos_is_neg

def int.mul.eq_zero { a b: int } : a * b = 0 -> a = 0 ∨ b = 0 := by
  intro ab_eq_zero
  cases a <;> cases b
  any_goals (apply Or.inl; rfl)
  any_goals (apply Or.inr; rfl)
  all_goals contradiction

#print axioms int.mul.eq_zero

def int.mul.eq_pos { a b: int } : a * b > 0 -> (a < 0 ∧ b < 0) ∨ (a > 0 ∧ b > 0) := by
  intro ab_gt_zero
  cases a <;> cases b
  any_goals contradiction
  apply Or.inr <;> apply And.intro <;> assumption
  apply Or.inl <;> apply And.intro <;> assumption

#print axioms int.mul.eq_pos

def int.mul.eq_neg { a b: int } : a * b < 0 -> (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) := by
  intro ab_lt_zero
  cases a <;> cases b
  any_goals contradiction
  apply Or.inr <;> apply And.intro <;> assumption
  apply Or.inl <;> apply And.intro <;> assumption

#print axioms int.mul.eq_neg

def int.sign_mul.mul_of_nat { s: int.Sign } { a b: nat } : s * a * (b: int) = s * (a * b) := by
  cases b with
  | zero =>
    unfold of_nat
    simp only
    rw [zero_eq, mul.zero_right, nat.zero_eq, nat.mul_zero]
    cases s <;> rfl
  | succ b =>
  cases a with
  | zero => 
    cases s <;> rfl
  | succ a =>
    unfold of_nat
    simp only

    rw [int.mul.def]
    unfold mul
    rw [sign.of_sign_mul, sign.pos, int.Sign.pos_right, abs.pos_succ]
    {
      cases s with
      | zero => rfl
      | pos =>
        repeat rw [int.Sign.int_pos]
        rw [abs.of_nat]
      | neg =>
        repeat rw [int.Sign.int_neg]
        rw [abs.neg_of_nat]
    }
    {
      apply Or.inr
      apply nat.noConfusion
    }

#print axioms int.sign_mul.mul_of_nat

