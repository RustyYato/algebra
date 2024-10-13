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

def int.mul.comm (a b: int) : a * b = b * a := by
  rw [mul.def, mul.def]
  unfold mul
  rw [nat.mul.comm]
  congr 1
  cases a <;> cases b <;> rfl

#print axioms int.mul.comm

def int.mul.one_right { b: int } :  b * 1 = b := by
  rw [int.mul.comm, int.mul.one_left]

def int.mul.neg_one_right { b: int } :  b * -1 = -b := by
  rw [int.mul.comm, int.mul.neg_one_left]

def int.mul.assoc (a b c: int) : a * b * c = a * (b * c) := by
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

def int.mul.right_comm (a b c: int) :
  a * b * c = a * c * b := by rw [int.mul.assoc, int.mul.comm b, int.mul.assoc]

#print axioms int.mul.right_comm

def int.mul.left_comm (a b c: int) :
  a * b * c = c * b * a := by rw [int.mul.comm _ c, int.mul.comm a, int.mul.assoc]

#print axioms int.mul.left_comm

def int.mul.comm_left (a b c: int) :
  a * (b * c) = b * (a * c) := by
  rw [←int.mul.assoc, ←int.mul.assoc, int.mul.comm a]

#print axioms int.mul.right_comm

def int.mul.comm_right (a b c: int) :
  a * (b * c) = c * (b * a) := by
  rw [int.mul.comm _ c, int.mul.comm a, int.mul.assoc]

#print axioms int.mul.comm_right

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
        apply le_of_lt
        assumption
        apply nat.succ_le_of_lt h
      | eq =>
        cases eq_of_compare_eq h
        clear h
        rw [←neg_neg (.neg_succ a), ←sub.def, neg.neg_succ, sub.refl, zero_left]
        rw [←neg_left, add.neg_self]
      | gt =>
        rw [int.add.lift_pos_neg_gt_to_nat]
        any_goals (apply gt_of_compare; assumption)
        rw [mul.def]
        unfold mul
        rw [sign.pos, int.Sign.pos_left, abs.pos_succ, ←nat.succ_sub, nat.sub_mul, int.sub.sign_mul]
        rw [sub.def, neg.sign_mul]
        rw [int.mul.abs_sign_mul_neg, int.mul.abs_sign_mul_pos]
        apply nat.mul.of_le_cancel_right
        apply le_of_lt
        apply gt_of_compare
        assumption
        apply nat.succ_le_of_lt
        apply gt_of_compare
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
        apply le_of_lt
        assumption
        apply nat.succ_le_of_lt h
      | eq =>
        cases eq_of_compare_eq h
        clear h
        rw [←neg_neg (.neg_succ a), ←sub.def, neg.neg_succ, sub.refl, zero_left]
        rw [←neg_left, add.neg_self]
      | gt =>
        rw [int.add.lift_pos_neg_gt_to_nat]
        any_goals (apply gt_of_compare; assumption)
        rw [mul.def]
        unfold mul
        rw [sign.pos, int.Sign.pos_left, abs.pos_succ, ←nat.succ_sub, nat.sub_mul, int.sub.sign_mul]
        rw [sub.def, neg.sign_mul]
        rw [int.mul.abs_sign_mul_neg, int.mul.abs_sign_mul_pos]
        apply nat.mul.of_le_cancel_right
        apply le_of_lt
        apply gt_of_compare
        assumption
        apply nat.succ_le_of_lt
        apply gt_of_compare
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
  repeat rw [int.mul.comm k]
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

def int.mul.inc_right (a b: int) : a * b.inc = a * b + a := by
  rw [int.inc.eq_add_one, int.mul.add_right]
  congr
  rw [int.mul.one_right]

#print axioms int.mul.inc_right

def int.mul.inc_left (a b: int) : a.inc * b = a * b + b := by
  rw [int.inc.eq_add_one, int.mul.add_left]
  congr
  rw [int.mul.one_left]

#print axioms int.mul.inc_left

def int.mul.dec_right (a b: int) : a * b.dec = a * b - a := by
  rw [int.dec.eq_add_neg_one, int.mul.add_right]
  congr
  rw [int.mul.neg_one_right]

#print axioms int.mul.inc_right

def int.mul.dec_left (a b: int) : a.dec * b = a * b - b := by
  rw [int.dec.eq_add_neg_one, int.mul.add_left]
  congr
  rw [int.mul.neg_one_left]

#print axioms int.mul.inc_left

def int.mul.lift_nat (a b: nat) : (a: int) * (b: int) = of_nat (a * b) := by
  induction b with
  | zero =>
    have : of_nat 0 = 0 := rfl
    rw [nat.zero_eq, nat.mul_zero, this, mul.zero_right]
  | succ b ih =>
    rw [int.inc.of_nat_succ, int.mul.inc_right, nat.mul_succ, int.add.lift_nat, ih, int.add.comm]

def int.mul.of_eq (a b: int) : ∀k, k ≠ 0 -> a * k = b * k -> a = b := by
  apply int.induction (fun a => ∀b k, k ≠ 0 -> a * k = b * k -> a = b) _ _ _ a
  {
    clear a b
    intro b k k_nz ak_eq_bk
    rw [int.mul.zero_left] at ak_eq_bk
    cases int.mul.eq_zero ak_eq_bk.symm with
    | inr h => contradiction
    | inl h => exact h.symm
  }
  {
    clear a b
    intro a ih b k k_nz ak_eq_bk
    apply int.inc.inj
    apply ih b.inc k k_nz
    rw [int.mul.inc_left, int.mul.inc_left, ak_eq_bk]
  }
  {
    clear a b
    intro a ih b k k_nz ak_eq_bk
    apply int.dec.inj
    apply ih b.dec k k_nz
    rw [int.mul.dec_left, int.mul.dec_left, ak_eq_bk]
  }

#print axioms int.mul.of_eq

def int.mul.compare_left_pos { a b k: int } :
  0 < k ->
  compare a b = compare (a * k) (b * k) := by
  intro h
  cases k with
  | zero | neg_succ k => contradiction
  | pos_succ k =>
    induction k with
    | zero => rw [int.one_eq, int.mul.one_right, int.mul.one_right]
    | succ k ih =>
      rw [int.pos_succ.succ, int.mul.inc_right, int.mul.inc_right]
      rw [ih]
      rw [int.add.compare_strict]
      rfl
      apply ih
      trivial
      trivial

#print axioms int.add.compare_left

def int.abs.mul (a b: int) : int.abs (a * b) = int.abs a * int.abs b := by
  cases a <;> cases b
  any_goals rfl
  all_goals rw [zero_eq, int.abs.zero, int.mul.zero_right, nat.mul_zero]
  rfl; rfl

def int.abs.inc_succ (a: int) : int.abs a.inc ≤ (int.abs a).succ := by
  cases a
  rfl
  rfl
  rename_i a
  cases a
  apply nat.zero_le
  unfold inc
  dsimp
  rw [int.abs.neg_succ, int.abs.neg_succ]
  apply le_trans
  apply le_of_lt
  apply nat.lt_succ_self
  apply le_of_lt
  apply nat.lt_succ_self

def int.abs.dec_succ (a: int) : int.abs a.dec ≤ (int.abs a).succ := by
  rw [←int.abs.neg, int.neg.dec]
  apply le_trans
  apply int.abs.inc_succ
  rw [int.abs.neg]

def int.abs.tri (a b: int) : int.abs (a + b) ≤ int.abs a + int.abs b := by
  have : ∀a b: nat, (int.pos_succ a + int.neg_succ b).abs ≤ a.succ + b.succ := by
    clear a b
    intro a b
    rw [int.add.def, add]
    dsimp
    rw [int.sub_nat.dec]
    induction b generalizing a with
    | zero =>
      rw [int.sub_nat, nat.one_eq, nat.add_one]
      cases a
      decide
      rename_i a
      rw [int.dec]
      dsimp
      rw [int.abs.pos_succ]
      apply le_trans
      apply le_of_lt
      apply nat.lt_succ_self
      apply le_of_lt
      apply nat.lt_succ_self
    | succ b ih =>
      rw [sub_nat, sub_nat.dec]
      apply le_trans
      apply int.abs.dec_succ
      rw [nat.add_succ]
      apply nat.succ_le_succ
      apply ih

  cases a <;> cases b
  rfl
  any_goals rw [int.zero_eq]
  any_goals rw [int.abs.zero]
  any_goals rw [int.add.zero_left]
  any_goals rw [int.add.zero_right]
  any_goals rw [nat.zero_add]
  any_goals rw [nat.add_zero]
  any_goals repeat rw [int.abs.pos_succ]
  any_goals repeat rw [int.abs.neg_succ]
  · rw [int.add.def, add]
    dsimp
    unfold inc
    dsimp
    rw [int.add_nat.pos_succ, int.abs.pos_succ, nat.add_succ]
  · apply this
  · rw [int.add.comm, nat.add.comm]
    apply this
  · rw [←int.abs.neg, int.add.neg, int.neg.neg_succ, int.neg.neg_succ]
    rw [int.add.def, add]
    dsimp
    unfold inc
    dsimp
    rw [int.add_nat.pos_succ, int.abs.pos_succ, nat.add_succ]

def int.abs.tri_lt' (a b: nat) :
(int.pos_succ a + int.neg_succ b).abs < (int.pos_succ a).abs + (int.neg_succ b).abs := by
rw [int.add.def, int.add]
dsimp
rw [int.sub_nat.dec]
induction b with
| zero =>
  rw [int.sub_nat]
  cases a
  trivial
  rw [int.dec]
  dsimp
  rename_i a
  rw [int.abs.pos_succ, int.abs.pos_succ, int.abs.neg_succ]
  rw [nat.one_eq, nat.add_one]
  apply lt_trans
  apply nat.lt_succ_self
  apply nat.lt_succ_self
| succ b ih =>
  rw [int.sub_nat, int.sub_nat.dec]
  apply lt_of_le_of_lt
  apply int.abs.dec_succ
  apply lt_of_lt_of_le
  apply nat.succ_lt_succ
  apply ih
  clear ih
  rw [int.abs.pos_succ, int.abs.neg_succ, int.abs.neg_succ, nat.add_succ _ b.succ]

def int.abs.tri_lt (a b: int) :
  (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b) ->
  int.abs (a + b) < int.abs a + int.abs b := by
  intro h
  cases a <;> cases b
  all_goals (
    cases h <;> rename_i h
    <;> cases h <;> rename_i l r
  )
  any_goals contradiction
  all_goals (rename_i a b; clear l r)
  apply int.abs.tri_lt'
  rw [int.add.comm, nat.add.comm]
  apply int.abs.tri_lt'
