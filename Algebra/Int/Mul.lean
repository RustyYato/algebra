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

#print axioms nat.mul.comm

def int.mul.asoc { a b c: int } : a * b * c = a * (b * c) := by
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

#print axioms nat.mul.assoc
