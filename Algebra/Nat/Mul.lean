import Algebra.Nat.Add

def nat.mul (a b: nat) : nat := match a with
  | .zero => .zero
  | .succ a => b + nat.mul a b

instance nat.mul_inst : Mul nat where
  mul := nat.mul

def nat.zero_mul (b: nat) : 0 * b = 0 := rfl

#print axioms nat.zero_mul

def nat.succ_mul (a b: nat) : a.succ * b = b + a * b := rfl

#print axioms nat.succ_mul

def nat.mul_zero (a: nat) : a * 0 = 0 := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [succ_mul, ih]
    rfl

#print axioms nat.mul_zero

def nat.mul_succ (a b: nat) : a * b.succ = a + (a * b) := by
  induction a generalizing b with
  | zero => rfl
  | succ a ih => rw [succ_mul, ih, succ_mul, succ_add, succ_add, add_left_comm]

#print axioms nat.mul_succ

def nat.mul_comm (a b: nat) : a * b = b * a := by
  induction a generalizing b with
  | zero => rw [zero_eq, zero_mul, mul_zero]
  | succ a ih => rw [succ_mul, mul_succ, ih]

#print axioms nat.mul_comm

def nat.add_mul (a b k: nat) : (a + b) * k = a * k + b * k := by
  induction k with
  | zero => rw [zero_eq, mul_zero, mul_zero, mul_zero, add_zero]
  | succ k ih =>
    rw [mul_succ, mul_succ, mul_succ, ih]
    rw [add_assoc, add_assoc]
    apply nat.add_eq_add_right
    rw [nat.add_left_comm]

#print axioms nat.add_mul

def nat.mul_add (a b k: nat) : k * (a + b) = k * a + k * b := by
  repeat rw [mul_comm k]
  apply nat.add_mul

#print axioms nat.mul_add

def nat.mul_assoc (a b c: nat) : (a * b) * c = a * (b * c) := by
  induction a generalizing b c with
  | zero => rw [zero_eq, zero_mul, zero_mul, zero_mul]
  | succ a ih => 
    rw [succ_mul, succ_mul, add_mul]
    apply nat.add_eq_add_right
    apply ih

#print axioms nat.mul_assoc

