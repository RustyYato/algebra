import Algebra.Nat.Sub

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

def nat.one_mul (a: nat) : 1 * a = a := by
  rw [←one_eq, succ_mul, zero_eq, zero_mul, add_zero]

#print axioms nat.one_mul

def nat.mul_one (a: nat) : a * 1 = a := by
  rw [←one_eq, mul_succ, zero_eq, mul_zero, add_zero]

#print axioms nat.mul_one

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

def nat.mul_ge (a b: nat) (b_nz: 0 < b) : a ≤ a * b := by
  match b with
  | .zero => contradiction
  | .succ b =>
    rw [mul_succ]
    apply le_add_right

#print axioms nat.mul_ge

def nat.mul_gt (a b: nat) (a_nz: 0 < a) (b_nz: 1 < b) : a < a * b := by
  match b with
  | .zero | .succ .zero => contradiction
  | .succ (.succ b) =>
    rw [mul_succ, mul_succ]
    match a with
    | .succ a =>
    rw [nat.succ_add, add_left_comm, succ_add]
    apply succ_lt_succ
    apply lt_of_le_and_lt _ (lt_succ_self _)
    apply le_add_right

#print axioms nat.mul_gt

def nat.to_mul_lt_mul (a b c: nat) (a_nz: 0 < a) : b < c -> a * b < a * c := by
  induction b generalizing a c with
  | zero =>
    intro h
    match c with
    | .succ c =>
    match a with
    | .succ a =>
    rw [zero_eq, mul_zero, succ_mul, succ_add]
    apply nat.zero_lt_succ
  | succ b ih =>
    intro h
    match a with
    | .succ a =>
    match c with
    | .succ c =>
    rw [mul_succ, mul_succ]
    apply nat.add_of_lt_cancel_left
    apply ih
    apply nat.zero_lt_succ
    exact h

#print axioms nat.to_mul_lt_mul


def nat.mul_lt_mul (a b c: nat) (a_nz: 0 < a) : a * b < a * c -> b < c := by
  induction c generalizing a b with
  | zero =>
    intro h
    rw [zero_eq, mul_zero] at h
    have := nat.not_lt_zero h
    contradiction
  | succ c ih =>
    intro h
    rw [mul_succ] at h
    cases b with
    | zero => trivial
    | succ b =>
      rw [mul_succ] at h
      apply ih a b a_nz
      apply nat.add_lt_cancel_left
      exact h

#print axioms nat.mul_lt_mul

def nat.mul_le_cancel_left (a b c: nat) : b ≤ c -> a * b ≤ a * c := by
  induction c generalizing a b with
  | zero =>
    intro h
    rw [le_zero h]
    apply le_refl
  | succ c ih =>
    intro h
    cases b with
    | zero =>
      rw [zero_eq, mul_zero]
      apply zero_le
    | succ b =>
    have := ih a b h
    rw [mul_succ, mul_succ]
    apply nat.add_le_cancel_left
    assumption

#print axioms nat.mul_lt_mul



def nat.mul_sub (a b c: nat) : a * (b - c) = a * b - a * c := by
  induction b generalizing a c with
  | zero => rw [zero_eq, zero_sub, mul_zero, zero_sub]
  | succ b ih =>
    cases c with
    | zero => rw [zero_eq, sub_zero, mul_zero, sub_zero]
    | succ c =>
      rw [succ_sub_succ, mul_succ, mul_succ, sub_add, add_comm, ←add_sub, sub_refl, add_zero]
      apply ih
      apply TotalOrder.le_refl

#print axioms nat.mul_sub
