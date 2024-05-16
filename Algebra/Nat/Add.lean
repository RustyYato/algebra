import Algebra.Nat.Cmp

def nat.add (a b: nat) : nat := match a with
  | .zero => b
  | .succ a => .succ (add a b)

instance nat.add_inst : Add nat where
  add := nat.add

def nat.zero_add (b: nat) : 0 + b = b := rfl

#print axioms nat.zero_add

def nat.succ_add (a b: nat) : a.succ + b = (a + b).succ := rfl 

#print axioms nat.succ_add

def nat.add_zero (a: nat) : a + 0 = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [succ_add]
    rw [ih]

#print axioms nat.add_zero

def nat.add_succ (a b: nat) : a + b.succ = (a + b).succ := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [succ_add, succ_add]
    rw [ih]

#print axioms nat.add_succ

def nat.add_comm (a b: nat) : a + b = b + a := by
  induction a with
  | zero =>
    rw [zero_eq, zero_add, add_zero]
  | succ a ih =>
    rw [succ_add, add_succ, ih]

#print axioms nat.add_comm

def nat.add_assoc (a b c: nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [zero_eq, zero_add, zero_add]
  | succ a iha =>
    repeat rw [succ_add]
    rw [iha]

#print axioms nat.add_assoc

def nat.le_add_right (a b: nat) : a ≤ a + b := by
  induction b with
  | zero =>
    rw [zero_eq, add_zero]
    apply nat.le_refl
  | succ b ih =>
    rw [add_succ]
    apply nat.le_trans
    exact ih
    apply nat.le_of_lt
    apply nat.lt_succ_self

#print axioms nat.le_add_right

def nat.le_add_left (a b: nat) : b ≤ a + b := by
  rw [add_comm]
  apply le_add_right

#print axioms nat.le_add_left

def nat.eq_zero_of_add_eq_left (a b: nat) : b = a + b -> a = 0 := by
  intro add_eq
  induction b with
  | zero => 
    rw [zero_eq, add_zero] at add_eq
    exact add_eq.symm
  | succ b ih =>
    apply ih
    rw [add_succ] at add_eq
    exact nat.succ.inj add_eq
  
#print axioms nat.eq_zero_of_add_eq_left

def nat.eq_zero_of_add_eq_right (a b: nat) : a = a + b -> b = 0 := by
  intro add_eq
  rw [add_comm] at add_eq
  apply eq_zero_of_add_eq_left
  assumption
  
#print axioms nat.eq_zero_of_add_eq_right

def nat.lt_add_right_nz (a b: nat) : 0 < b -> a < a + b := by
  intro zero_lt_b
  induction b with
  | zero =>
    contradiction
  | succ b ih =>
    cases nat.lt_or_eq_of_le <|nat.le_of_lt_succ zero_lt_b with
    | inl zero_lt_b =>
      rw [add_succ]
      apply nat.lt_trans
      apply ih
      assumption
      apply nat.lt_succ_self
    | inr zero_eq_b =>
      rw [←zero_eq_b, add_succ, add_zero]
      apply nat.lt_succ_self

#print axioms nat.lt_add_right_nz

def nat.lt_add_left_nz (a b: nat) : 0 < a -> b < a + b := by
  rw [add_comm]
  apply lt_add_right_nz

#print axioms nat.lt_add_left_nz

def nat.add_eq_add (a b c d: nat) : a = c -> b = d -> a + b = c + d := by
  intro a_eq_c b_eq_d
  rw [a_eq_c, b_eq_d]

#print axioms nat.add_eq_add

def nat.add_eq_add_left (a b c: nat) : a = c -> a + b = c + b := by
  intro a_eq_c
  rw [a_eq_c]

#print axioms nat.add_eq_add_left

def nat.add_eq_add_right (a b d: nat) : b = d -> a + b = a + d := by
  intro b_eq_d
  rw [b_eq_d]

#print axioms nat.add_eq_add_right

def nat.add_cancel_left {a b k: nat} : k + a = k + b -> a = b := by
  intro k_add
  induction k with
  | zero => 
    rw [zero_eq, zero_add, zero_add] at k_add
    exact k_add
  | succ k ih =>
    rw [succ_add, succ_add] at k_add
    apply ih
    exact nat.succ.inj k_add

#print axioms nat.add_cancel_left

def nat.add_cancel_right {a b k: nat} : a + k = b + k -> a = b := by
  rw [add_comm _ k, add_comm _ k]
  exact nat.add_cancel_left

#print axioms nat.add_cancel_right

def nat.add_of_lt_cancel_left {a b k: nat} : a < b -> k + a < k + b := by
  intro k_add
  induction k with
  | zero => exact k_add
  | succ k ih =>
    apply nat.succ_lt_succ
    exact ih

#print axioms nat.add_of_lt_cancel_left

def nat.add_of_lt_cancel_right {a b k: nat} : a < b -> a + k < b + k := by
  intro a_lt_b
  rw [add_comm _ k, add_comm _ k]
  exact nat.add_of_lt_cancel_left a_lt_b

#print axioms nat.add_of_lt_cancel_right

def nat.add_lt_cancel_left {a b k: nat} : k + a < k + b -> a < b := by
  intro k_add
  induction k with
  | zero => 
    rw [zero_eq, zero_add, zero_add] at k_add
    exact k_add
  | succ k ih =>
    rw [succ_add, succ_add] at k_add
    apply ih
    exact k_add

#print axioms nat.add_lt_cancel_left

def nat.add_lt_cancel_right {a b k: nat} : a + k < b + k -> a < b := by
  rw [add_comm _ k, add_comm _ k]
  exact nat.add_lt_cancel_left

#print axioms nat.add_lt_cancel_right

def nat.add_le_left (a b: nat) : a ≤ a + b := by
  induction b with
  | zero =>
    rw [zero_eq, add_zero]
    apply le_refl
  | succ b ih =>
    apply TotalOrder.le_trans ih
    rw [add_succ]
    apply TotalOrder.le_of_lt
    apply nat.lt_succ_self

def nat.add_le_cancel_left (a b c: nat) : b ≤ c -> a + b ≤ a + c := by
  induction c generalizing a b with
  | zero =>
    intro h
    rw [le_zero h]
    apply le_refl
  | succ c ih =>
    intro h
    cases b with
    | zero =>
      rw [zero_eq, add_zero]
      apply add_le_left
    | succ b =>
    have := ih a b h
    rw [add_succ, add_succ]
    exact this

def nat.add_eq_zero { a b: nat } : a + b = 0 -> a = 0 := by
  intro add_eq_zero
  cases a with
  | zero => rfl
  | succ _ => contradiction

#print axioms nat.add_eq_zero

def nat.add_left_comm (a b c: nat) : a + (b + c) = b + (a + c) := by
  rw [←add_assoc, add_comm a b, add_assoc]

#print axioms nat.add_left_comm

def nat.add_right_comm (a b c: nat) : (a + b) + c = (a + c) + b := by
  rw [add_assoc, add_comm b c, ←add_assoc]

#print axioms nat.add_right_comm
