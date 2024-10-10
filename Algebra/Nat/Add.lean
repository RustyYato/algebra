import Algebra.Nat.Cmp

def nat.add (a b: nat) : nat := match a with
  | .zero => b
  | .succ a => .succ (add a b)

instance nat.instAdd : Add nat where
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

def nat.add.comm (a b: nat) : a + b = b + a := by
  induction a with
  | zero =>
    rw [zero_eq, zero_add, add_zero]
  | succ a ih =>
    rw [succ_add, add_succ, ih]

#print axioms nat.add.comm

def nat.add.assoc (a b c: nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [zero_eq, zero_add, zero_add]
  | succ a iha =>
    repeat rw [succ_add]
    rw [iha]

#print axioms nat.add.assoc

def nat.add.le_left (a b: nat) : a ≤ a + b := by
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

#print axioms nat.add.le_left

def nat.add.le_right (a b: nat) : b ≤ a + b := by
  rw [comm]
  apply le_left

#print axioms nat.add.le_right

def nat.add.eq_zero_of_cancel_left (a b: nat) : b = a + b -> a = 0 := by
  intro add_eq
  induction b with
  | zero =>
    rw [zero_eq, add_zero] at add_eq
    exact add_eq.symm
  | succ b ih =>
    apply ih
    rw [add_succ] at add_eq
    exact nat.succ.inj add_eq

#print axioms nat.add.eq_zero_of_cancel_left

def nat.add.eq_zero_of_cancel_right (a b: nat) : a = a + b -> b = 0 := by
  intro add_eq
  rw [comm] at add_eq
  apply eq_zero_of_cancel_left
  assumption

#print axioms nat.add.eq_zero_of_cancel_right

def nat.add.compare_left (a b k: nat) : compare (k + a) (k + b) = compare a b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [succ_add, succ_add, compare.succ, ih]

#print axioms nat.add.compare_left

def nat.add.compare_right (a b k: nat) : compare (a + k) (b + k) = compare a b := by
  rw [comm _ k, comm _ k, compare_left]

#print axioms nat.add.compare_right

def nat.add.lt_right_nz (a b: nat) : 0 < b -> a < a + b := by
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

#print axioms nat.add.lt_right_nz

def nat.add.lt_left_nz (a b: nat) : 0 < a -> b < a + b := by
  rw [comm]
  apply lt_right_nz

#print axioms nat.add.lt_left_nz

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

def nat.add.cancel_left {a b k: nat} : k + a = k + b -> a = b := by
  intro k_add
  induction k with
  | zero =>
    rw [zero_eq, zero_add, zero_add] at k_add
    exact k_add
  | succ k ih =>
    rw [succ_add, succ_add] at k_add
    apply ih
    exact nat.succ.inj k_add

#print axioms nat.add.cancel_left

def nat.add.cancel_right {a b k: nat} : a + k = b + k -> a = b := by
  rw [comm _ k, comm _ k]
  exact cancel_left

#print axioms nat.add.cancel_right

def nat.add.of_lt_cancel_left {a b k: nat} : a < b -> k + a < k + b := by
  intro k_add
  induction k with
  | zero => exact k_add
  | succ k ih =>
    apply nat.succ_lt_succ
    exact ih

#print axioms nat.add.of_lt_cancel_left

def nat.add.of_lt_cancel_right {a b k: nat} : a < b -> a + k < b + k := by
  intro a_lt_b
  rw [comm _ k, comm _ k]
  exact nat.add.of_lt_cancel_left a_lt_b

#print axioms nat.add.of_lt_cancel_right

def nat.add.lt_cancel_left {a b k: nat} : k + a < k + b -> a < b := by
  intro k_add
  induction k with
  | zero =>
    rw [zero_eq, zero_add, zero_add] at k_add
    exact k_add
  | succ k ih =>
    rw [succ_add, succ_add] at k_add
    apply ih
    exact k_add

#print axioms nat.add.lt_cancel_left

def nat.add.lt_cancel_right {a b k: nat} : a + k < b + k -> a < b := by
  rw [comm _ k, comm _ k]
  exact lt_cancel_left

#print axioms nat.add.lt_cancel_right

def nat.add.of_le_cancel_left (a b c: nat) : b ≤ c -> a + b ≤ a + c := by
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
      apply le_left
    | succ b =>
    have := ih a b h
    rw [add_succ, add_succ]
    exact this

#print axioms nat.add.of_le_cancel_left

def nat.add.of_le_cancel_right (a b c: nat) : b ≤ c -> b + a ≤ c + a:= by
  intros
  repeat rw [comm _ a]
  apply nat.add.of_le_cancel_left <;> assumption

#print axioms nat.add.of_le_cancel_right

def nat.add.eq_zero { a b: nat } : a + b = 0 -> a = 0 := by
  intro add_eq_zero
  cases a with
  | zero => rfl
  | succ _ => contradiction

#print axioms nat.add.eq_zero

def nat.add.comm_left (a b c: nat) : a + (b + c) = b + (a + c) := by
  rw [←assoc, comm a b, assoc]

#print axioms nat.add.comm_left

def nat.add.comm_right (a b c: nat) : (a + b) + c = (a + c) + b := by
  rw [assoc, comm b c, ←assoc]

#print axioms nat.add.comm_right

def nat.one_add (a: nat) : 1 + a = a.succ := rfl

#print axioms nat.one_add

def nat.add_one (a: nat) : a + 1 = a.succ := by
  rw [add.comm, one_add]

#print axioms nat.add_one

def nat.add.le (a b c d: nat) : a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro a_le_c b_le_d
  apply le_trans (of_le_cancel_right b a c a_le_c) (of_le_cancel_left c b d b_le_d)

#print axioms nat.add.le

def nat.add.lt (a b c d: nat) : a < c -> b < d -> a + b < c + d := by
  intro a_le_c b_le_d
  apply lt_trans (of_lt_cancel_right a_le_c) (of_lt_cancel_left b_le_d)

#print axioms nat.add.lt
