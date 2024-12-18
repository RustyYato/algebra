import Algebra.Nat.Cmp

def nat.add (a b: nat) : nat := match a with
  | .zero => b
  | .succ a => .succ (add a b)

instance nat.instAdd : Add nat where
  add := nat.add

def nat.zero_add (b: nat) : 0 + b = b := rfl

def nat.succ_add (a b: nat) : a.succ + b = (a + b).succ := rfl

def nat.add_zero (a: nat) : a + 0 = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [succ_add]
    rw [ih]

def nat.add_succ (a b: nat) : a + b.succ = (a + b).succ := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [succ_add, succ_add]
    rw [ih]

def nat.add.comm (a b: nat) : a + b = b + a := by
  induction a with
  | zero =>
    rw [zero_eq, zero_add, add_zero]
  | succ a ih =>
    rw [succ_add, add_succ, ih]

def nat.add.assoc (a b c: nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [zero_eq, zero_add, zero_add]
  | succ a iha =>
    repeat rw [succ_add]
    rw [iha]

def nat.add.le_left (a b: nat) : a ≤ a + b := by
  induction b with
  | zero => rw [zero_eq, add_zero]
  | succ b ih =>
    rw [add_succ]
    apply le_trans
    exact ih
    apply le_of_lt
    apply lt_succ_self

def nat.add.le_right (a b: nat) : b ≤ a + b := by
  rw [comm]
  apply le_left

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

def nat.add.eq_zero_of_cancel_right (a b: nat) : a = a + b -> b = 0 := by
  intro add_eq
  rw [comm] at add_eq
  apply eq_zero_of_cancel_left
  assumption

def nat.add.le_left_iff {a b k: nat} : a ≤ b ↔ k + a ≤ k + b := by
  apply Iff.intro
  · intro h
    induction h generalizing k with
    | zero =>
      rw [nat.add_zero]
      apply nat.add.le_left
    | succ a b _ ih =>
      rw [nat.add_succ, nat.add_succ]
      apply nat.succ_le_succ
      apply ih
  · intro h
    induction k generalizing a b with
    | zero =>
      rw [nat.zero_eq, nat.zero_add, nat.zero_add] at h
      assumption
    | succ k ih =>
      apply nat.le_of_succ_le_succ
      apply ih
      rw [nat.add_succ, nat.add_succ, ←nat.succ_add, ←nat.succ_add]
      exact h

def nat.add.lt_left_iff {a b k: nat} : a < b ↔ k + a < k + b := by
  apply Iff.intro
  intro h
  have := (add.le_left_iff (k := k)).mp (succ_le_of_lt h)
  rw [nat.add_succ] at this
  apply lt_of_succ_le
  assumption
  intro h
  have := succ_le_of_lt h
  rw [←nat.add_succ] at this
  have := add.le_left_iff.mpr this
  apply lt_of_succ_le
  assumption

def nat.add.le_right_iff {a b k: nat} : a ≤ b ↔ a + k ≤ b + k := by
  rw [add.comm _ k, add.comm _ k]
  apply nat.add.le_left_iff

def nat.add.lt_right_iff {a b k: nat} : a < b ↔ a + k < b + k := by
  rw [add.comm _ k, add.comm _ k]
  apply nat.add.lt_left_iff

def nat.add_lt_of_lt_of_le (a b c d: nat) :
  a < c ->
  b ≤ d ->
  a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply nat.add.lt_right_iff.mp
  assumption
  apply nat.add.le_left_iff.mp
  assumption

def nat.add_lt_of_le_of_lt (a b c d: nat) :
  a ≤ c ->
  b < d ->
  a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply nat.add.lt_left_iff.mp
  assumption
  apply nat.add.le_right_iff.mp
  assumption

def nat.add.le {a b c d: nat} :
  a ≤ c ->
  b ≤ d ->
  a + b ≤ c + d := by
  intro ac bd
  apply le_trans
  apply nat.add.le_left_iff.mp
  assumption
  apply nat.add.le_right_iff.mp
  assumption

def nat.add.lt {a b c d: nat} :
  a < c ->
  b < d ->
  a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply nat.add.lt_left_iff.mp
  assumption
  apply nat.add.lt_right_iff.mp
  assumption

def nat.add.lt_right_nz (a b: nat) : 0 < b -> a < a + b := by
  intro h
  suffices a + 0 < a + b from by
    rw [add_zero] at this
    exact this
  apply add.lt_left_iff.mp
  assumption

def nat.add.lt_left_nz (a b: nat) : 0 < a -> b < a + b := by
  rw [comm]
  apply lt_right_nz

def nat.add_eq_add (a b c d: nat) : a = c -> b = d -> a + b = c + d := by
  intro a_eq_c b_eq_d
  rw [a_eq_c, b_eq_d]

def nat.add_eq_add_left (a b c: nat) : a = c -> a + b = c + b := by
  intro a_eq_c
  rw [a_eq_c]

def nat.add_eq_add_right (a b d: nat) : b = d -> a + b = a + d := by
  intro b_eq_d
  rw [b_eq_d]

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

def nat.add.cancel_right {a b k: nat} : a + k = b + k -> a = b := by
  rw [comm _ k, comm _ k]
  exact cancel_left

def nat.add.of_lt_cancel_left {a b k: nat} : a < b -> k + a < k + b := by
  intro k_add
  induction k with
  | zero => exact k_add
  | succ k ih =>
    apply nat.succ_lt_succ
    exact ih

def nat.add.of_lt_cancel_right {a b k: nat} : a < b -> a + k < b + k := by
  intro a_lt_b
  rw [comm _ k, comm _ k]
  exact nat.add.of_lt_cancel_left a_lt_b

def nat.add.lt_cancel_left {a b k: nat} : k + a < k + b -> a < b := nat.add.lt_left_iff.mpr

def nat.add.lt_cancel_right {a b k: nat} : a + k < b + k -> a < b := nat.add.lt_right_iff.mpr

def nat.add.of_le_cancel_left (a b c: nat) : b ≤ c -> a + b ≤ a + c := nat.add.le_left_iff.mp

def nat.add.of_le_cancel_right (a b c: nat) : b ≤ c -> b + a ≤ c + a := nat.add.le_right_iff.mp

def nat.add.eq_zero { a b: nat } : a + b = 0 -> a = 0 := by
  intro add_eq_zero
  cases a with
  | zero => rfl
  | succ _ => contradiction

def nat.add.comm_left (a b c: nat) : a + (b + c) = b + (a + c) := by
  rw [←assoc, comm a b, assoc]

def nat.add.comm_right (a b c: nat) : (a + b) + c = (a + c) + b := by
  rw [assoc, comm b c, ←assoc]

def nat.one_add (a: nat) : 1 + a = a.succ := rfl

def nat.add_one (a: nat) : a + 1 = a.succ := by
  rw [add.comm, one_add]
