import Algebra.Nat.Sub

def nat.mul (a b: nat) : nat := match a with
  | .zero => .zero
  | .succ a => b + nat.mul a b

instance nat.mul_inst : Mul nat where
  mul := nat.mul

def nat.zero_mul (b: nat) : 0 * b = 0 := rfl

def nat.succ_mul (a b: nat) : a.succ * b = b + a * b := rfl

def nat.mul_zero (a: nat) : a * 0 = 0 := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [succ_mul, ih]
    rfl

def nat.mul_succ (a b: nat) : a * b.succ = a + (a * b) := by
  induction a generalizing b with
  | zero => rfl
  | succ a ih => rw [succ_mul, ih, succ_mul, succ_add, succ_add, add.comm_left]

def nat.one_mul (a: nat) : 1 * a = a := by
  rw [←one_eq, succ_mul, zero_eq, zero_mul, add_zero]

def nat.mul_one (a: nat) : a * 1 = a := by
  rw [←one_eq, mul_succ, zero_eq, mul_zero, add_zero]

def nat.mul.comm (a b: nat) : a * b = b * a := by
  induction a generalizing b with
  | zero => rw [zero_eq, zero_mul, mul_zero]
  | succ a ih => rw [succ_mul, mul_succ, ih]

def nat.add_mul (a b k: nat) : (a + b) * k = a * k + b * k := by
  induction k with
  | zero => rw [zero_eq, mul_zero, mul_zero, mul_zero, add_zero]
  | succ k ih =>
    rw [mul_succ, mul_succ, mul_succ, ih]
    rw [add.assoc, add.assoc]
    apply nat.add_eq_add_right
    rw [add.comm_left]

def nat.mul_add (a b k: nat) : k * (a + b) = k * a + k * b := by
  repeat rw [mul.comm k]
  apply add_mul

def nat.mul.eq_zero {a b: nat} : a * b = 0 -> a = 0 ∨ b = 0 := by
  intro mul_eq_zero
  cases a
  exact Or.inl rfl
  cases b
  exact Or.inr rfl
  rw [succ_mul, succ_add] at mul_eq_zero
  contradiction

def nat.mul.assoc (a b c: nat) : (a * b) * c = a * (b * c) := by
  induction a generalizing b c with
  | zero => rw [zero_eq, zero_mul, zero_mul, zero_mul]
  | succ a ih =>
    rw [succ_mul, succ_mul, add_mul]
    apply nat.add_eq_add_right
    apply ih

def nat.mul.comm_left (a b c: nat) : a * (b * c) = b * (a * c) := by
  rw [←mul.assoc, mul.comm a, mul.assoc]
def nat.mul.comm_right (a b c: nat) : a * (b * c) = c * (b * a) := by
  rw [mul.comm b, mul.comm_left, mul.comm b]

def nat.mul.ge (a b: nat) (b_nz: 0 < b) : a ≤ a * b := by
  match b with
  | .zero => contradiction
  | .succ b =>
    rw [mul_succ]
    apply add.le_left

def nat.mul.gt (a b: nat) (a_nz: 0 < a) (b_nz: 1 < b) : a < a * b := by
  match b with
  | .zero | .succ .zero => contradiction
  | .succ (.succ b) =>
    rw [mul_succ, mul_succ]
    match a with
    | .succ a =>
    rw [nat.succ_add, add.comm_left, succ_add]
    apply succ_lt_succ
    apply lt_of_le_of_lt _ lt_succ_self
    apply add.le_left

def nat.mul.cancel_left (a b c: nat) (a_nz: 0 < a) : a * b = a * c -> b = c := by
  induction c generalizing a b with
  | zero =>
    intro h
    rw [zero_eq, mul_zero] at h
    cases nat.mul.eq_zero h
    rename_i h
    cases h
    contradiction
    assumption
  | succ c ih =>
    intro h
    rw [mul_succ] at h
    cases b with
    | zero =>
      rw [zero_eq, mul_zero] at h
      cases add.eq_zero h.symm
      contradiction
    | succ b =>
      rw [mul_succ] at h
      congr
      apply ih
      assumption
      apply add.cancel_left h

def nat.mul.cancel_right (a b c: nat) (a_nz: 0 < a) : b * a = c * a -> b = c := by
  repeat rw [comm _ a]
  apply cancel_left <;> assumption

def nat.mul.of_lt_cancel_left (a b c: nat) (a_nz: 0 < a) : b < c -> a * b < a * c := by
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
    apply add.of_lt_cancel_left
    apply ih
    apply zero_lt_succ
    exact nat.lt_of_succ_lt_succ h

def nat.mul.of_lt_cancel_right (a b c: nat) (a_nz: 0 < a) : b < c -> b * a < c * a := by
  intros
  repeat rw [comm _ a]
  apply of_lt_cancel_left <;> assumption

def nat.mul.lt_cancel_left (a b c: nat) (a_nz: 0 < a) : a * b < a * c -> b < c := by
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
    | zero => exact nat.zero_lt_succ
    | succ b =>
      rw [mul_succ] at h
      apply nat.succ_lt_succ <| ih a b a_nz _
      apply add.lt_cancel_left
      exact h

def nat.mul.lt_cancel_right (a b c: nat) (a_nz: 0 < a): b * a < c * a -> b < c := by
  repeat rw [comm _ a]
  apply lt_cancel_left <;> assumption

def nat.mul.of_le_cancel_left (a b c: nat) : b ≤ c -> a * b ≤ a * c := by
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
    have := ih a b (nat.le_of_succ_le_succ h)
    rw [mul_succ, mul_succ]
    apply add.of_le_cancel_left
    assumption

def nat.mul.of_le_cancel_right (a b c: nat) : b ≤ c -> b * a ≤ c * a := by
  repeat rw [comm _ a]
  apply of_le_cancel_left

def nat.mul_sub (a b c: nat) : a * (b - c) = a * b - a * c := by
  induction b generalizing a c with
  | zero => rw [zero_eq, zero_sub, mul_zero, zero_sub]
  | succ b ih =>
    cases c with
    | zero => rw [zero_eq, sub_zero, mul_zero, sub_zero]
    | succ c =>
      rw [succ_sub_succ, mul_succ, mul_succ, sub_add, add.comm, ←add_sub, sub.refl, add_zero]
      apply ih
      apply le_refl

def nat.sub_mul (a b c: nat): (b - c) * a = b * a - c * a := by
  repeat rw [mul.comm _ a]
  apply nat.mul_sub

def nat.mul.eq_one {a b: nat} : a * b = 1 -> a = 1 ∧ b = 1 := by
  intro mul_eq_one
  match a with
  | 0 => rw [zero_mul] at mul_eq_one; contradiction
  | .succ (.succ a) =>
    have : ∀(a b: nat), a.succ.succ * b = 0 ∨ a.succ.succ * b > 1 := by
      clear mul_eq_one a b
      clear a
      intro a b
      induction b with
      | zero =>
        rw [zero_eq, mul_zero]
        exact Or.inl rfl
      | succ b ih =>
        cases ih with
        | inl ih =>
          rw [mul_succ, ih]
          apply Or.inr
          rw [add_zero]
          apply nat.succ_lt_succ nat.zero_lt_succ
        | inr ih =>
          apply Or.inr
          rw [mul_succ]
          apply lt_of_lt_of_le
          assumption
          apply nat.add.le_right
    have := this a b
    rw [mul_eq_one] at this
    cases this <;> contradiction
  | 1 =>
    apply And.intro rfl
    rw [one_mul] at mul_eq_one
    assumption

def nat.eq_of_mul_eq { a b k: nat } : 0 < k -> k * a = k * b -> a = b := by
  intro k_nz k_mul
  induction a generalizing b k with
  | zero =>
    rw [zero_eq, mul_zero] at k_mul
    cases mul.eq_zero k_mul.symm with
    | inl h =>
      rw [h] at k_nz
      contradiction
    | inr h => exact h.symm
  | succ a ih =>
    cases b with
    | zero =>
      rw [zero_eq, mul_zero] at k_mul
      cases mul.eq_zero k_mul with
      | inl h =>
        rw [h] at k_nz
        contradiction
      | inr h => contradiction
    | succ b =>
      congr
      apply ih
      assumption
      rw [mul_succ, mul_succ] at k_mul
      apply nat.add.cancel_left
      assumption

def nat.mul.le (a b c d: nat) : a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro a_le_c b_le_d
  apply le_trans
  exact (nat.mul.of_le_cancel_left _ _ _ b_le_d)
  exact (nat.mul.of_le_cancel_right _ _ _ a_le_c)

def nat.mul.lt (a b c d: nat) : a < c -> b < d -> a * b < c * d := by
  intro a_lt_c b_lt_d
  match c with
  | .zero =>
    have := not_lt_zero a_lt_c
    contradiction
  | .succ c =>
  match b with
  | .zero =>
    rw [nat.zero_eq, mul_zero]
    match d with
    | 0 =>
      have := not_lt_zero b_lt_d
      contradiction
    | .succ d => exact nat.zero_lt_succ
  | .succ b =>
  apply lt_trans
  apply of_lt_cancel_right
  exact nat.zero_lt_succ
  assumption
  apply of_lt_cancel_left
  exact nat.zero_lt_succ
  assumption

-- def nat.mul.compare_left_pos (a b k: nat) : 0 < k -> compare (a * k) (b * k) = compare a b := by
--   intro h
--   induction k with
--   | zero => contradiction
--   | succ k ih =>
--     cases k
--     rw [nat.one_eq, mul_one, mul_one]
--     rename_i k
--     rw [mul_succ a, mul_succ b]
--     apply add.compare_both
--     rfl
--     apply ih
--     trivial
