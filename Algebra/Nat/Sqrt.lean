import Algebra.Nat.Dvd

def nat.square : nat -> nat := fun x => x * x
postfix:max "²" => nat.square

def nat.sqrt : nat -> nat :=
  nat.induction (fun _ => nat) <| fun n ih =>
    if h:n ≤ 1 then n else
    let small := 2 * ih (n / 4) (by
      refine div.lt n 4 rfl ?_
      match n with
      | nat.succ n => trivial)
    let large := small.succ
    if n < large² then small else large

def nat.sqrt.zero : nat.sqrt 0 = 0 := by rfl
def nat.sqrt.one : nat.sqrt 1 = 1 := by rfl
def nat.sqrt.le_one : ∀x ≤ 1, nat.sqrt x = x := by
  intro x h
  match x with
  | nat.zero => rfl
  | nat.succ nat.zero => rfl

def nat.sqrt.gt_one : ∀x > 1,
  nat.sqrt x =
  if x < (2 * nat.sqrt (x / 4)).succ² then 2 * nat.sqrt (x / 4) else
  (2 * nat.sqrt (x / 4)).succ := by
  intro x h
  conv => { lhs; rw [sqrt] }
  unfold induction
  rw [dif_neg]
  dsimp
  rw [←sqrt]
  apply nat.not_lt_of_ge
  assumption

def nat.sqrt.sq_le_self (n: nat): n.sqrt² ≤ n := by
  revert n
  apply nat.induction
  intro n ih
  cases lt_or_ge 1 n
  · rw [nat.sqrt.gt_one]
    any_goals assumption
    rename_i one_lt_n
    split <;> rename_i h
    unfold square
    have : 2 * 2 = (4: nat) := rfl
    rw [mul.assoc, ←mul.assoc _ 2, mul.comm _ 2, ←mul.assoc 2, ←mul.assoc 2, mul.assoc, this]
    apply le_trans
    apply mul.le
    apply le_refl
    apply ih
    apply div.lt
    trivial
    · match n with
      | nat.succ n => trivial
    apply nat.div.mul_le
    replace h := TotalOrder.le_of_not_lt h
    exact h
  · match n with
    | 0 =>
      rw [nat.sqrt.zero]
      apply nat.le_refl
    | 1 =>
      rw [nat.sqrt.one]
      apply nat.le_refl

def nat.mul_two (n: nat) : n + n = 2 * n := by
  have : (2: nat) = 1 + 1 := rfl
  rw [this, add_mul, one_mul]

def nat.dvd.cancel_left (a b: nat) : a ∣ b -> a * (b / a) = b := by
  intro a_dvd_b
  cases a with
  | zero =>
    rw [nat.zero_eq] at *
    rw [zero_mul]
    have ⟨ x, prf ⟩ := a_dvd_b
    rw [zero_mul] at prf
    assumption
  | succ a =>
  have := nat.div_def b a.succ nat.zero_lt_succ
  rw [nat.dvd.mod_eq_zero a_dvd_b, nat.add_zero, mul.comm] at this
  rw [←this]

def nat.div.add_left (a b k: nat) (h: 0 < k) : (a * k + b) / k = a + b / k := by
  induction a with
  | zero => rw [zero_eq, zero_mul, zero_add, zero_add]
  | succ a ih =>
    rw [div.if_ge, succ_add]
    congr
    rw [succ_mul, add.assoc, add.comm k, add_sub_inv, ih]
    assumption
    rw [succ_mul, add.assoc]
    apply add.le_left

def nat.div.mul (a b c d: nat) : (a / b) * (c / d) ≤ (a * c) / (b * d) := by
  cases b with
  | zero =>
    rw [zero_eq, div_zero, zero_mul]
    apply zero_le
  | succ b =>
  cases d with
  | zero =>
    rw [zero_eq, div_zero, mul_zero]
    apply zero_le
  | succ d =>
  have ab := nat.div_def a b.succ nat.zero_lt_succ
  have cd := nat.div_def c d.succ nat.zero_lt_succ

  -- (a₀ * b * c₀ * d + a₀ * b * c₁ + a₁ * c₀ * d + a₁ * c₁) / (b * d)
  -- (a₀ * c₀ * b * d + a₀ * b * c₁ + a₁ * c₀ * d + a₁ * c₁) / (b * d)
  -- a₀ * c₀ + (a₀ * b * c₁ + a₁ * c₀ * d + a₁ * c₁) / (b * d)

  conv => {
    rhs
    rw [ab, cd]
  }
  rw [mul_add, add_mul, add_mul]
  conv => {
    rhs
    lhs
    lhs
    lhs
    rw [mul.assoc, ←mul.assoc b.succ, mul.comm b.succ, mul.assoc, ←mul.assoc]
  }
  rw [add.assoc]
  rw [nat.div.add_left]
  apply add.le_left
  trivial

def nat.sqrt.spec (n x: nat): x * x ≤ n -> x ≤ n.sqrt := by
  intro xsq_le_n
  induction n using nat.induction generalizing x with
  | ih n ih =>
  replace ih := fun m => ih m
  cases lt_or_ge 1 n
  · rename_i one_lt_n
    unfold sqrt induction
    rw [←sqrt, dif_neg]
    dsimp
    split
    · rename_i h
      apply Decidable.byContradiction
      intro g
      replace g := TotalOrder.lt_of_not_ge g
      replace g := nat.succ_le_of_lt g
      have := le_trans (mul.le _ _ _ _ g g) xsq_le_n
      have := lt_of_lt_of_le h this
      have := lt_irrefl _ this
      contradiction
    · rename_i h
      have := ih (n / 4) (by
        apply div.lt
        trivial
        match n with
        | nat.succ n => trivial
        ) (x / 2) (by
        apply le_trans
        apply nat.div.mul
        apply div.le_div_if_mul_le
        trivial
        have : (2: nat) * 2 = 4 := rfl
        rw [this]
        rw [mul.comm]
        apply le_trans
        apply add.le_left _ (x * x % 4)
        rw [←div_def]
        assumption
        trivial
        )
      have := add.le _ _ _ _ this this
      rw [mul_two, mul_two] at this
      match mod_def:x%2 with
      | 0 =>
        have two_div_x := nat.dvd.of_mod_eq_zero (by trivial) mod_def
        rw [dvd.cancel_left _ _ two_div_x] at this
        apply le_trans this
        apply le_of_lt
        apply lt_succ_self
      | 1 =>
        rw [nat.one_eq] at *
        rw [nat.div_def x 2, mod_def]
        rw [add_one]
        apply succ_le_succ
        rw [mul.comm]
        assumption
        trivial
      | nat.succ (nat.succ z) =>
        have := nat.mod.lt x 2 (by trivial)
        rw [mod_def] at this
        have := not_lt_zero <| lt_of_succ_lt_succ (lt_of_succ_lt_succ this)
        contradiction
    apply TotalOrder.not_le_of_lt
    assumption
  · rename_i h
    unfold sqrt induction
    rw [←sqrt, dif_pos]
    · match n with
      | 0 =>
        match x with
        | 0 => rfl
      | 1 =>
        match x with
        | 0 | 1 => trivial
    · assumption
