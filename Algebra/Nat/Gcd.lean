import Algebra.Nat.Dvd

def nat.gcd.induction.fueled
  (motive: nat -> nat -> Sort _)
  (right_zero: ∀a, motive a 0)
  (right_nz: ∀a b, 0 < b -> motive b (a % b) -> motive a b)
  (fuel: nat): ∀a b, my_option (motive a b) := fun a b =>
  match fuel with
  | .zero => .none
  | .succ fuel =>
  match b with
  | .zero => .some <| right_zero a
  | .succ b => match fueled motive right_zero right_nz fuel b.succ (a % b.succ) with
    | .none => .none
    | .some m => .some <| right_nz a b.succ nat.zero_lt_succ m

def nat.gcd.induction.fueled.termination
  (motive: nat -> nat -> Sort _)
  (right_zero: ∀a, motive a 0)
  (right_nz: ∀a b, 0 < b -> motive b (a % b) -> motive a b)
  (fuel: nat):
  ∀a b, b < fuel -> fueled motive right_zero right_nz fuel a b ≠ .none := by
  induction fuel with
  | zero =>
    intro a b enough_fuel
    have := nat.not_lt_zero enough_fuel
    contradiction
  | succ fuel ih =>
  intro a b b_lt_succ_fuel
  cases b with
  | zero =>
    intro
    contradiction
  | succ b =>
    unfold fueled
    simp only
    have := ih b.succ (a % b.succ) (by
      apply TotalOrder.lt_of_lt_and_le
      apply nat.mod.lt
      apply nat.zero_lt_succ
      exact nat.le_of_lt_succ b_lt_succ_fuel
    )
    split
    rename_i h
    have := this h
    contradiction
    intro
    contradiction

#print axioms nat.gcd.induction.fueled.termination

def nat.gcd.induction.fueled.fuel_irr
  (motive: nat -> nat -> Sort _)
  (right_zero: ∀a, motive a 0)
  (right_nz: ∀a b, 0 < b -> motive b (a % b) -> motive a b)
  (fuela fuelb: nat):
  ∀a b, b < fuela -> b < fuelb ->
  fueled motive right_zero right_nz fuela a b = fueled motive right_zero right_nz fuelb a b := by
    induction fuela generalizing fuelb with
    | zero =>
      intro a b b_lt_zero
      have := nat.not_lt_zero b_lt_zero
      contradiction
    | succ fuela ih =>
      cases fuelb with
      | zero =>
        intro a b _ b_lt_zero
        have := nat.not_lt_zero b_lt_zero
        contradiction
      | succ fuelb =>
        intro a b b_le_fuela b_le_fuelb
        cases b with
        | zero => rfl
        | succ b =>
          unfold fueled
          simp only
          rw [ih]

          apply TotalOrder.lt_of_lt_and_le
          apply nat.mod.lt
          apply nat.zero_lt_succ
          exact nat.le_of_lt_succ b_le_fuela

          apply TotalOrder.lt_of_lt_and_le
          apply nat.mod.lt
          apply nat.zero_lt_succ
          exact nat.le_of_lt_succ b_le_fuelb

#print axioms nat.gcd.induction.fueled.fuel_irr

def nat.gcd.induction
  (motive: nat -> nat -> Sort _)
  (right_zero: ∀a, motive a 0)
  (right_nz: ∀a b, 0 < b -> motive b (a % b) -> motive a b):
  ∀a b, motive a b
  := fun (a b: nat) =>
    match h:nat.gcd.induction.fueled motive right_zero right_nz b.succ a b with
    | .some m => m
    | .none => by
      apply False.elim
      apply nat.gcd.induction.fueled.termination motive right_zero right_nz b.succ a b
      apply nat.lt_succ_self
      assumption

#print axioms nat.gcd.induction

def nat.gcd.induction.remove_fuel
    (motive: nat -> nat -> Sort _)
    (right_zero: ∀a, motive a 0)
    (right_nz: ∀a b, 0 < b -> motive b (a % b) -> motive a b):
    ∀a b, ∀fuel, b < fuel -> induction.fueled motive right_zero right_nz fuel a b = .some (induction motive right_zero right_nz a b) := by
    intro a b fuel b_lt_fuel
    unfold induction
    split
    rename_i h
    rw [←h]
    apply nat.gcd.induction.fueled.fuel_irr
    assumption
    apply nat.lt_succ_self
    apply False.elim
    apply nat.gcd.induction.fueled.termination motive right_zero right_nz b.succ a b
    apply nat.lt_succ_self
    assumption

#print axioms nat.gcd.induction.remove_fuel

def nat.gcd.induction.right_zero
    (motive: nat -> nat -> Sort _)
    (right_zero: ∀a, motive a 0)
    (right_nz: ∀a b, 0 < b -> motive b (a % b) -> motive a b):
    ∀a, induction motive right_zero right_nz a 0 = right_zero a := fun _ => rfl

#print axioms nat.gcd.induction.right_zero

def nat.gcd.induction.right_nz
    (motive: nat -> nat -> Sort _)
    (right_zero: ∀a, motive a 0)
    (right_nz: ∀a b, 0 < b -> motive b (a % b) -> motive a b):
    ∀a b (b_nz: 0 < b),
    induction motive right_zero right_nz a b = right_nz a b b_nz (induction motive right_zero right_nz b (a % b)) := by
    intro a b b_nz
    conv => {
      lhs
      unfold induction
    }
    split
    {
      rename_i m h
      match b with
      | .succ b =>
      unfold induction.fueled at h
      simp only at h
      split at h
      contradiction
      have h := my_option.some.inj h
      rw [←h]
      congr
      clear h
      clear h
      rename_i h
      rw [induction.remove_fuel] at h
      rw [my_option.some.inj h]
      apply nat.mod.lt
      apply nat.zero_lt_succ
    }
    {
      apply False.elim
      apply nat.gcd.induction.fueled.termination motive right_zero right_nz b.succ a b
      apply nat.lt_succ_self
      assumption
    }

#print axioms nat.gcd.induction.right_nz

def nat.gcd (a b: nat) : nat := nat.gcd.induction (fun _ _ => nat) (fun a => a) (fun _ _ _ prev => prev) a b

def nat.gcd.right_zero { a: nat } : gcd a 0 = a := rfl
def nat.gcd.right_nz { a b: nat } : 0 < b -> gcd a b = gcd b (a % b) := by
  apply nat.gcd.induction.right_nz

def nat.gcd_ne_zero : ∀a b, gcd a b ≠ 0 -> a ≠ 0 ∨ b ≠ 0 := by
  apply nat.gcd.induction
  {
    intro a gcd_eq_zero
    apply Or.inl
    match a with
    | .succ _ => exact nat.noConfusion
  }
  {
    intro a b zero_lt_b _ gcd_ne_zero
    rw [nat.gcd.right_nz] at gcd_ne_zero
    apply Or.inr
    apply TotalOrder.ne_of_gt zero_lt_b
    assumption
  }

#print axioms nat.gcd_ne_zero

def nat.gcd.to_dvd : ∀{a b c: nat}, c ∣ gcd a b -> c ∣ a ∧ c ∣ b := by
  apply induction
  {
    intro a c c_dvd_gcd
    apply And.intro
    assumption
    apply nat.dvd.zero
  }
  {
    intro a b zero_lt_b ih c c_dvd_gcd
    rw [right_nz] at c_dvd_gcd
    have ⟨ c_dvd_b, c_dvd_rem ⟩ := ih c_dvd_gcd
    apply And.intro
    apply dvd.of_mod
    repeat assumption
  }

#print axioms nat.gcd.to_dvd

def nat.gcd.of_dvd : ∀{a b c: nat}, c ∣ a -> c ∣ b -> c ∣ gcd a b := by
  apply induction
  {
    intros
    assumption
  }
  {
    intros a b zero_lt_b ih c c_dvd_a c_dvd_b
    rw [right_nz]
    apply ih
    assumption
    apply dvd.mod <;> assumption
    assumption
  }

#print axioms nat.gcd.of_dvd

def nat.gcd.dvd (a b: nat): gcd a b ∣ a ∧ gcd a b ∣ b := nat.gcd.to_dvd (nat.dvd.refl _)

#print axioms nat.gcd.dvd

def nat.gcd.dvd_left (a b: nat): gcd a b ∣ a := (nat.gcd.dvd a b).left
def nat.gcd.dvd_right (a b: nat): gcd a b ∣ b := (nat.gcd.dvd a b).right

#print axioms nat.gcd.dvd

def nat.gcd.comm : ∀(a b: nat), gcd a b = gcd b a := by
  intro a b
  apply dvd.antisymm
  have ⟨ _, _ ⟩ := nat.gcd.dvd a b
  apply of_dvd <;> assumption
  have ⟨ _, _ ⟩ := nat.gcd.dvd b a
  apply of_dvd <;> assumption

#print axioms nat.gcd.comm

def nat.gcd.idempot_left : ∀{a b: nat}, gcd (gcd a b) b = gcd a b := by
  intro a b
  apply dvd.antisymm
  exact (nat.gcd.dvd _ _).left
  apply of_dvd
  apply dvd.refl
  exact (nat.gcd.dvd _ _).right

#print axioms nat.gcd.idempot_left

def nat.gcd.idempot_right : ∀{a b: nat}, gcd a (gcd a b) = gcd a b := by
  intro a b
  rw [comm _ (gcd _ _), comm a]
  apply idempot_left

#print axioms nat.gcd.idempot_right

def nat.gcd.assoc : ∀{a b c: nat}, gcd (gcd a b) c = gcd a (gcd b c) := by
  intro a b c
  apply dvd.antisymm
  apply of_dvd
  apply dvd.trans
  apply dvd_left
  apply dvd_left
  apply of_dvd
  apply dvd.trans
  apply dvd_left
  apply dvd_right
  apply dvd_right
  apply of_dvd
  apply of_dvd
  apply dvd_left
  apply dvd.trans
  apply dvd_right
  apply dvd_left
  apply dvd.trans
  apply dvd_right
  apply dvd_right

#print axioms nat.gcd.idempot_right

def nat.gcd.eq_zero : ∀{a b}, gcd a b = 0 -> a = 0 ∧ b = 0 := by
  intro a b  gcd_eq_zero
  have : 0 ∣ gcd a b := by
    rw [gcd_eq_zero]
    apply dvd.refl
  have ⟨ zero_dvd_a, zero_dvd_b ⟩  := nat.gcd.to_dvd this
  apply And.intro
  exact dvd.eq_zero_of_by_zero zero_dvd_a
  exact dvd.eq_zero_of_by_zero zero_dvd_b

#print axioms nat.gcd.eq_zero

def nat.gcd.common_right : ∀a b k, gcd (a * k) (b * k) = gcd a b * k := by
  apply nat.gcd.induction
  {
    intro a c
    rw [right_zero, zero_mul, right_zero]
  }
  {
    intro a b b_nz ih k
    cases k with
    | zero =>
      rw [zero_eq, mul_zero, mul_zero, mul_zero]
      rfl
    | succ c =>
    rw [right_nz, @right_nz a b]
    rw [nat.mul_mod, ih c.succ]
    assumption
    rw [mul_succ]
    apply TotalOrder.lt_of_lt_and_le
    assumption
    apply nat.add.le_left
  }

#print axioms nat.gcd.common_right

def nat.gcd.common_left : ∀a b k, gcd (k * a) (k * b) = k * gcd a b := by
  intros a b k
  rw [mul.comm k]
  rw [mul.comm k]
  rw [mul.comm k]
  apply common_right

#print axioms nat.gcd.common_left

def nat.gcd.div_common : ∀a b k, k ∣ a -> k ∣ b -> gcd (a / k) (b / k) = gcd a b / k := by
  intros a b k k_dvd_a k_dvd_b
  cases k with
  | zero =>
    rw [zero_eq, nat.div_zero, nat.div_zero, nat.div_zero]
    rfl
  | succ k =>
    have ⟨ x, xprf ⟩ := k_dvd_a
    have ⟨ y, yprf ⟩ := k_dvd_b
    cases xprf
    cases yprf
    clear k_dvd_b k_dvd_a
    rw [nat.gcd.common_left]
    repeat rw [mul_div]
    repeat apply zero_lt_succ

#print axioms nat.gcd.div_common

def nat.dvd.mul_div (a b c: nat) : c ∣ b -> a * (b / c) = (a * b) / c := by
  intro c_dvd_b
  have dvd₀ := nat.gcd.dvd_right c (a * b)
  have dvd₁ := nat.gcd.of_dvd (dvd.refl c) c_dvd_b
  have dvd₂ : gcd c b ∣ gcd c (a * b) := by
    apply nat.gcd.of_dvd
    apply nat.gcd.dvd_left
    apply nat.dvd.trans
    apply nat.gcd.dvd_right
    apply nat.dvd.mul_right

  cases c with
  | zero =>
    rw [zero_eq, nat.div_zero, nat.div_zero,  nat.mul_zero]
  | succ c =>

  have ⟨ x, xprf ⟩ := nat.dvd.trans dvd₁ (nat.dvd.trans dvd₂ dvd₀)
  have ⟨ y, yprf ⟩ := c_dvd_b
  rw [←xprf, ←yprf, nat.mul_div, nat.mul_div]
  rw [←yprf] at xprf
  clear yprf
  rw [←nat.mul.assoc, nat.mul.comm a, nat.mul.assoc] at xprf
  apply nat.eq_of_mul_eq _ xprf.symm
  repeat exact zero_lt_succ

#print axioms nat.dvd.mul_div

def nat.gcd.eq_left_of_dvd : ∀(a b: nat), a ∣ b -> gcd a b = a := by
  intro a b a_dvd_b
  apply nat.dvd.antisymm
  apply gcd.dvd_left
  apply gcd.of_dvd
  apply dvd.refl
  assumption

#print axioms nat.gcd.eq_left_of_dvd

def nat.gcd.eq_right_of_dvd : ∀(a b: nat), b ∣ a -> gcd a b = b := by
  intro a b a_dvd_b
  apply nat.dvd.antisymm
  apply gcd.dvd_right
  apply gcd.of_dvd
  assumption
  apply dvd.refl

#print axioms nat.gcd.eq_right_of_dvd

def nat.gcd.left_zero { a: nat } : gcd 0 a = a := by
  rw [gcd.comm, gcd.right_zero]

#print axioms nat.gcd.left_zero

def nat.gcd.one_right : gcd a 1 = 1 := by
  apply nat.dvd.antisymm
  apply gcd.dvd_right
  apply nat.dvd.by_one

#print axioms nat.gcd.one_right

def nat.gcd.one_left : gcd 1 a = 1 := by
  apply nat.dvd.antisymm
  apply gcd.dvd_left
  apply nat.dvd.by_one

#print axioms nat.gcd.one_left

def nat.gcd.gt_zero { a b: nat } : 0 < a ∨ 0 < b -> 0 < gcd a b := by
  intro a_nz_or_b_nz
  cases h:gcd a b
  have ⟨ _, _ ⟩  := eq_zero h
  cases a <;> cases b <;> contradiction
  apply zero_lt_succ

#print axioms nat.gcd.gt_zero
