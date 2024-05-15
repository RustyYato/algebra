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
      apply nat.mod_lt
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
          apply nat.mod_lt
          apply nat.zero_lt_succ
          exact nat.le_of_lt_succ b_le_fuela
          
          apply TotalOrder.lt_of_lt_and_le
          apply nat.mod_lt
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
      apply nat.mod_lt
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
    apply nat.dvd_zero
  }
  {
    intro a b zero_lt_b ih c c_dvd_gcd
    rw [right_nz] at c_dvd_gcd
    have ⟨ c_dvd_b, c_dvd_rem ⟩ := ih c_dvd_gcd
    apply And.intro
    apply of_dvd_mod 
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
    apply dvd_mod <;> assumption
    assumption
  }

#print axioms nat.gcd.of_dvd

def nat.gcd.dvd (a b: nat): gcd a b ∣ a ∧ gcd a b ∣ b := nat.gcd.to_dvd (nat.dvd_refl _)

#print axioms nat.gcd.dvd

def nat.gcd.dvd_left (a b: nat): gcd a b ∣ a := (nat.gcd.dvd a b).left
def nat.gcd.dvd_right (a b: nat): gcd a b ∣ b := (nat.gcd.dvd a b).right

#print axioms nat.gcd.dvd

def nat.gcd.comm : ∀(a b: nat), gcd a b = gcd b a := by
  intro a b
  apply dvd_antisymm
  have ⟨ _, _ ⟩ := nat.gcd.dvd a b
  apply of_dvd <;> assumption
  have ⟨ _, _ ⟩ := nat.gcd.dvd b a
  apply of_dvd <;> assumption

#print axioms nat.gcd.comm

def nat.gcd.idempot_left : ∀{a b: nat}, gcd (gcd a b) b = gcd a b := by
  intro a b
  apply dvd_antisymm
  exact (nat.gcd.dvd _ _).left
  apply of_dvd
  apply dvd_refl
  exact (nat.gcd.dvd _ _).right

#print axioms nat.gcd.idempot_left

def nat.gcd.idempot_right : ∀{a b: nat}, gcd a (gcd a b) = gcd a b := by
  intro a b
  rw [comm _ (gcd _ _), comm a]
  apply idempot_left

#print axioms nat.gcd.idempot_right

def nat.gcd.assoc : ∀{a b c: nat}, gcd (gcd a b) c = gcd a (gcd b c) := by
  intro a b c
  apply dvd_antisymm
  apply of_dvd
  apply nat.dvd.trans
  apply nat.gcd.dvd_left
  apply nat.gcd.dvd_left
  apply of_dvd
  apply nat.dvd.trans
  apply nat.gcd.dvd_left
  apply nat.gcd.dvd_right
  apply nat.gcd.dvd_right
  apply of_dvd
  apply of_dvd
  apply nat.gcd.dvd_left
  apply nat.dvd.trans
  apply nat.gcd.dvd_right
  apply nat.gcd.dvd_left
  apply nat.dvd.trans
  apply nat.gcd.dvd_right
  apply nat.gcd.dvd_right

#print axioms nat.gcd.idempot_right

def nat.gcd_eq_zero : ∀{a b}, gcd a b = 0 -> a = 0 ∧ b = 0 := by
  intro a b  gcd_eq_zero
  have : 0 ∣ gcd a b := by
    rw [gcd_eq_zero]
    apply nat.dvd_refl
  have ⟨ zero_dvd_a, zero_dvd_b ⟩  := nat.gcd.to_dvd this
  apply And.intro
  exact nat.eq_zero_of_zero_dvd zero_dvd_a
  exact nat.eq_zero_of_zero_dvd zero_dvd_b

#print axioms nat.gcd_eq_zero

