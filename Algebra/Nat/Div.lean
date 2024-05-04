import Algebra.Nat.Mul
import Algebra.Nat.Sub
import Algebra.Nat.WellFounded

inductive my_option (t: Sort α) where
  | none
  | some (value: t)

def my_option.is_some (o: my_option α) : Prop := match o with
  | .none => False
  | .some _ => True

def nat.div_mod_induction.fueled
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b )
  (fuel: nat):
  ∀a b, 0 < b -> my_option (motive a b) := fun a b b_nz =>
    match fuel with
    | .zero => .none
    | .succ fuel =>
    match lt_or_ge_dec a b with
    | .Lt a_lt_b => .some <| is_lt a b a_lt_b
    | .Ge a_ge_b => match nat.div_mod_induction.fueled motive is_lt is_ge fuel (a - b) b b_nz with
      | .none => .none
      | .some prev => .some <| is_ge a b a_ge_b prev

def nat.div_mod_induction.fueled.termination
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b )
  (fuel: nat):
  ∀a b b_nz,
    a < fuel ->
    (nat.div_mod_induction.fueled motive is_lt is_ge fuel a b b_nz).is_some := by
    intro a b b_nz a_lt_fuel
    induction fuel generalizing a with
    | zero =>
      have := nat.not_lt_zero a_lt_fuel
      contradiction
    | succ fuel ih =>
      unfold fueled
      split
      rename_i a_lt_b _
      trivial
      rename_i a_ge_b _
      have ih := ih (a - b) <| 
        lt_of_lt_and_le
        (sub_nz_lt a b b_nz a_ge_b)
        (le_of_lt_succ a_lt_fuel)
      split
      rename_i h
      rw [h] at ih
      contradiction
      trivial

#print axioms nat.div_mod_induction.fueled.termination

def nat.div_mod_induction.fueled.fuel_irr
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b )
  (fuel_a fuel_b: nat):
  ∀a b b_nz,
    a < fuel_a -> a < fuel_b ->
    nat.div_mod_induction.fueled motive is_lt is_ge fuel_a a b b_nz =
    nat.div_mod_induction.fueled motive is_lt is_ge fuel_b a b b_nz
    := by
    intro a b b_nz a_lt_fuel_a a_lt_fuel_b
    induction fuel_a generalizing a fuel_b with
    | zero => 
      have := nat.not_lt_zero a_lt_fuel_a
      contradiction
    | succ fuel_a iha =>  
    cases fuel_b with
    | zero => 
      have := nat.not_lt_zero a_lt_fuel_b
      contradiction
    | succ fuel_b =>
      unfold fueled
      cases lt_or_ge_dec a b with
      | Lt a_lt_b => trivial
      | Ge a_ge_b =>
        simp only
        rw [iha]
        exact lt_of_lt_and_le (sub_nz_lt a b b_nz a_ge_b) (le_of_lt_succ a_lt_fuel_a)
        exact lt_of_lt_and_le (sub_nz_lt a b b_nz a_ge_b) (le_of_lt_succ a_lt_fuel_b)

#print axioms nat.div_mod_induction.fueled.fuel_irr

def nat.div_mod_induction
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b ):
  ∀a b, 0 < b -> motive a b := fun a b b_nz => match h:nat.div_mod_induction.fueled motive is_lt is_ge a.succ a b b_nz with
    | .some m => m
    | .none => by
      have := nat.div_mod_induction.fueled.termination motive is_lt is_ge a.succ a b b_nz (lt_succ_self _)
      rw [h] at this
      contradiction

#print axioms nat.div_mod_induction

def nat.div_mod_induction.remove_fuel
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b ):
  ∀a b b_nz fuel,
  a < fuel ->
  nat.div_mod_induction.fueled motive is_lt is_ge fuel a b b_nz =
  (.some (nat.div_mod_induction motive is_lt is_ge a b b_nz)) := by
  intro a b b_nz fuel a_lt_fuel
  unfold div_mod_induction
  split
  {
    rename_i h
    rw [←h]
    rw [nat.div_mod_induction.fueled.fuel_irr]
    assumption
    apply lt_succ_self
  }
  {
    have := fueled.termination motive is_lt is_ge a.succ a b b_nz (lt_succ_self _)
    rename_i h
    rw [h] at this
    contradiction
  }

def nat.div_mod_induction.is_lt
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b ):
  ∀a b b_nz a_lt_b, 
  nat.div_mod_induction motive is_lt is_ge a b b_nz = is_lt a b a_lt_b := by
  intro a b b_nz a_lt_b
  unfold div_mod_induction
  split
  {
    rename_i m h
    unfold fueled at h
    have pick_lt := nat.lt_or_ge_dec.pick_lt a_lt_b
    rw [pick_lt] at h
    simp only at h
    exact my_option.some.inj h.symm
  }
  {
    have := fueled.termination motive is_lt is_ge a.succ a b b_nz (lt_succ_self _)
    rename_i h
    rw [h] at this
    contradiction
  }

#print axioms nat.div_mod_induction.is_lt

def nat.div_mod_induction.is_ge
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b ):
  ∀a b b_nz a_ge_b, 
  nat.div_mod_induction motive is_lt is_ge a b b_nz = is_ge a b a_ge_b (nat.div_mod_induction motive is_lt is_ge (a - b) b b_nz) := by
  intro a b b_nz a_ge_b
  conv => {
    lhs
    unfold div_mod_induction
  }
  split
  {
    rename_i m h
    unfold fueled at h
    have pick_ge := nat.lt_or_ge_dec.pick_ge a_ge_b
    rw [pick_ge] at h
    simp only at h
    rw [nat.div_mod_induction.remove_fuel] at h
    simp only at h
    exact my_option.some.inj h.symm
    apply sub_nz_lt
    repeat assumption
  }
  {
    have := fueled.termination motive is_lt is_ge a.succ a b b_nz (lt_succ_self _)
    rename_i h
    rw [h] at this
    contradiction
  }

#print axioms nat.div_mod_induction.is_ge

def nat.div : ∀(_ b: nat), 0 < b -> nat := nat.div_mod_induction
    (fun _ _ => nat)
    (fun _ _ _ => nat.zero)
    (fun _ _ _ prev => prev.succ)

#print axioms nat.div

def nat.mod : ∀(_ b: nat), 0 < b -> nat :=  nat.div_mod_induction
    (fun _ _ => nat)
    (fun a _ _ => a)
    (fun _ _ _ prev => prev)

#print axioms nat.mod

def nat.div.def { a b: nat } { b_nz: 0 < b } : (a.div b b_nz) = (nat.div_mod_induction
    (fun _ _ => nat)
    (fun _ _ _ => nat.zero)
    (fun _ _ _ prev => prev.succ) a b b_nz) := rfl

def nat.mod.def { a b: nat } { b_nz: 0 < b } : (a.mod b b_nz) = (nat.div_mod_induction
    (fun _ _ => nat)
    (fun a _ _ => a)
    (fun _ _ _ prev => prev) a b b_nz) := rfl

instance nat.div_inst : Div nat where
  div a b := match b with
     | .zero => .zero
     | .succ b => a.div b.succ rfl

instance nat.mod_inst : Mod nat where
  mod a b := match b with
     | .zero => .zero
     | .succ b => a.mod b.succ rfl

def nat.div_eq' : ∀{ a b: nat }, a / b = (match b with
     | .zero => .zero
     | .succ b => a.div b.succ rfl) := rfl

def nat.mod_eq' : ∀{ a b: nat }, a % b = (match b with
     | .zero => .zero
     | .succ b => a.mod b.succ rfl) := rfl

def nat.div_eq : ∀{ a b: nat } (b_nz: 0 < b), a / b = a.div b b_nz := by
  intro a b b_nz
  rw [nat.div_eq']
  cases b with
  | zero => contradiction
  | succ b => rfl

#print axioms nat.div_eq

def nat.mod_eq : ∀{ a b: nat } (b_nz: 0 < b), a % b = a.mod b b_nz := by
  intro a b b_nz
  rw [nat.mod_eq']
  cases b with
  | zero => contradiction
  | succ b => rfl

#print axioms nat.mod_eq

def nat.div.is_lt : ∀{ a b: nat } (b_nz: 0 < b), a < b -> a.div b b_nz = 0 := by
  intro a b b_nz a_lt_b
  unfold div
  rw [div_mod_induction.is_lt]
  rfl
  assumption

#print axioms nat.div.is_lt

def nat.div.is_ge : ∀{ a b: nat } (b_nz: 0 < b), a ≥ b -> a.div b b_nz = ((a - b).div b b_nz).succ := by
  intro a b b_nz a_ge_b
  unfold div
  rw [div_mod_induction.is_ge _ _ _ a b]
  assumption

#print axioms nat.div.is_ge

def nat.mod.is_lt : ∀{ a b: nat } (b_nz: 0 < b), a < b -> a.mod b b_nz = a := by
  intro a b b_nz a_lt_b
  unfold mod
  rw [div_mod_induction.is_lt]
  assumption

#print axioms nat.mod.is_lt

def nat.mod.is_ge : ∀{ a b: nat } (b_nz: 0 < b), a ≥ b -> a.mod b b_nz = (a - b).mod b b_nz := by
  intro a b b_nz a_ge_b
  unfold mod
  rw [div_mod_induction.is_ge _ _ _ a b]
  assumption

#print axioms nat.mod.is_ge

def nat.div.is_lt' : ∀{ a b: nat } (b_nz: 0 < b), a < b -> a / b = 0 := by
  intro a b b_nz a_lt_b
  rw [nat.div_eq]
  apply nat.div.is_lt
  repeat assumption

#print axioms nat.div.is_lt'

def nat.div.is_ge' : ∀{ a b: nat } (_: 0 < b), a ≥ b -> a / b = ((a - b) / b).succ := by
  intro a b b_nz a_ge_b
  rw [nat.div_eq, nat.div_eq]
  apply nat.div.is_ge
  repeat assumption

#print axioms nat.div.is_ge'

def nat.mod.is_lt' : ∀{ a b: nat } (_: 0 < b), a < b -> a % b = a := by
  intro a b b_nz a_lt_b
  rw [nat.mod_eq]
  apply nat.mod.is_lt
  repeat assumption

#print axioms nat.mod.is_lt'

def nat.mod.is_ge': ∀{ a b: nat } (_: 0 < b), a ≥ b -> a % b = (a - b) % b := by
  intro a b b_nz a_ge_b
  rw [nat.mod_eq, nat.mod_eq]
  apply nat.mod.is_ge
  repeat assumption

#print axioms nat.mod.is_ge'

def nat.mod_lt (a b: nat) (b_nz: 0 < b) : a % b < b := by
  rw [nat.mod_eq b_nz]
  apply nat.div_mod_induction (fun a b => ∀b_nz, mod a b b_nz < b)
  {
    intro a b a_lt_b b_nz
    rw [nat.mod.is_lt]
    assumption
    assumption
  }
  {
    intro a b _ ih b_nz
    rw [nat.mod.is_ge]
    exact ih b_nz
    assumption
  }
  assumption

#print axioms nat.mod_lt

def nat.div_def (a b: nat) (b_nz: 0 < b) : a = (a / b) * b + a % b := by
  apply nat.div_mod_induction (fun a b => 0 < b -> a = (a / b) * b + a % b)
  {
    intro a b a_lt_b b_nz
    rw [nat.mod.is_lt', nat.div.is_lt']
    rw [zero_mul, zero_add]
    repeat assumption
  }
  {
    intro a b _ ih b_nz
    rw [nat.mod.is_ge', nat.div.is_ge']
    rw [succ_mul, add_assoc, ←ih, add_sub, add_comm, ←add_sub, sub_refl, add_zero]
    apply le_refl
    repeat assumption
  }
  repeat assumption

#print axioms nat.div_def

