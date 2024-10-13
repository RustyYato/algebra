import Algebra.Nat.Mul
import Algebra.Nat.Sub
import Algebra.Nat.WellFounded
import Algebra.MyOption

structure div_mod.IndCtx where
  motive: nat -> (b: nat) -> 0 < b -> Sort α
  is_lt: ∀(a b: nat), (a_lt_b: a < b) -> motive a b (nat.zero_lt_of_lt a_lt_b)
  is_ge: ∀(a b: nat), (b_nz: 0 < b) -> a ≥ b -> motive (a - b) b b_nz -> motive a b b_nz

def nat.div_mod.induction.fueled (ctx: div_mod.IndCtx) (fuel: nat):
  ∀a b b_nz, my_option (ctx.motive a b b_nz) := fun a b b_nz =>
    match fuel with
    | .zero => .none
    | .succ fuel =>
    match lt_or_ge_dec a b with
    | .Lt a_lt_b => .some <| ctx.is_lt a b a_lt_b
    | .Ge a_ge_b => match fueled ctx fuel (a - b) b b_nz with
      | .none => .none
      | .some prev => .some <| ctx.is_ge a b b_nz a_ge_b prev

def nat.div_mod.induction.fueled.termination
  {ctx: div_mod.IndCtx} {fuel: nat}:
  ∀{a b b_nz}, a < fuel -> fueled ctx fuel a b b_nz ≠ .none := by
    intro a b b_nz a_lt_fuel
    induction fuel generalizing a with
    | zero =>
      have := nat.not_lt_zero a_lt_fuel
      contradiction
    | succ fuel ih =>
      unfold fueled
      split
      rename_i a_lt_b _
      exact my_option.noConfusion
      rename_i a_ge_b _
      have ih := @ih (a - b) <|
        lt_of_lt_of_le
        (sub.lt_nz a b b_nz a_ge_b)
        (le_of_lt_succ a_lt_fuel)
      split
      rename_i h
      rw [h] at ih
      contradiction
      exact my_option.noConfusion

#print axioms nat.div_mod.induction.fueled.termination

def nat.div_mod.induction.fueled.fuel_irr
  (ctx: div_mod.IndCtx) (fuel_a fuel_b: nat):
  ∀a b b_nz, a < fuel_a -> a < fuel_b ->
    fueled ctx fuel_a a b b_nz = fueled ctx fuel_b a b b_nz
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
        exact lt_of_lt_of_le (sub.lt_nz a b b_nz a_ge_b) (le_of_lt_succ a_lt_fuel_a)
        exact lt_of_lt_of_le (sub.lt_nz a b b_nz a_ge_b) (le_of_lt_succ a_lt_fuel_b)

#print axioms nat.div_mod.induction.fueled.fuel_irr

def nat.div_mod.induction
  ( motive: nat -> (b: nat) -> 0 < b -> Sort α )
  ( is_lt: ∀(a b: nat), (a_lt_b: a < b) -> motive a b (nat.zero_lt_of_lt a_lt_b))
  ( is_ge: ∀(a b: nat), (b_nz: 0 < b) -> a ≥ b -> motive (a - b) b b_nz -> motive a b b_nz ):
  ∀a b b_nz, motive a b b_nz := fun a b b_nz => match h:induction.fueled (div_mod.IndCtx.mk motive is_lt is_ge) a.succ a b b_nz with
    | .some m => m
    | .none => False.elim <| induction.fueled.termination (lt_succ_self _) h

#print axioms nat.div_mod.induction

def nat.div_mod.induction.remove_fuel
  ( motive: nat -> (b: nat) -> 0 < b -> Sort α )
  ( is_lt: ∀(a b: nat), (a_lt_b: a < b) -> motive a b (nat.zero_lt_of_lt a_lt_b))
  ( is_ge: ∀(a b: nat), (b_nz: 0 < b) -> a ≥ b -> motive (a - b) b b_nz -> motive a b b_nz):
  ∀a b b_nz fuel,
  a < fuel ->
  induction.fueled (div_mod.IndCtx.mk motive is_lt is_ge) fuel a b b_nz =
  (.some (induction motive is_lt is_ge a b b_nz)) := by
  intro a b b_nz fuel a_lt_fuel
  unfold induction
  split
  {
    rename_i h
    rw [←h]
    rw [induction.fueled.fuel_irr]
    assumption
    apply lt_succ_self
  }
  {
    rename_i h
    exact False.elim <| induction.fueled.termination (lt_succ_self _) h
  }

#print axioms nat.div_mod.induction.remove_fuel

def nat.div_mod.induction.if_lt:
  ∀a b b_nz a_lt_b,
  induction motive is_lt is_ge a b b_nz = is_lt a b a_lt_b := by
  intro a b b_nz a_lt_b
  unfold induction
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
    rename_i h
    exact False.elim <| induction.fueled.termination (lt_succ_self _) h
  }

#print axioms nat.div_mod.induction.if_lt

def nat.div_mod.induction.if_ge
  ( motive: nat -> (b: nat) -> 0 < b -> Sort α )
  ( is_lt: ∀(a b: nat), (a_lt_b: a < b) -> motive a b (nat.zero_lt_of_lt a_lt_b))
  ( is_ge: ∀(a b: nat), (b_nz: 0 < b) -> a ≥ b -> motive (a - b) b b_nz -> motive a b b_nz):
  ∀a b b_nz a_ge_b,
  induction motive is_lt is_ge a b b_nz = is_ge a b b_nz a_ge_b (induction motive is_lt is_ge (a - b) b b_nz) := by
  intro a b b_nz a_ge_b
  conv => {
    lhs
    unfold induction
  }
  split
  {
    rename_i m h
    unfold fueled at h
    have pick_ge := nat.lt_or_ge_dec.pick_ge a_ge_b
    rw [pick_ge] at h
    simp only at h
    rw [remove_fuel] at h
    simp only at h
    exact my_option.some.inj h.symm
    apply sub.lt_nz
    repeat assumption
  }
  {
    rename_i h
    exact False.elim <| induction.fueled.termination (lt_succ_self _) h
  }

#print axioms nat.div_mod.induction.if_ge

def nat.div : ∀(_ b: nat), 0 < b -> nat := div_mod.induction
    (fun _ _ _ => nat)
    (fun _ _ _ => nat.zero)
    (fun _ _ _ _ prev => prev.succ)

#print axioms nat.div

def nat.mod : ∀(_ b: nat), 0 < b -> nat :=  div_mod.induction
    (fun _ _ _ => nat)
    (fun a _ _ => a)
    (fun _ _ _ _ prev => prev)

#print axioms nat.mod

def nat.div.def { a b: nat } { b_nz: 0 < b } : (a.div b b_nz) = (div_mod.induction
    (fun _ _ _ => nat)
    (fun _ _ _ => nat.zero)
    (fun _ _ _ _ prev => prev.succ) a b b_nz) := rfl

def nat.mod.def { a b: nat } { b_nz: 0 < b } : (a.mod b b_nz) = (div_mod.induction
    (fun _ _ _ => nat)
    (fun a _ _ => a)
    (fun _ _ _ _ prev => prev) a b b_nz) := rfl

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

def nat.div.if_lt' : ∀{ a b: nat } (b_nz: 0 < b), a < b -> a.div b b_nz = 0 := by
  intro a b b_nz a_lt_b
  unfold div
  rw [div_mod.induction.if_lt]
  rfl
  assumption

#print axioms nat.div.if_lt'

def nat.div.if_ge' : ∀{ a b: nat } (b_nz: 0 < b), a ≥ b -> a.div b b_nz = ((a - b).div b b_nz).succ := by
  intro a b b_nz a_ge_b
  unfold div
  rw [div_mod.induction.if_ge]
  assumption

#print axioms nat.div.if_ge'

def nat.mod.if_lt' : ∀{ a b: nat } (b_nz: 0 < b), a < b -> a.mod b b_nz = a := by
  intro a b b_nz a_lt_b
  unfold mod
  rw [div_mod.induction.if_lt]
  assumption

#print axioms nat.mod.if_lt'

def nat.mod.if_ge': ∀{ a b: nat } (b_nz: 0 < b), a ≥ b -> a.mod b b_nz = (a - b).mod b b_nz := by
  intro a b b_nz a_ge_b
  unfold mod
  rw [div_mod.induction.if_ge]
  assumption

#print axioms nat.mod.if_ge'

def nat.div.if_lt : ∀(a b: nat) (_: 0 < b), a < b -> a / b = 0 := by
  intro a b b_nz a_lt_b
  rw [nat.div_eq]
  apply nat.div.if_lt'
  repeat assumption

#print axioms nat.div.if_lt

def nat.div.if_ge:  ∀(a b: nat) (_: 0 < b), a ≥ b -> a / b = ((a - b) / b).succ := by
  intro a b b_nz a_ge_b
  rw [nat.div_eq, nat.div_eq]
  apply nat.div.if_ge'
  repeat assumption

#print axioms nat.div.if_ge

def nat.mod.if_lt : ∀(a b: nat) (_: 0 < b), a < b -> a % b = a := by
  intro a b b_nz a_lt_b
  rw [nat.mod_eq]
  apply nat.mod.if_lt'
  repeat assumption

#print axioms nat.mod.if_lt

def nat.mod.if_ge: ∀(a b: nat) (_: 0 < b), a ≥ b -> a % b = (a - b) % b := by
  intro a b b_nz a_ge_b
  rw [nat.mod_eq, nat.mod_eq]
  apply nat.mod.if_ge'
  repeat assumption

#print axioms nat.mod.if_ge

def nat.mod.lt (a b: nat) (b_nz: 0 < b) : a % b < b := by
  rw [nat.mod_eq b_nz]
  apply div_mod.induction (fun a b _ => ∀b_nz, mod a b b_nz < b)
  {
    intro a b a_lt_b b_nz
    rw [nat.mod.if_lt']
    assumption
    assumption
  }
  {
    intro a b _ _ ih b_nz
    rw [nat.mod.if_ge']
    exact ih b_nz
    assumption
  }
  assumption

#print axioms nat.mod.lt

def nat.div_def (a b: nat) (b_nz: 0 < b) : a = (a / b) * b + a % b := by
  apply div_mod.induction (fun a b _ => 0 < b -> a = (a / b) * b + a % b)
  {
    intro a b a_lt_b b_nz
    rw [nat.mod.if_lt, nat.div.if_lt]
    rw [zero_mul, zero_add]
    repeat assumption
  }
  {
    intro a b _ _ ih b_nz
    rw [nat.mod.if_ge, nat.div.if_ge]
    rw [succ_mul, add.assoc, ←ih, add_sub, add.comm, ←add_sub, sub.refl, add_zero]
    apply le_refl
    repeat assumption
  }
  repeat assumption

#print axioms nat.div_def

def nat.mod_zero : ∀{a: nat}, a % 0 = 0 := by intros; rfl

#print axioms nat.mod_zero

def nat.div_zero : ∀{a: nat}, a / 0 = 0 := by intros; rfl

#print axioms nat.div_zero

def nat.zero_mod : ∀{a: nat}, 0 % a = 0 := by
  intro a
  cases a <;> rfl

#print axioms nat.zero_mod

def nat.zero_div : ∀{a: nat}, 0 / a = 0 := by
  intro a
  cases a <;> rfl

#print axioms nat.zero_div

def nat.div.one : ∀{a: nat}, a / 1 = a := by
  intro a
  apply div_mod.induction (fun a b _ => b = 1 -> a / b = a) _ _ a 1 (zero_lt_succ) rfl
  {
    intro a b a_lt_b b_eq_one
    cases b_eq_one
    match a with
    | .zero => rfl
    | .succ a =>
      have := nat.not_lt_zero a_lt_b
      contradiction
  }
  {
    intro a b b_nz a_ge_b ih b_eq_one
    cases b_eq_one
    rw [div.if_ge]
    rw [ih rfl]
    any_goals assumption
    match a with
    | .succ a =>
    rw [←nat.one_eq, succ_sub_succ, zero_eq, sub_zero]
  }

#print axioms nat.div.one

def nat.mul_mod :∀(a b k: nat), (a * k) % (b * k) = (a % b) * k := by
  intro a b
  cases b with
  | zero =>
    intros
    rw [zero_eq, zero_mul, mod_zero, mod_zero, zero_mul]
  | succ b =>
  apply div_mod.induction (fun a b _ => ∀k, (a * k) % (b * k) = (a % b) * k)
  any_goals apply nat.zero_lt_succ
  {
    intro a b a_lt_b k
    cases k with
    | zero =>
      rw [zero_eq, mul_zero, mul_zero, mul_zero]
      rfl
    | succ k =>
    have : 0 < b := by
      apply lt_of_le_of_lt
      apply nat.zero_le
      any_goals assumption
    rw [mod.if_lt, mod.if_lt]
    assumption
    assumption
    apply lt_of_lt_of_le
    exact  this
    apply nat.mul.ge
    apply nat.zero_lt_succ
    rw [mul.comm a, mul.comm b]
    apply nat.mul.of_lt_cancel_left
    apply nat.zero_lt_succ
    assumption
  }
  {
    intro a b _ a_ge_b ih k
    cases k with
    | zero =>
      rw [zero_eq, mul_zero, mul_zero, mul_zero]; rfl
    | succ k =>
    cases b with
    | zero => rw [zero_eq, zero_mul, mod_zero, mod_zero, zero_mul]
    | succ b =>
    rw [mod.if_ge, mod.if_ge a b.succ]
    rw [←ih]
    congr
    rw [mul.comm _ k.succ, mul.comm _ k.succ, mul.comm _ k.succ, mul_sub]
    apply nat.zero_lt_succ
    assumption
    rw [mul_succ, succ_add]
    apply nat.zero_lt_succ
    rw [mul.comm a, mul.comm b.succ]
    apply nat.mul.of_le_cancel_left
    assumption
  }

def nat.div.gt_zero (a b: nat) : 0 < b -> b ≤ a -> a / b > 0 := by
  intro b_nz b_le_a
  rw [div.if_ge]
  any_goals assumption
  apply nat.zero_lt_succ

#print axioms nat.div.gt_zero

def nat.div.lt (a b: nat) : 1 < b -> 0 < a -> a / b < a := by
  intro b_gt_one a_nz
  conv => {
    rhs
    rw [nat.div_def a b (by
      apply lt_trans
      apply nat.lt_succ_self
      exact b_gt_one)]
  }
  match b with
  | .succ (.succ b) =>
  clear b_gt_one
  rw [mul_succ]
  conv => {
    lhs
    rw [←add_zero (a / _)]
  }
  rw [add.assoc]
  apply nat.add.of_lt_cancel_left
  apply div_mod.induction (fun (a b: nat) _ => 0 < a -> 1 < b -> 0 < a / b * b.dec + a % b)
  {
    clear b a_nz a
    clear b
    intro a b a_lt_b a_nz b_gt_one
    match a with
    | .succ a =>
    match b with
    | .succ (.succ b) =>
    clear a_nz b_gt_one
    unfold dec
    simp only
    rw [div.if_lt, zero_mul, zero_add, mod.if_lt]
    any_goals apply nat.zero_lt_succ
    assumption
    assumption
  }
  {
    clear b a_nz a
    clear b
    intro a b _ a_ge_b ih a_nz b_gt_one
    match a with
    | .succ a =>
    match b with
    | .succ (.succ b) =>
    clear a_nz b_gt_one
    unfold dec
    simp only
    rw [div.if_ge]
    rw [nat.mul_succ]
    repeat rw [succ_add]
    apply nat.zero_lt_succ
    apply nat.zero_lt_succ
    assumption
  }
  apply nat.zero_lt_succ
  assumption
  apply nat.zero_lt_succ
  assumption

#print axioms nat.div.lt

def nat.div.of_eq_zero { a b: nat } : a / b = 0 -> b = 0 ∨ a < b := by
  cases b with
  | zero => exact Or.inl
  | succ b =>
    intro div_eq_zero
    apply Or.inr
    apply Decidable.byContradiction
    intro h
    have a_ge_b_succ := not_lt_implies_ge h
    rw [if_ge] at div_eq_zero
    contradiction
    apply zero_lt_succ
    assumption

#print axioms nat.div.of_eq_zero

def nat.div.spec (a b: nat) (b_pos: 0 < b) :
  a / b = if a < b then 0 else ((a - b) / b).succ := by
  cases lt_or_ge a b
  · rename_i a_lt_b
    rw [if_pos, nat.div.if_lt]
    apply lt_of_le_of_lt
    apply nat.zero_le
    repeat assumption
  · rename_i a_ge_b
    rw [if_neg, nat.div.if_ge]
    repeat assumption
    apply flip not_lt_and_ge
    assumption

def nat.div.le_div_if_mul_le (a b: nat) (b_pos: 0 < b) : ∀c, b * c ≤ a -> c ≤ a / b := by
  apply nat.div_mod.induction (fun a b _ => ∀c, b * c ≤ a -> c ≤ a / b) _ _ a b b_pos
  <;> clear a b_pos b
  · intro a b b_pos c h
    rw [nat.div.if_lt]
    · match c with
      | nat.zero => apply le_refl
      | nat.succ c =>
        rw [nat.mul_succ] at h
        have := le_trans (nat.add.le_left _ _) h
        have := not_lt_of_ge this b_pos
        contradiction
    apply lt_of_le_of_lt _ b_pos
    apply nat.zero_le
    assumption
  · intro a b b_pos a_ge_b ih c h
    rw [nat.div.if_ge]
    any_goals trivial
    cases c with
    | zero => apply nat.zero_le
    | succ c =>
    apply nat.succ_le_succ
    apply ih
    rw [nat.mul_succ] at h
    generalize g:b * c = d
    rw [g] at h
    clear g c ih a_ge_b b_pos
    induction b generalizing a with
    | zero =>
      rw [zero_eq, sub_zero]
      rw [zero_eq, nat.zero_add] at h
      assumption
    | succ b ih =>
      cases a with
      | zero =>
        rw [succ_add] at h
        cases h <;> contradiction
      | succ a =>
      rw [succ_sub_succ]
      rw [succ_add] at h
      apply ih
      exact nat.le_of_succ_le_succ h

def nat.div.le { a b: nat } : a / b ≤ a := by
  cases b
  rw [zero_eq, div_zero]
  apply zero_le
  rename_i b
  have := div_def a b.succ zero_lt_succ
  conv => { rhs; rw [this] }
  apply flip le_trans
  apply nat.add.le_left
  exact mul.ge (a / b.succ) b.succ rfl

def nat.div.mul_le { a b: nat } : b * (a / b) ≤ a := by
  cases b
  rw [zero_eq, div_zero]
  apply zero_le
  rename_i b
  have := div_def a b.succ zero_lt_succ
  conv => { rhs; rw [this] }
  apply flip le_trans
  apply nat.add.le_left
  rw [mul.comm]

def nat.div_div { a b c: nat} : a / b / c = a / (b * c) := by
  cases b with
  | zero =>
    rw [zero_eq, div_zero, zero_mul, div_zero, zero_div]
  | succ b =>
  cases c with
  | zero =>
    rw [zero_eq, div_zero, mul_zero, div_zero]
  | succ c =>
  apply le_antisymm
  · apply div.le_div_if_mul_le
    exact zero_lt_succ
    rw [mul.assoc _ c.succ]
    apply le_trans
    apply nat.mul.le
    apply le_refl
    apply nat.div.mul_le
    apply nat.div.mul_le
  · apply div.le_div_if_mul_le
    exact zero_lt_succ
    apply div.le_div_if_mul_le
    exact zero_lt_succ
    rw [←mul.assoc]
    apply nat.div.mul_le

#print axioms nat.div_div
