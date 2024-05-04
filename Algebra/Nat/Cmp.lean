import Algebra.Nat.Basic

def nat.cmp (a b: nat) : Ordering := match a, b with
  | nat.zero, nat.zero => Ordering.eq
  | nat.zero, nat.succ _ => Ordering.lt
  | nat.succ _, nat.zero => Ordering.gt
  | nat.succ a, nat.succ b => a.cmp b

#print axioms nat.cmp

def nat.cmp.swap {a b: nat} : a.cmp b = (b.cmp a).swap := by
  induction a generalizing b with
  | zero => cases b <;> trivial
  | succ a ih => 
    cases b with
    | zero => trivial
    | succ b => exact ih

#print axioms nat.cmp.swap

def nat.cmp.swap_eq {a b: nat} {o: Ordering} : a.cmp b = o -> b.cmp a = o.swap := by
  intro a_cmp_b
  rw [←a_cmp_b]
  apply nat.cmp.swap

#print axioms nat.cmp.swap_eq

instance nat.le : LE nat where
  le a b := nat.cmp a b = Ordering.lt ∨ nat.cmp a b = Ordering.eq

#print axioms nat.le

instance nat.lt : LT nat where
  lt a b := nat.cmp a b = Ordering.lt

#print axioms nat.lt

instance nat.beq : BEq nat where
  beq a b := nat.cmp a b = Ordering.eq

#print axioms nat.beq

instance nat.lawful_beq : LawfulBEq nat where
  eq_of_beq := by
    intro a b a_eq_b
    induction a generalizing b with
    | zero =>
      cases b with
      | zero => trivial
      | succ _ => contradiction
    | succ a ih =>
      cases b with
      | zero => contradiction
      | succ b =>
        have a_eq_b : a == b := a_eq_b
        rw [ih a_eq_b]
  rfl := by
    intro a
    induction a with
    | zero => rfl
    | succ _ ih => exact ih

#print axioms nat.lawful_beq

def nat.beq_symm { a b: nat } : a == b -> b == a := by
  intro a_eq_b
  rw [nat.lawful_beq.eq_of_beq a_eq_b]
  exact nat.lawful_beq.rfl

#print axioms nat.beq_symm

def nat.le_of_lt { a b: nat } : a < b -> a ≤ b := Or.inl

#print axioms nat.le_of_lt

def nat.le_refl (a: nat) : a ≤ a := by
  apply Or.inr
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

#print axioms nat.le_refl

def nat.le_of_beq { a b: nat } : a == b -> a ≤ b := by
  intro a_eq_b
  rw [nat.lawful_beq.eq_of_beq a_eq_b]
  apply nat.le_refl

#print axioms nat.le_of_beq

def nat.le_of_eq { a b: nat } : a = b -> a ≤ b := by
  intro a_eq_b
  rw [a_eq_b]
  apply nat.le_refl

#print axioms nat.le_of_eq

def nat.ge_of_gt { a b: nat } : a > b -> a ≥ b := nat.le_of_lt

#print axioms nat.ge_of_gt

def nat.ge_refl (a: nat) : a ≥ a := nat.le_refl a

#print axioms nat.ge_refl

def nat.ge_of_beq { a b: nat } : a == b -> a ≥ b := fun a_eq_b => nat.le_of_beq (nat.beq_symm a_eq_b)

#print axioms nat.ge_of_beq

def nat.ge_of_eq { a b: nat } : a = b -> a ≥ b := fun a_eq_b => nat.le_of_eq a_eq_b.symm 

#print axioms nat.ge_of_eq

def nat.eq_of_cmp { a b: nat } : a.cmp b = Ordering.eq -> a = b := by
  intro a_eq_b
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => trivial
    | succ _ => contradiction
  | succ a ih =>
    cases b with
    | zero => contradiction
    | succ b =>
      have a_eq_b : cmp a b = Ordering.eq := a_eq_b
      rw [ih a_eq_b]

#print axioms nat.eq_of_cmp

def nat.gt_of_cmp { a b: nat } : a.cmp b = Ordering.gt -> a > b := by
  intro a_gt_b
  exact nat.cmp.swap_eq a_gt_b

#print axioms nat.gt_of_cmp

def nat.lt_or_eq_of_le { a b: nat } : a ≤ b -> a < b ∨ a = b := by
  intro a_le_b
  cases a_le_b with
  | inl a_lt_b => exact Or.inl a_lt_b
  | inr a_eq_b => 
    apply Or.inr
    exact nat.eq_of_cmp a_eq_b

#print axioms nat.lt_or_eq_of_le

def nat.lt_or_ge (a b: nat) : a < b ∨ a ≥ b := by
  cases h:nat.cmp a b
  exact Or.inl h
  exact Or.inr <| nat.ge_of_eq (nat.eq_of_cmp h)
  exact Or.inr <| nat.ge_of_gt (nat.gt_of_cmp h)

#print axioms nat.lt_or_ge

def nat.zero_le (a: nat) : 0 ≤ a := by
  cases a
  exact nat.le_of_eq rfl
  exact nat.le_of_lt rfl

#print axioms nat.zero_le

def nat.le_zero {a: nat} : a ≤ 0 -> a = 0 := by
  intro a_le_zero
  cases a with
  | zero => rfl
  | succ a => cases a_le_zero <;> contradiction

#print axioms nat.le_zero

def nat.not_lt_zero {a: nat} : a < 0 -> False := by
  intro a_lt_zero
  cases a <;> contradiction

def nat.lt_succ_self (a: nat) : a < a.succ := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

#print axioms nat.lt_succ_self

def nat.lt_of_succ_lt_succ { a b: nat } : a.succ < b.succ -> a < b := id

#print axioms nat.lt_of_succ_lt_succ

def nat.succ_lt_succ { a b: nat } : a < b -> a.succ < b.succ := id

#print axioms nat.succ_lt_succ

def nat.le_of_succ_le_succ { a b: nat } : a.succ ≤ b.succ -> a ≤ b := id

#print axioms nat.le_of_succ_le_succ

def nat.succ_le_succ { a b: nat } : a ≤ b -> a.succ ≤ b.succ := id

#print axioms nat.succ_le_succ

def nat.le_antisymm { a b: nat } : a ≤ b -> b ≤ a -> a = b := by
  intro a_le_b b_le_a
  induction a generalizing b with
  | zero =>
    rw [nat.le_zero b_le_a]
    rfl
  | succ a ih =>
    cases b with
    | zero => 
      have := nat.le_zero a_le_b
      contradiction
    | succ b => rw [ih a_le_b b_le_a]

#print axioms nat.le_antisymm

def nat.not_lt_and_ge { a b: nat } : a < b -> a ≥ b -> False := by
  intro a_lt_b a_ge_b
  induction b generalizing a with
  | zero => exact nat.not_lt_zero a_lt_b
  | succ b ih =>
    cases a with
    | zero =>
      have := nat.le_zero a_ge_b
      contradiction
    | succ a => exact ih a_lt_b a_ge_b

#print axioms nat.not_lt_and_ge
