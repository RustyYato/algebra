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

inductive LtOrGe (a b: nat): Type where
  | Lt : a < b -> LtOrGe a b
  | Ge : a ≥ b -> LtOrGe a b

def nat.lt_or_ge_dec (a b: nat) : LtOrGe a b := 
  match  h:nat.cmp a b with
  | .lt =>.Lt h
  | .eq => .Ge <| nat.ge_of_eq (nat.eq_of_cmp h)
  | .gt => .Ge <| nat.ge_of_gt (nat.gt_of_cmp h)

#print axioms nat.lt_or_ge_dec

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

def nat.le_of_lt_succ { a b: nat } : a < b.succ -> a ≤ b := by
  intro a_lt_b_succ
  induction a generalizing b with
  | zero => apply nat.zero_le
  | succ a ih =>
    cases b with
    | zero =>
      have := nat.not_lt_zero a_lt_b_succ
      contradiction
    | succ b => 
      apply ih
      assumption

#print axioms nat.le_of_lt_succ

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

def nat.cmp_trans { a b c: nat } { o : Ordering } :
  a.cmp b = o -> 
  b.cmp c = o ->
  a.cmp c = o := by
    intro cmp_ab cmp_bc
    induction a generalizing b c with
    | zero =>
      cases b with
      | zero => exact cmp_bc
      | succ b =>
        unfold cmp at cmp_ab
        rw [←cmp_ab] at cmp_bc
        rw [←cmp_ab]
        clear cmp_ab o
        cases c <;> trivial
    | succ a iha =>
      cases b with
      | zero =>
        unfold cmp at cmp_ab
        rw [←cmp_ab] at cmp_bc
        rw [←cmp_ab]
        cases c <;> contradiction
      | succ b =>
        cases c with
        | zero =>
          unfold cmp at cmp_bc
          rw [←cmp_bc]
          rfl
        | succ c => exact iha cmp_ab cmp_bc

#print axioms nat.cmp_trans

def nat.cmp_or_eq_trans { a b c: nat } { o : Ordering } :
  a.cmp b = o ∨ a.cmp b = Ordering.eq -> 
  b.cmp c = o ∨ b.cmp c = Ordering.eq ->
  a.cmp c = o ∨ a.cmp c = Ordering.eq:= by
  intro cmp_ab cmp_bc
  cases cmp_ab with
  | inr a_eq_b =>
    rw [nat.eq_of_cmp a_eq_b]
    assumption
  | inl cmp_ab =>
    cases cmp_bc with
    | inr b_eq_c =>
      rw [←nat.eq_of_cmp b_eq_c]
      apply Or.inl
      assumption
    | inl cmp_bc =>
      apply Or.inl
      apply nat.cmp_trans <;> assumption

#print axioms nat.cmp_or_eq_trans

def nat.lt_trans { a b c: nat } : a < b -> b < c -> a < c := nat.cmp_trans
def nat.le_trans { a b c: nat } : a ≤ b -> b ≤ c -> a ≤ c := nat.cmp_or_eq_trans

def nat.gt_trans { a b c: nat } : a > b -> b > c -> a > c := fun x y => nat.cmp_trans y x
def nat.ge_trans { a b c: nat } : a ≥ b -> b ≥ c -> a ≥ c := fun x y => nat.cmp_or_eq_trans y x

def nat.lt_of_lt_and_le { a b c: nat } : a < b -> b ≤ c -> a < c := by
  intro a_lt_b b_le_c
  cases nat.lt_or_eq_of_le b_le_c with
  | inl b_lt_c => apply nat.lt_trans <;> assumption
  | inr b_eq_c => rw [←b_eq_c]; assumption

#print axioms nat.lt_of_lt_and_le

def nat.lt_of_le_and_lt { a b c: nat } : a ≤ b -> b < c -> a < c := by
  intro a_le_b b_lt_c
  cases nat.lt_or_eq_of_le a_le_b with
  | inl a_lt_b => apply nat.lt_trans <;> assumption
  | inr a_eq_b => rw [a_eq_b]; assumption

#print axioms nat.lt_of_le_and_lt

def nat.lt_or_ge_dec.pick_lt {a b: nat} : (a_lt_b: a < b) -> nat.lt_or_ge_dec a b = LtOrGe.Lt a_lt_b := by
  intro a_lt_b
  match a.lt_or_ge_dec b with
  | .Lt a_lt_b => rfl
  | .Ge a_ge_b =>
    have := nat.not_lt_and_ge a_lt_b a_ge_b
    contradiction

#print axioms nat.lt_or_ge_dec.pick_lt

def nat.lt_or_ge_dec.pick_ge {a b: nat} : (a_ge_b: a ≥ b) -> nat.lt_or_ge_dec a b = LtOrGe.Ge a_ge_b := by
  intro a_ge_b
  match a.lt_or_ge_dec b with
  | .Lt a_lt_b =>
    have := nat.not_lt_and_ge a_lt_b a_ge_b
    contradiction
  | .Ge a_ge_b => rfl

#print axioms nat.lt_or_ge_dec.pick_ge
