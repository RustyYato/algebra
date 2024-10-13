import Algebra.Nat.Basic
import Algebra.Order.Basic

def nat.cmp (a b: nat) : Ordering := match a, b with
  | nat.zero, nat.zero => Ordering.eq
  | nat.zero, nat.succ _ => Ordering.lt
  | nat.succ _, nat.zero => Ordering.gt
  | nat.succ a, nat.succ b => a.cmp b

#print axioms nat.cmp

instance nat.ordInst : Ord nat := ⟨ nat.cmp ⟩

def nat.cmp.swap {a b: nat} : a.cmp b = (b.cmp a).swap := by
  induction a generalizing b with
  | zero => cases b <;> trivial
  | succ a ih =>
    cases b with
    | zero => trivial
    | succ b => exact ih

#print axioms nat.cmp.swap

def nat.cmp.refl (a: nat) : a.cmp a = .eq := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

#print axioms nat.cmp.refl

def nat.cmp.eq_of_compare_eq { a b: nat } : compare a b = Ordering.eq -> a = b := by
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
        rw [ih]
        assumption

#print axioms nat.cmp.eq_of_compare_eq

def nat.cmp.trans { a b c: nat } { o : Ordering } :
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

#print axioms nat.cmp.trans

instance nat.totalOrdInst : TotalOrder nat where
  compare_transitive := by intros; apply cmp.trans <;> assumption
  eq_of_compare_eq := by intros; apply cmp.eq_of_compare_eq; assumption
  compare_eq_refl := by intros; apply cmp.refl
  compare_antisymm := by intros; apply cmp.swap

inductive LtOrGe (a b: nat): Type where
  | Lt : a < b -> LtOrGe a b
  | Ge : a ≥ b -> LtOrGe a b

def nat.lt_or_ge_dec (a b: nat) : LtOrGe a b :=
  match  h:nat.cmp a b with
  | .lt =>.Lt h
  | .eq => .Ge <| ge_of_eq (eq_of_compare_eq h)
  | .gt => .Ge <| ge_of_gt (gt_of_compare h)

#print axioms nat.lt_or_ge_dec

def nat.zero_le (a: nat) : 0 ≤ a := by
  cases a
  exact le_of_eq rfl
  exact le_of_lt rfl

#print axioms nat.zero_le

def nat.le_zero {a: nat} : a ≤ 0 -> a = 0 := by
  intro a_le_zero
  cases a with
  | zero => rfl
  | succ a => cases a_le_zero <;> contradiction

#print axioms nat.le_zero

def nat.zero_lt_succ { a: nat } : 0 < a.succ := rfl

#print axioms nat.zero_lt_succ

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

def nat.lt_succ_of_le { a b: nat } : a ≤ b -> a < b.succ := by
  intro a_le_b
  induction a generalizing b with
  | zero => apply nat.zero_lt_succ
  | succ a ih =>
    cases b with
    | zero =>
      have := le_zero a_le_b
      contradiction
    | succ b =>
      apply ih
      assumption

#print axioms nat.lt_succ_of_le

def nat.succ_le_of_lt { a b: nat } : a < b -> a.succ ≤ b := by
  intro a_lt_b_succ
  induction a generalizing b with
  | zero =>
    match b with
    | .succ b => apply nat.zero_le
  | succ a ih =>
    cases b with
    | zero =>
      have := nat.not_lt_zero a_lt_b_succ
      contradiction
    | succ b =>
      apply ih
      assumption

#print axioms nat.succ_le_of_lt

def nat.lt_of_succ_le { a b: nat } : a.succ ≤ b -> a < b := by
  intro a_le_b
  induction a generalizing b with
  | zero =>
    match b with
    | .succ b => apply nat.zero_lt_succ
  | succ a ih =>
    cases b with
    | zero =>
      have := le_zero a_le_b
      contradiction
    | succ b =>
      apply ih
      assumption

#print axioms nat.succ_le_of_lt

def nat.lt_or_ge_dec.pick_lt {a b: nat} : (a_lt_b: a < b) -> nat.lt_or_ge_dec a b = LtOrGe.Lt a_lt_b := by
  intro a_lt_b
  match a.lt_or_ge_dec b with
  | .Lt a_lt_b => rfl
  | .Ge a_ge_b =>
    have := not_lt_of_ge a_ge_b a_lt_b
    contradiction

#print axioms nat.lt_or_ge_dec.pick_lt

def nat.lt_or_ge_dec.pick_ge {a b: nat} : (a_ge_b: a ≥ b) -> nat.lt_or_ge_dec a b = LtOrGe.Ge a_ge_b := by
  intro a_ge_b
  match a.lt_or_ge_dec b with
  | .Lt a_lt_b =>
    have := not_lt_of_ge a_ge_b a_lt_b
    contradiction
  | .Ge a_ge_b => rfl

#print axioms nat.lt_or_ge_dec.pick_ge

def nat.zero_lt_of_lt { a b: nat } (a_lt_b: a < b): 0 < b := lt_of_le_of_lt (zero_le _) a_lt_b

#print axioms nat.zero_lt_of_lt

def nat.toNat_lt { a b: nat } : a < b -> a.toNat < b.toNat := by
  intro a_lt_b
  induction a generalizing b with
  | zero =>
    match b with
    | .succ _ => apply Nat.zero_lt_succ
  | succ a ih =>
    match b with
    | .succ b =>
    unfold toNat
    apply Nat.succ_lt_succ
    apply ih
    assumption

#print axioms nat.toNat_lt

def nat.toNat_le { a b: nat } : a ≤ b -> a.toNat ≤ b.toNat := by
  intro a_lt_b
  induction a generalizing b with
  | zero =>
    apply Nat.zero_le
  | succ a ih =>
    match b with
    | .succ b =>
    unfold toNat
    apply Nat.succ_le_succ
    apply ih
    assumption

#print axioms nat.toNat_le

def nat.ofNat_lt { a b: Nat } : a < b -> nat.ofNat a < nat.ofNat b := by
  intro a_lt_b
  induction a generalizing b with
  | zero =>
    match b with
    | .succ _ => trivial
  | succ a ih =>
    match b with
    | .succ b =>
    apply nat.succ_lt_succ
    apply ih
    apply Nat.lt_of_succ_lt_succ
    exact a_lt_b

#print axioms nat.toNat_lt

def nat.ofNat_le { a b: Nat } : a ≤ b -> nat.ofNat a ≤ nat.ofNat b := by
  intro a_le_b
  induction a generalizing b with
  | zero => apply zero_le
  | succ a ih =>
    match b with
    | .succ b =>
    apply nat.succ_le_succ
    apply ih
    apply Nat.le_of_succ_le_succ
    exact a_le_b

#print axioms nat.toNat_le

def nat.compare.succ (a b: nat) : compare a.succ b.succ = compare a b := rfl

#print axioms nat.compare.succ
