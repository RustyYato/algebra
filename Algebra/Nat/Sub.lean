import Algebra.Nat.Add
import Algebra.Nat.Dec

-- saturating sub, to make proofs simpler
def nat.sub (a b: nat) := match b with
  | nat.zero => a
  | nat.succ b => a.dec.sub b

#print axioms nat.sub

def nat.pred (n: nat) :=
  match n with
  | .succ n => n
  | .zero => 0

instance nat.sub_inst : Sub nat where
  sub := nat.sub

def nat.sub_def (a b: nat) : a - b = a.sub b := rfl
def nat.sub_zero (a: nat) : a - 0 = a := by
  rw [nat.sub_def]
  unfold sub
  rfl

#print axioms nat.sub_zero

def nat.sub_succ (a b: nat) : a - b.succ = a.dec - b := rfl

#print axioms nat.sub_succ

def nat.zero_sub (b: nat) : 0 - b = 0 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [nat.sub_succ]
    exact ih

#print axioms nat.zero_sub

def nat.succ_sub_succ (a b: nat) : a.succ - b.succ = a - b := rfl

#print axioms nat.succ_sub_succ

def nat.sub.refl (a: nat) : a - a = 0 := by
  induction a with
  | zero => rfl
  | succ _ ih => rw [succ_sub_succ, ih]

#print axioms nat.sub.refl

def nat.succ_sub {a b: nat} : b ≤ a -> a.succ - b = (a - b).succ := by
  intro b_le_a
  induction a generalizing b with
  | zero =>
    rw [le_zero b_le_a]
    rfl
  | succ a  ih =>
    cases lt_or_eq_of_le b_le_a with
    | inl b_lt_a_succ =>
      have b_le_a := le_of_lt_succ b_lt_a_succ
      cases b with
      | zero => rfl
      | succ b =>
        rw [succ_sub_succ, succ_sub_succ]
        apply ih
        apply le_trans _ b_le_a
        apply le_of_lt
        apply lt_succ_self
    | inr b_eq_a_succ =>
      rw [b_eq_a_succ]
      repeat rw [succ_sub_succ, sub_refl]
      clear ih b_le_a b_eq_a_succ b
      induction a with
      | zero => rfl
      | succ _ ih => congr

#print axioms nat.succ_sub

def nat.sub_add (a b c: nat) : a - (b + c) = a - b - c := by
  cases a with
  | zero =>
    rw [zero_eq]
    repeat rw [nat.zero_sub]
  | succ a =>
    cases b with
    | zero => rw [zero_eq, zero_add, sub_zero]
    | succ b =>
      rw [succ_add, succ_sub_succ, succ_sub_succ]
      apply nat.sub_add

#print axioms nat.sub_add

def nat.add_sub (a b c: nat) : c ≤ b -> a + (b - c) = (a + b) - c := by
  intro c_le_b
  induction b generalizing c with
  | zero =>
    rw [le_zero c_le_b]
    rfl
  | succ b ih =>
    cases lt_or_eq_of_le c_le_b with
    | inl c_lt_b_succ =>
      have c_le_b := le_of_lt_succ c_lt_b_succ
      rw [add_succ]
      rw [nat.succ_sub, nat.succ_sub, add_succ]
      rw [ih c c_le_b]
      apply le_trans c_le_b
      apply add.le_right
      assumption
    | inr c_eq_b =>
      rw [c_eq_b]
      rw [succ_sub_succ, add_succ, succ_sub_succ, ih]
      apply le_refl

#print axioms nat.add_sub

def nat.add_sub_inv (a b: nat) : a + b - b = a := by
  rw [←add_sub, sub.refl, add_zero]
  apply le_refl

#print axioms nat.add_sub_inv

def nat.sub_add_inv (a b: nat) : b ≤ a -> a - b + b = a := by
  intro b_le_a
  rw [add.comm, nat.add_sub, add.comm]
  apply nat.add_sub_inv
  assumption

#print axioms nat.sub_add_inv

def nat.sub.le_left (a b c: nat) : a ≤ b -> a - c ≤ b - c := by
  intro a_le_b
  induction c generalizing a b with
  | zero => rw [zero_eq, sub_zero, sub_zero]; assumption
  | succ c ih =>
  cases a with
  | zero =>
    rw [zero_eq, zero_sub]
    apply zero_le
  | succ a =>
    match b with
    | succ b =>
    rw [succ_sub_succ, succ_sub_succ]
    exact ih a b a_le_b

#print axioms nat.sub.le_left

def nat.sub.le (a b: nat) : a - b ≤ a := by
  induction b with
  | zero =>
    apply le_of_eq
    rw [zero_eq, sub_zero]
  | succ x ih =>
    rw [sub_succ]
    apply le_trans _ ih
    apply le_left
    apply dec.le

#print axioms nat.sub.le

def nat.sub.lt_nz (a b: nat) : 0 < b -> b ≤ a -> a - b < a := by
  intro b_nz b_le_a
  match b with
  | .succ b =>
  match a with
  | .succ a =>
  rw [succ_sub_succ]
  apply lt_of_le_of_lt
  apply le
  apply lt_succ_self

#print axioms nat.sub.lt_nz

def nat.sub.lt { a b: nat }: a < b -> a - b = 0 := by
  induction b generalizing a with
  | zero =>
    intro  h
    have := nat.not_lt_zero h
    contradiction
  | succ b ih =>
    intro a_le_b
    cases a with
    | zero => rw [zero_eq, zero_sub]
    | succ a =>
      rw [succ_sub_succ]
      apply ih
      assumption

#print axioms nat.sub.lt

def nat.sub_sub (a b c: nat) : c ≤ b -> a - (b - c) = (a + c) - b := by
  intro c_le_b
  induction b generalizing a c with
  | zero =>
    cases nat.le_zero c_le_b
    rw [sub_zero, zero_eq, sub_zero, add_zero, sub_zero]
  | succ b ih =>
    cases c with
    | zero => rw [zero_eq, add_zero, sub_zero]
    | succ c =>
      rw [succ_sub_succ, add_succ, succ_sub_succ]
      apply ih
      exact c_le_b

#print axioms nat.sub_sub

def nat.sub.eq_zero {a b: nat} : a - b = 0 ↔ a ≤ b := by
  induction a generalizing b with
  | zero =>
    apply Iff.intro
    intro
    apply zero_le
    intro
    rw [zero_eq, zero_sub]
  | succ a ih =>
    match b with
    | 0 =>
      apply Iff.intro
      intro
      contradiction
      intro h
      have := not_lt_and_ge nat.zero_lt_succ h
      contradiction
    | succ b =>
      rw [succ_sub_succ]
      apply Iff.intro
      intro h
      apply succ_le_succ
      exact ih.mp h
      intro h
      exact ih.mpr h

#print axioms nat.sub.eq_zero

def nat.sub.compare_strict (a b c: nat) :
  c ≤ a ->
  c ≤ b ->
  compare (a - c) (b - c) = compare a b := by
  intro c_le_a c_le_b
  rw [←nat.add.compare_right (a - c) (b - c) c, nat.sub_add_inv, nat.sub_add_inv]
  assumption
  assumption
