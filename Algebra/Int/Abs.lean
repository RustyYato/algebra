import Algebra.Int.Neg

def int.abs (i: int) : nat := match i with
 | .zero => .zero
 | .pos_succ n => n.succ
 | .neg_succ n => n.succ

#print axioms int.abs

def int.sign.signum (i: int.Sign) : int := match i with
  | .neg => -1
  | .pos => 1
  | .zero => 0

#print axioms int.sign.signum

def int.signum (i: int) : int := match i with
  | .neg_succ _ => -1
  | .pos_succ _ => 1
  | .zero => 0

#print axioms int.signum

def int.signum.of_nat (n: nat) : n.to_int.signum ≠ -1 := by
  cases n <;> (intro; contradiction)

#print axioms int.signum.of_nat

def int.signum.neg (i: int) : i.neg.signum = i.signum.neg := by
  cases i <;> rfl

#print axioms int.signum.neg

def int.abs.ge (i: int) : i ≤ i.abs := by
  cases i
  trivial
  apply Or.inr
  apply compare_eq_refl
  apply Or.inl
  rfl

#print axioms int.abs.ge

def int.abs.sign { x: int } : x.sign * x.abs = x := by cases x <;> rfl

#print axioms int.abs.sign

def int.abs.flip_sign { x: int } : x.sign.flip * x.abs = -x := by cases x <;> rfl

#print axioms int.abs.flip_sign

def int.abs.sign_mul { s: int.Sign } { x: nat } : s ≠ int.Sign.zero ∨ x = .zero -> int.abs (s * x) = x := by
  intro c
  cases s <;> cases x
  any_goals rfl
  rename_i x
  cases c <;> contradiction

#print axioms int.abs.sign_mul

def int.abs.zero : int.abs 0 = 0 := rfl
def int.abs.pos_succ : int.abs (.pos_succ a) = a.succ := rfl
def int.abs.neg_succ : int.abs (.neg_succ a) = a.succ := rfl

def int.abs.of_nat (a: nat) : int.abs a = a := by
  cases a <;> rfl

#print axioms int.abs.of_nat

def int.abs.neg_of_nat { a: nat } : int.abs (-a) = a := by
  cases a <;> rfl

#print axioms int.abs.neg_of_nat

def int.abs.neg { a: int } : int.abs (-a) = a.abs := by cases a <;> rfl

#print axioms int.abs.neg

def int.abs.of_nonneg (a: int) : 0 ≤ a -> int.abs a = a := by
  intro h
  cases a
  rfl
  rfl
  cases h <;> contradiction
