import Algebra.Int.Neg

def int.abs (i: int) : nat := match i with
 | .zero => .zero
 | .pos_succ n => n.succ
 | .neg_succ n => n.succ

#print axioms int.abs

def int.sign (i: int) : int.Sign := match i with
  | .zero => .zero
  | .pos_succ _ => .pos
  | .neg_succ _ => .neg

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
  apply TotalOrder.compare_eq_refl
  apply Or.inl
  rfl

#print axioms int.abs.ge

