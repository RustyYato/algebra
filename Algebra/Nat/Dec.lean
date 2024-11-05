import Algebra.Nat.Cmp

def nat.dec (a: nat) : nat := match a with
  | .zero => .zero
  | .succ a => a

#print axioms nat.dec

def nat.dec.le (a: nat) : a.dec ≤ a :=
  match a with
  | .zero => le_of_eq rfl
  | .succ _ => le_of_lt lt_succ_self

#print axioms nat.dec.le
