import Algebra.Nat.Cmp

def nat.dec (a: nat) : nat := match a with
  | .zero => .zero
  | .succ a => a

#print axioms nat.dec


