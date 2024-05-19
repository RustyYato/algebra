import Algebra.Int.Add
import Algebra.Int.Abs
import Algebra.Nat.Mul

def int.mul (a b: int) : int := a.sign * b.sign * (a.abs * b.abs)

#print axioms int.mul

instance int.mul.inst : Mul int := ⟨ int.mul ⟩ 

