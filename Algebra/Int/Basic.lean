import Algebra.Nat.Basic

inductive int where
  | zero
  | pos_succ (val: nat)
  | neg_succ (val: nat)
deriving DecidableEq

def int.ofNat (n: Nat) : int := match n with
  | .zero => .zero
  | .succ n => .pos_succ <| nat.ofNat n

def int.toInt (n: int) : Int := match n with
  | .zero => .ofNat 0
  | .pos_succ n => .ofNat n.toNat.succ
  | .neg_succ n => .neg n.toNat.succ

instance int.instOfNat (n: Nat) : OfNat int n where
  ofNat := int.ofNat n

instance int.instRepr : Repr int where
  reprPrec n := reprPrec n.toInt

def int.zero_eq : int.zero = 0 := rfl
#print axioms nat.zero_eq
def int.one_eq : int.pos_succ .zero = 1 := rfl
#print axioms nat.one_eq
