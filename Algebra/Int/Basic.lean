import Algebra.Nat.Basic

inductive int where
  | zero
  | pos_succ (val: nat)
  | neg_succ (val: nat)
deriving DecidableEq

inductive int.Sign where
  | zero
  | pos
  | neg
deriving DecidableEq, Repr

def int.ofNat (n: Nat) : int := match n with
  | .zero => .zero
  | .succ n => .pos_succ <| nat.ofNat n

def int.of_nat (n: nat) : int := match n with
  | .zero => .zero
  | .succ n => .pos_succ n

def nat.to_int (n: nat) : int := int.of_nat n 

def int.toInt (n: int) : Int := match n with
  | .zero => .ofNat 0
  | .pos_succ n => .ofNat n.toNat.succ
  | .neg_succ n => .neg n.toNat.succ

instance int.instOfNat (n: Nat) : OfNat int n where
  ofNat := int.ofNat n

instance int.instRepr : Repr int where
  reprPrec n := reprPrec n.toInt

def int.zero_eq : int.zero = 0 := rfl
#print axioms int.zero_eq
def int.one_eq : int.pos_succ .zero = 1 := rfl
#print axioms int.one_eq

instance nat_to_int : Coe nat int where
  coe := int.of_nat

instance Nat_to_int : Coe Nat int where
  coe := int.ofNat

@[simp]
instance nat.Sign.mulInst : Mul int.Sign where
  mul a b := match a, b with
    | .zero, _ | _, .zero => .zero
    | .pos, .pos | .neg, .neg => .pos
    | .pos, .neg | .neg, .pos => .neg

@[simp]
instance nat.mul_sign : HMul int.Sign nat int where
  hMul s n := match s with
    | .zero => .zero
    | .pos => match n with
      | .zero => .zero
      | .succ n => .pos_succ n
    | .neg => match n with
      | .zero => .zero
      | .succ n => .neg_succ n

#print axioms nat.mul_sign
