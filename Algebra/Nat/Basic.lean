inductive nat : Type where
  | zero
  | succ (n: nat)
deriving DecidableEq

def nat.ofNat (n: Nat) : nat := match n with
  | .zero => .zero
  | .succ n => .succ <| nat.ofNat n

def nat.toNat (n: nat) : Nat := match n with
  | .zero => .zero
  | .succ n => .succ n.toNat

instance nat.of_Nat (n: Nat) : OfNat nat n where
  ofNat := nat.ofNat n

instance nat.repr : Repr nat where
  reprPrec n := reprPrec n.toNat

