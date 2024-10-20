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

def nat.zero_eq : nat.zero = 0 := rfl
#print axioms nat.zero_eq
def nat.one_eq : nat.zero.succ = 1 := rfl
#print axioms nat.one_eq

def nat.toNat_ofNat (n: nat) : .ofNat n.toNat = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold ofNat toNat
    dsimp
    rw [ih]

def nat.ofNat_toNat (n: Nat) : (nat.ofNat n).toNat = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold ofNat toNat
    dsimp
    rw [ih]
