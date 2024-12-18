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
def int.one_eq : int.pos_succ .zero = 1 := rfl
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

def int.sign (i: int) : int.Sign := match i with
  | .zero => .zero
  | .pos_succ _ => .pos
  | .neg_succ _ => .neg

@[simp]
def int.Sign.flip (s: int.Sign) : int.Sign := match s with
  | .zero => .zero
  | .pos => .neg
  | .neg => .pos

def int.sign.zero : int.sign 0 = .zero := rfl
def int.sign.pos : int.sign (int.pos_succ x) = .pos := rfl
def int.sign.neg : int.sign (int.neg_succ x) = .neg := rfl

def int.Sign.zero_left :  Sign.zero * x = Sign.zero := by cases x <;> rfl
def int.Sign.zero_right :  x * Sign.zero = Sign.zero := by cases x <;> rfl
def int.Sign.pos_left :  Sign.pos * x = x := by cases x <;> rfl
def int.Sign.pos_right :  x * Sign.pos = x := by cases x <;> rfl
def int.Sign.neg_left :  Sign.neg * x = x.flip := by cases x <;> rfl
def int.Sign.neg_right :  x * Sign.neg = x.flip := by cases x <;> rfl

def int.Sign.int_zero_nat { s: int.Sign } : s * (0: nat) = 0 := by cases s <;> rfl

def int.Sign.int_zero { x: nat } :  Sign.zero * x = (0: int) := by cases x <;> rfl
def int.Sign.int_pos { x: nat } :  Sign.pos * x = x := by cases x <;> rfl

def int.sign.of_sign_mul { s: int.Sign } { x: nat } : s = int.Sign.zero ∨ x ≠ .zero -> int.sign (s * x) = s := by
  intros
  cases s <;> cases x
  any_goals rfl
  all_goals (
    rename_i c
    cases c <;> contradiction
  )

def int.Sign.flip_flip { s: int.Sign } : s.flip.flip = s := by cases s <;> rfl

def int.of_nat.inj { a b: nat } : int.of_nat a = int.of_nat b -> a = b := by
  intro eq
  cases a <;> cases b <;> cases eq
  rfl; rfl

def int.of_nat.pos (a: nat) : int.pos_succ a = int.of_nat a.succ := rfl
def int.of_nat.zero : 0 = int.of_nat 0 := rfl
def int.OfNat_of_nat : OfNat.ofNat n = int.of_nat (OfNat.ofNat n) := by cases n <;> rfl
