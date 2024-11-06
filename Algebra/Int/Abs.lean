import Algebra.Int.Neg
import Algebra.Operators.AbsVal

def int.abs (i: int) : nat := match i with
 | .zero => .zero
 | .pos_succ n => n.succ
 | .neg_succ n => n.succ

instance : AbsoluteValue int nat := ⟨int.abs⟩

def int.abs.def (a: int) : ‖a‖ = a.abs := rfl

def int.sign.signum (i: int.Sign) : int := match i with
  | .neg => -1
  | .pos => 1
  | .zero => 0

def int.signum (i: int) : int := match i with
  | .neg_succ _ => -1
  | .pos_succ _ => 1
  | .zero => 0

def int.signum.of_nat (n: nat) : n.to_int.signum ≠ -1 := by
  cases n <;> (intro; contradiction)

def int.signum.neg (i: int) : i.neg.signum = i.signum.neg := by
  cases i <;> rfl

def int.abs.ge (i: int) : i ≤ int.of_nat ‖i‖ := by
  cases i
  trivial
  rfl
  exact .neg_pos

def int.abs.sign { x: int } : x.sign * ‖x‖ = x := by cases x <;> rfl

def int.abs.flip_sign { x: int } : x.sign.flip * ‖x‖ = -x := by cases x <;> rfl

def int.abs.sign_mul { s: int.Sign } { x: nat } : s ≠ int.Sign.zero ∨ x = .zero -> ‖s * x‖ = x := by
  intro c
  cases s <;> cases x
  any_goals rfl
  rename_i x
  cases c <;> contradiction

def int.abs.zero : ‖0: int‖ = 0 := rfl
def int.abs.one : ‖1: int‖ = 1 := rfl
def int.abs.neg_one : ‖-1: int‖ = 1 := rfl
def int.abs.pos_succ : ‖int.pos_succ a‖ = a.succ := rfl
def int.abs.neg_succ : ‖int.neg_succ a‖ = a.succ := rfl

def int.abs.of_nat (a: nat) : ‖int.of_nat a‖ = a := by
  cases a <;> rfl

def int.abs.neg_of_nat { a: nat } : ‖-int.of_nat a‖ = a := by
  cases a <;> rfl

def int.abs.neg { a: int } : ‖-a‖ = ‖a‖ := by cases a <;> rfl

def int.abs.of_nonneg (a: int) : 0 ≤ a -> ‖a‖ = a := by
  intro h
  cases a
  rfl
  rfl
  cases h <;> contradiction
