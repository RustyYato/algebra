import Algebra.Nat.Div

def nat.ofBool : Bool -> nat
| false => 0
| true => 1

def nat.bitwise_rec
  { motive: nat -> nat -> Sort _ }
  (left_zero: ∀b, motive 0 b)
  (right_zero: ∀a > 0, motive a 0)
  (pos: ∀a b, 0 < a -> 0 < b -> motive (a / 2) (b / 2) -> motive a b):
  ∀a b, motive a b
| .zero, b => left_zero b
| .succ a, .zero => right_zero a.succ nat.zero_lt_succ
| .succ a, .succ b => pos a.succ b.succ nat.zero_lt_succ nat.zero_lt_succ (nat.bitwise_rec left_zero right_zero pos (a.succ / 2) (b.succ / 2))
termination_by a => a
decreasing_by
  exact div.lt a.succ 2 (by decide) nat.zero_lt_succ

def nat.bits_rec
  { motive: nat -> Sort _ }
  (zero: motive 0)
  (pos: ∀a > 0, motive (a / 2) ->  motive a):
  ∀a, motive a
| .zero => zero
| .succ a => pos a.succ nat.zero_lt_succ (nat.bits_rec zero pos (a.succ / 2))
termination_by a => a
decreasing_by
  exact div.lt a.succ 2 (by decide) nat.zero_lt_succ

def nat.msb_pos : nat -> nat := nat.bits_rec (motive := fun _ => nat) 0 (fun _ _ ih => ih.succ)
def nat.counts_ones : nat -> nat := nat.bits_rec (motive := fun _ => nat) 0 (fun a _ ih => ih + a % 2)

def nat.bitwise (f: Bool -> Bool -> Bool) : nat -> nat -> nat :=
  nat.bitwise_rec
  (fun b =>
    match f false true with
    | false => 0
    | true => b)
  (fun a _ =>
  match f true false with
  | false => 0
  | true => a)
  (fun a b _ _ ih => 2 * ih + nat.ofBool (f (a % 2 = 1) (b % 2 = 1)))
#print Nat.bitwise._unary

def nat.zero_bitwise (f: Bool -> Bool -> Bool) :
  nat.bitwise f 0 b = if f false true then b else 0 := by
  unfold bitwise bitwise_rec
  split
  split
  rw [if_neg]
  apply Bool.eq_false_iff.mp
  assumption
  rw [if_pos]
  assumption
  contradiction
  contradiction

def nat.bitwise_zero (f: Bool -> Bool -> Bool) :
  nat.bitwise f a 0 = if f true false then a else 0 := by
  unfold bitwise bitwise_rec
  split
  split <;> split <;> rfl
  split
  rw [if_neg]
  apply Bool.eq_false_iff.mp
  assumption
  rw [if_pos]
  assumption
  contradiction

def nat.bitwise_pos (f: Bool -> Bool -> Bool) (a b: nat) :
  0 < a -> 0 < b ->
  nat.bitwise f a b = 2 * (nat.bitwise f (a / 2) (b / 2)) + nat.ofBool (f (a % 2 = 1) (b % 2 = 1)) := by
  intro a_pos b_pos
  conv => { lhs; rw [bitwise] }
  unfold bitwise_rec
  split
  any_goals contradiction
  rfl

abbrev nat.and := nat.bitwise Bool.and
abbrev nat.or := nat.bitwise Bool.or
abbrev nat.xor := nat.bitwise Bool.xor
