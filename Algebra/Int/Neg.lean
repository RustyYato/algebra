import Algebra.Int.Cmp

def int.neg (i: int): int := match i with
  | .zero => .zero
  | .pos_succ n => .neg_succ n
  | .neg_succ n => .pos_succ n

instance int.instNeg : Neg int where
  neg := int.neg

def int.neg_neg : ∀i: int, - -i = i := by intro i; cases i <;> rfl

def int.neg_one_eq : int.neg_succ .zero = -1 := rfl
def int.Sign.int_neg { x: nat } :  Sign.neg * x = -(x: int) := by cases x <;> rfl

def int.neg.inj: ∀{ a b: int }, -a = -b -> a = b := by
  intros a b
  cases a <;> cases b
  any_goals exact id
  any_goals intro; contradiction
  intro h
  rw [int.neg_succ.inj h]
  intro h
  rw [int.pos_succ.inj h]

def int.neg.swap_lt: ∀{ a b: int }, a < b ↔ -b < -a := by
  suffices ∀{a b: int}, a < b -> -b < -a by
    intro a b
    apply Iff.intro this
    intro h
    have := this h
    rw [neg_neg, neg_neg] at this
    exact this
  intros a b
  intro a_lt_b
  induction a_lt_b
  exact .neg_pos
  exact .neg_zero
  exact .zero_pos
  apply int.LT.pos
  assumption
  apply int.LT.neg
  assumption

def int.neg.swap_le: ∀{ a b: int }, a ≤ b ↔ -b ≤ -a := by
  suffices ∀{a b: int}, a ≤ b -> -b ≤ -a by
    intro a b
    apply Iff.intro this
    intro h
    have := this h
    rw [neg_neg, neg_neg] at this
    exact this
  intros a b
  intro a_lt_b
  induction a_lt_b
  exact .neg_pos
  exact .neg_zero
  exact .zero_pos
  exact .zero
  apply int.LE.pos
  assumption
  apply int.LE.neg
  assumption

def int.neg.swap_gt: ∀{ a b: int }, a > b ↔ -b > -a := by
  intros
  apply int.neg.swap_lt

def int.neg.swap_ge: ∀{ a b: int }, a ≥ b ↔ -b ≥ -a := by
  intros
  apply int.neg.swap_le

def int.neg.def (a: int) : -a = a.neg := rfl
def int.neg.zero : -(0: int) = 0 := rfl
def int.neg.pos_succ : -int.pos_succ n = int.neg_succ n := rfl
def int.neg.neg_succ : -int.neg_succ n = int.pos_succ n := rfl

def int.neg.sign_mul { s: int.Sign } { x: nat } : -(s * x) = s.flip * x := by
  cases s with
  | zero => rfl
  | pos | neg =>
    cases x <;> rfl
