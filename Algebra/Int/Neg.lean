import Algebra.Int.Cmp

def int.neg (i: int): int := match i with
  | .zero => .zero
  | .pos_succ n => .neg_succ n
  | .neg_succ n => .pos_succ n

#print axioms int.neg

instance int.instNeg : Neg int where
  neg := int.neg

def int.neg_neg : ∀i: int, - -i = i := by intro i; cases i <;> rfl

#print axioms int.neg_neg

def int.neg_one_eq : int.neg_succ .zero = -1 := rfl
#print axioms int.neg_one_eq

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

#print axioms int.neg.inj

def int.neg.swap_cmp : ∀{ a b: int }, compare (-b) (-a) = compare a b := by
  intro a b
  cases a <;> cases b
  any_goals apply TotalOrder.compare_antisymm
  repeat rfl

#print axioms int.neg.swap_cmp

def int.neg.swap_lt: ∀{ a b: int }, a < b ↔ -b < -a := by
  intros a b
  apply Iff.intro
  intro a_lt_b
  rw [TotalOrder.unfold_lt]
  rw [int.neg.swap_cmp]
  assumption
  intro a_lt_b
  rw [TotalOrder.unfold_lt] at a_lt_b
  rw [int.neg.swap_cmp] at a_lt_b
  assumption

#print axioms int.neg.swap_lt

def int.neg.swap_le: ∀{ a b: int }, a ≤ b ↔ -b ≤ -a := by
  intros a b
  apply Iff.intro
  intro a_le_b
  rw [TotalOrder.unfold_le]
  rw [int.neg.swap_cmp]
  assumption
  intro a_le_b
  rw [TotalOrder.unfold_le] at a_le_b
  rw [int.neg.swap_cmp] at a_le_b
  assumption

#print axioms int.neg.swap_le

def int.neg.swap_gt: ∀{ a b: int }, a > b ↔ -b > -a := by
  intros
  apply int.neg.swap_lt

#print axioms int.neg.swap_gt

def int.neg.swap_ge: ∀{ a b: int }, a ≥ b ↔ -b ≥ -a := by
  intros
  apply int.neg.swap_le

#print axioms int.neg.swap_ge

def int.neg.def (a: int) : -a = a.neg := rfl
def int.neg.zero : -(0: int) = 0 := rfl
def int.neg.pos_succ : -int.pos_succ n = int.neg_succ n := rfl
def int.neg.neg_succ : -int.neg_succ n = int.pos_succ n := rfl

def int.neg.sign_mul { s: int.Sign } { x: nat } : -(s * x) = s.flip * x := by
  cases s with
  | zero => rfl
  | pos | neg =>
    cases x <;> rfl

#print axioms int.neg.sign_mul
