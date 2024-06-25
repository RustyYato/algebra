import Algebra.Int.Abs
import Algebra.Nat.Add
import Algebra.Nat.Sub
import Algebra.Nat.WellFounded

def int.inc (a: int): int := match a with
  | .zero => .pos_succ .zero
  | .pos_succ x => .pos_succ x.succ
  | .neg_succ .zero => .zero
  | .neg_succ (.succ x) => .neg_succ x

def int.dec (a: int): int := match a with
  | .zero => .neg_succ .zero
  | .neg_succ x => .neg_succ x.succ
  | .pos_succ .zero => .zero
  | .pos_succ (.succ x) => .pos_succ x

def int.add_nat (a: int) (b: nat) := match b with
   | .zero => a
   | .succ b => a.inc.add_nat b

def int.sub_nat (a: int) (b: nat) := match b with
   | .zero => a
   | .succ b => a.dec.sub_nat b

def int.add (a b: int): int :=
  match b with
  | .zero => a
  | .pos_succ b => a.inc.add_nat b
  | .neg_succ b => a.dec.sub_nat b

#print axioms int.add

instance int.add.inst : Add int := ⟨ int.add ⟩
instance int.sub.inst : Sub int where
  sub a b := a + (-b)

#print axioms int.add.inst

def int.add.def { a b: int } : a + b = int.add a b := rfl
def int.sub.def { a b: int } : a - b = a + (-b) := rfl

def int.add_zero { a: int } : a + 0 = a := by cases a <;> rfl

def int.inc.pos_succ : (int.pos_succ a).inc = int.pos_succ a.succ := rfl
def int.dec.neg_succ : (int.neg_succ a).dec = int.neg_succ a.succ := rfl

def int.inc.eq_add_one (a: int) : a.inc = a + 1 := rfl
def int.dec.eq_add_neg_one (a: int) : a.dec = a + -1 := rfl
def int.dec.eq_sub_one (a: int) : a.dec = a - 1 := rfl

def int.inc.neg { i: int } : -i.inc = (-i).dec := by
  cases i
  any_goals rfl
  rename_i i
  cases i <;> rfl

#print axioms int.inc.neg

def int.dec.neg { i: int } : -i.dec = (-i).inc := by
  cases i
  any_goals rfl
  rename_i i
  cases i <;> rfl

#print axioms int.dec.neg

def int.inc.zero : int.inc 0 = 1 := rfl
def int.dec.zero : int.dec 0 = -1 := rfl

def int.inc.neg_one : int.inc (-1) = 0 := rfl
def int.dec.one : int.dec 1 = 0 := rfl


def int.inc_dec_inv ( a: int ) : a.inc.dec = a := by
  cases a with
  | zero | pos_succ => rfl
  | neg_succ a => cases a <;> rfl

def int.dec_inc_inv ( a: int ) : a.dec.inc = a := by
  cases a with
  | zero | neg_succ => rfl
  | pos_succ a => cases a <;> rfl

def int.inc_dec_swap { a: int } : a.inc.dec = a.dec.inc := by rw [int.inc_dec_inv, int.dec_inc_inv a]

def int.add_nat.inc { x: int } { y: nat } : int.add_nat x.inc y = (int.add_nat x y).inc := by
  induction y generalizing x with
  | zero => rfl
  | succ y ih =>
    conv => {
      lhs
      unfold add_nat
    }
    rw [ih]
    congr 1

#print axioms int.add_nat.inc

def int.add_nat.dec { x: int } { y: nat } : int.add_nat x.dec y = (int.add_nat x y).dec := by
  cases y with
  | zero => rfl
  | succ y =>
    unfold add_nat
    rw [
    int.dec_inc_inv x,
    int.add_nat.inc,
    int.inc_dec_inv]

#print axioms int.add_nat.dec

def int.sub_nat.dec { x: int } { y: nat } : int.sub_nat x.dec y = (int.sub_nat x y).dec := by
  induction y generalizing x with
  | zero => rfl
  | succ y ih =>
    conv => {
      lhs
      unfold sub_nat
    }
    rw [ih]
    congr 1

#print axioms int.add_nat.inc

def int.sub_nat.inc { x: int } { y: nat } : int.sub_nat x.inc y = (int.sub_nat x y).inc := by
  cases y with
  | zero => rfl
  | succ y =>
    unfold sub_nat
    rw [
    int.inc_dec_inv x,
    int.sub_nat.dec,
    int.dec_inc_inv]

#print axioms int.sub_nat.inc

def int.pos_succ.def : int.pos_succ x = int.inc x := by cases x <;> rfl
def int.neg_succ.def : int.neg_succ x = int.dec (-x) := by cases x <;> rfl
def int.pos_succ.of_nat : nat.succ x = int.pos_succ x := by cases x <;> rfl
def int.pos_succ.succ : int.pos_succ (nat.succ x) = int.inc (int.pos_succ x) := by cases x <;> rfl
def int.neg_succ.succ : int.neg_succ (nat.succ x) = int.dec (int.neg_succ x) := by cases x <;> rfl
def int.inc.of_nat_succ : of_nat (nat.succ x) = int.inc (of_nat x) := by cases x <;> rfl

def int.add_nat.zero : int.add_nat 0 x = x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    unfold of_nat
    simp
    unfold add_nat
    rw [int.add_nat.inc, ih]
    clear ih
    cases x <;> rfl

#print axioms int.add_nat.zero

def int.add_nat.neg_one : int.add_nat (-1) x = int.dec x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    unfold of_nat
    rw [←neg_one_eq] at *
    unfold add_nat
    rw [add_nat.inc, ih]
    simp
    rw [←int.inc_dec_swap, ←pos_succ.def]

#print axioms int.add_nat.neg_one

def int.add_nat.one : int.add_nat 1 x = int.pos_succ x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [←one_eq] at *
    unfold add_nat
    rw [add_nat.inc, ih]
    rfl

#print axioms int.add_nat.one

def int.sub_nat.zero : int.sub_nat 0 x = -x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    unfold of_nat
    simp
    unfold sub_nat
    rw [int.sub_nat.dec, ih]
    clear ih
    cases x <;> rfl

#print axioms int.sub_nat.zero

def int.sub_nat.neg_one : int.sub_nat (-1) x = int.neg_succ x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [←neg_one_eq] at *
    unfold sub_nat
    rw [sub_nat.dec, ih]
    rfl

#print axioms int.sub_nat.neg_one

def int.sub_nat.one : int.sub_nat 1 x = int.inc (-x) := by
  induction x with
  | zero => rfl
  | succ x ih =>
    unfold of_nat
    rw [←one_eq] at *
    unfold sub_nat
    rw [sub_nat.dec, ih]
    rw [int.inc_dec_swap]
    rw [←neg_succ.def]
    rfl

#print axioms int.sub_nat.one

def int.zero_add { a: int } : 0 + a = a := by
  cases a
  rfl
  {
    rename_i b
    rw [int.add.def]
    unfold add
    simp only
    induction b with
    | zero => rfl
    | succ b ih =>
        unfold add_nat
        rw [←int.inc.pos_succ, add_nat.inc, ih]
  }
  {
    rename_i b
    rw [int.add.def]
    unfold add
    simp only
    induction b with
    | zero => rfl
    | succ b ih =>
        unfold sub_nat
        rw [←int.dec.neg_succ, sub_nat.dec, ih]
  }

#print axioms int.zero_add

def int.add.neg_one_right { a: int } : a + -1 = a.dec := by cases a <;> rfl
def int.add.one_right { a: int } : a + 1 = a.inc := by cases a <;> rfl

def int.add.inc_left { a b: int } : a.inc + b = (a + b).inc := by
  cases b with
  | zero => rfl
  | neg_succ b =>
    rw [add.def, add]
    simp only
    rw [sub_nat.dec, add.def, add]
    simp only
    rw [sub_nat.inc, sub_nat.dec, int.inc_dec_swap]
  | pos_succ b =>
    rw [add.def, add]
    simp only
    rw [add_nat.inc, add.def, add]

#print axioms int.add.inc_left

def int.add.dec_left { a b: int } : a.dec + b = (a + b).dec := by
  cases b with
  | zero => rfl
  | pos_succ b =>
    rw [add.def, add]
    simp only
    rw [add_nat.inc, add.def, add]
    simp only
    rw [add_nat.dec, add_nat.inc, int.inc_dec_swap]
  | neg_succ b =>
    rw [add.def, add]
    simp only
    rw [sub_nat.dec, add.def, add]

#print axioms int.add.dec_left

def int.add.inc_dec_right { a b: int } : a + b.inc = (a + b).inc ∧ a + b.dec = (a + b).dec := by
  cases b with
  | zero => apply And.intro <;> rfl
  | neg_succ b =>
    induction b generalizing a with
    | zero =>
      rw [neg_one_eq, neg_one_right, dec_inc_inv]
      apply And.intro <;> rfl
    | succ b ih =>
      apply And.intro
      rw [neg_succ.succ, ih.right, dec_inc_inv, dec_inc_inv]
      rw [neg_succ.succ, ih.right]
      rw [←neg_succ.succ, ←neg_succ.succ]
      rw [add.def, add.def]
      unfold add
      simp
      conv => {
        lhs
        unfold sub_nat
        unfold sub_nat
      }
      rw [sub_nat.dec]
      rw [sub_nat.dec]
  | pos_succ b =>
    induction b generalizing a with
    | zero =>
      rw [one_eq, one_right, inc_dec_inv]
      apply And.intro <;> rfl
    | succ b ih =>
      apply And.intro
      rw [pos_succ.succ, ih.left]
      rw [←pos_succ.succ, ←pos_succ.succ]
      rw [add.def, add.def]
      unfold add
      simp
      conv => {
        lhs
        unfold add_nat
        unfold add_nat
      }
      rw [add_nat.inc]
      rw [add_nat.inc]
      rw [pos_succ.succ, ih.left, inc_dec_inv, inc_dec_inv]

#print axioms int.add.inc_dec_right

def int.add.inc_right { a b: int } : a + b.inc = (a + b).inc := by
  apply int.add.inc_dec_right.left

#print axioms int.add.inc_right

def int.add.dec_right { a b: int } : a + b.dec = (a + b).dec := by
  apply int.add.inc_dec_right.right

#print axioms int.add.dec_right

def int.sub.inc_left { a b : int } : a.inc - b = (a - b).inc := by
  apply int.add.inc_left

#print axioms int.sub.inc_left

def int.sub.inc_right { a b : int } : a - b.inc = (a - b).dec := by
  rw [sub.def, inc.neg]
  apply int.add.dec_right

#print axioms int.sub.inc_left

def int.sub.dec_left { a b : int } : a.dec - b = (a - b).dec := by
  apply int.add.dec_left

#print axioms int.sub.dec_left

def int.sub.dec_right { a b : int } : a - b.dec = (a - b).inc := by
  rw [sub.def, dec.neg]
  apply int.add.inc_right

#print axioms int.sub.dec_right

def int.add_nat.comm_pos { a b: nat } : (int.pos_succ a).add_nat b = (int.pos_succ b).add_nat a := by
  induction b generalizing a with
  | zero =>
    rw [one_eq, add_nat.one]
    rfl
  | succ b ih =>
    conv => { lhs; unfold add_nat }
    rw [pos_succ.succ, add_nat.inc, ih, add_nat.inc]

#print axioms int.add_nat.comm_pos

def int.add_nat.comm_neg { a b: nat } : ((int.neg_succ a).add_nat b).inc = ((int.pos_succ b).sub_nat a).dec := by
  induction b generalizing a with
  | zero =>
    rw [one_eq, sub_nat.one, inc_dec_inv]
    unfold add_nat
    rw [neg_succ.def, dec_inc_inv]
  | succ b ih =>
    unfold add_nat
    rw [add_nat.inc, ih, dec_inc_inv, pos_succ.succ, sub_nat.inc, inc_dec_inv]

#print axioms int.add_nat.comm_neg

def int.sub_nat.comm_pos { a b: nat } : ((int.pos_succ a).sub_nat b).dec = ((int.neg_succ b).add_nat a).inc := by
  induction b generalizing a with
  | zero =>
    unfold sub_nat
    rw [←add_nat.inc]
    unfold int.inc
    rw [zero_eq, int.add_nat.zero, int.pos_succ.def, int.inc_dec_inv]
  | succ b ih =>
    unfold sub_nat
    rw [sub_nat.dec, ih, inc_dec_swap, ←add_nat.dec]
    rfl

#print axioms int.sub_nat.comm_pos

def int.sub_nat.comm_neg { a b: nat } : (int.neg_succ a).sub_nat b = (int.neg_succ b).sub_nat a := by
  induction b generalizing a with
  | zero =>
    rw [neg_one_eq, sub_nat.neg_one]
    rfl
  | succ b ih =>
    conv => { lhs; unfold sub_nat }
    rw [neg_succ.succ, sub_nat.dec, sub_nat.dec, ih]

#print axioms int.sub_nat.comm_neg

def int.add.comm { a b: int } : a + b = b + a := by
  cases a with
  | zero => rw [zero_eq, zero_add, add_zero]
  | pos_succ a =>
    cases b with
    | zero => rw [zero_eq, zero_add, add_zero]
    | pos_succ b =>
      rw [add.def, add.def]
      unfold add
      simp
      rw [add_nat.inc, add_nat.inc, int.add_nat.comm_pos]
    | neg_succ b =>
      rw [add.def, add.def]
      unfold add
      simp
      rw [add_nat.inc, sub_nat.dec, int.add_nat.comm_neg]
  | neg_succ a =>
    cases b with
    | zero => rw [zero_eq, zero_add, add_zero]
    | pos_succ b =>
      rw [add.def, add.def]
      unfold add
      simp
      rw [add_nat.inc, sub_nat.dec, int.sub_nat.comm_pos]
    | neg_succ b =>
      rw [add.def, add.def]
      unfold add
      simp
      rw [sub_nat.dec, sub_nat.dec, int.sub_nat.comm_neg]

#print axioms int.add.comm

def int.add.assoc { a b c: int } : (a + b) + c = a + (b + c) := by
  cases c with
  | zero => rfl
  | pos_succ c =>
    rw [@add.def _ (.pos_succ c)]
    rw [@add.def _ (.pos_succ c)]
    unfold add
    simp
    rw [add_nat.inc, add_nat.inc, add.inc_right]
    congr
    induction c generalizing a b with
    | zero => rfl
    | succ c ih =>
      unfold add_nat
      rw [add_nat.inc, add_nat.inc, ih, inc_right]
  | neg_succ c =>
    rw [@add.def _ (.neg_succ c)]
    rw [@add.def _ (.neg_succ c)]
    unfold add
    simp
    rw [sub_nat.dec, sub_nat.dec, add.dec_right]
    congr
    induction c generalizing a b with
    | zero => rfl
    | succ c ih =>
      unfold sub_nat
      rw [sub_nat.dec, sub_nat.dec, ih, dec_right]

#print axioms int.add.assoc

def int.add.neg_self { a: int } : a + -a = 0 := by
  cases a with
  | zero => rfl
  | pos_succ a =>
    rw [add.def]
    unfold add
    simp
    induction a with
    | zero => rfl
    | succ a ih =>
      rw [pos_succ.succ, inc_dec_inv, sub_nat]
      assumption
  | neg_succ a =>
    rw [add.def]
    unfold add
    simp
    induction a with
    | zero => rfl
    | succ a ih =>
      rw [neg_succ.succ, dec_inc_inv, add_nat]
      assumption

#print axioms int.add.neg_self

def int.sub.refl { a: int } : a - a = 0 := int.add.neg_self

#print axioms int.sub.refl

def int.add.zero_left { a: int } : 0 + a = a := by
  rw [add.def]
  cases a <;> (unfold add; simp)
  rfl
  rw [inc.zero, add_nat.one]
  rw [dec.zero, sub_nat.neg_one]

#print axioms int.add.zero_left

def int.add.zero_right { a: int } : a + 0 = a := rfl

#print axioms int.add.zero_right

def int.sub.zero_left { a: int } : 0 - a = -a := by
  rw [sub.def, add.zero_left]

def int.of_gt_zero { a: int } : 0 < a -> ∃x, a = int.pos_succ x := by
  intros
  cases a
  any_goals contradiction
  rename_i x _
  exists x

#print axioms int.of_gt_zero

def int.of_lt_zero { a: int } : 0 > a -> ∃x, a = int.neg_succ x := by
  intros
  cases a
  any_goals contradiction
  rename_i x _
  exists x

#print axioms int.of_lt_zero

def int.inc.compare { a b: int } : compare a.inc b.inc = compare a b := by
  cases a <;> cases b
  any_goals rfl
  any_goals simp
  any_goals (
    rename_i b
    cases b
    any_goals rfl)
  all_goals rename_i a b
  cases a <;> cases b
  any_goals rfl
  cases a <;> cases b
  any_goals rfl

#print axioms int.inc.compare

def int.dec.compare { a b: int } : compare a.dec b.dec = compare a b := by
  cases a <;> cases b
  any_goals rfl
  any_goals simp
  any_goals (
    rename_i b
    cases b
    any_goals rfl)
  all_goals rename_i a b
  cases a <;> cases b
  any_goals rfl
  cases a <;> cases b
  any_goals rfl

#print axioms int.dec.compare

def int.inc_dec_compare { a b: int } : compare a.inc b = compare a b.dec := by
  cases a <;> cases b
  any_goals rfl
  any_goals simp
  any_goals (
    rename_i b
    cases b
    any_goals rfl)
  all_goals rename_i a b
  cases a <;> cases b
  any_goals rfl
  cases a <;> cases b
  any_goals rfl

#print axioms int.inc_dec_compare

def int.dec_inc_compare { a b: int } : compare a.dec b = compare a b.inc := by
  cases a <;> cases b
  any_goals rfl
  any_goals simp
  any_goals (
    rename_i b
    cases b
    any_goals rfl)
  all_goals rename_i a b
  cases a <;> cases b
  any_goals rfl
  cases a <;> cases b
  any_goals rfl

#print axioms int.dec_inc_compare

def int.inc.cmp { a b: int } : cmp a.inc b.inc = cmp a b := by
  apply int.inc.compare

#print axioms int.inc.cmp

def int.dec.cmp { a b: int } : cmp a.dec b.dec = cmp a b := by
  apply int.dec.compare

#print axioms int.dec.cmp

def int.inc_dec_cmp { a b: int } : cmp a.inc b = cmp a b.dec := by
  apply int.inc_dec_compare

#print axioms int.inc_dec_cmp

def int.dec_inc_cmp { a b: int } : cmp a.dec b = cmp a b.inc := by
  apply int.dec_inc_compare

#print axioms int.dec_inc_cmp

def int.add.compare_swap { a b k: int } : compare (a + k) b = compare a (b - k) := by
  cases k with
  | zero => rw [zero_eq, add_zero]; rfl
  | pos_succ k =>
    induction k generalizing a b with
    | zero =>
      rw [one_eq, one_right, sub.def, neg_one_right]
      apply inc_dec_compare
    | succ k ih =>
      rw [pos_succ.succ, inc_right, ←inc_left, sub.def, inc.neg, dec_right, ←inc_dec_compare, ←sub.def]
      apply ih
  | neg_succ k =>
    induction k generalizing a b with
    | zero =>
      rw [neg_one_eq, neg_one_right, sub.def, neg_neg, one_right]
      apply dec_inc_compare
    | succ k ih =>
      rw [neg_succ.succ, dec_right, ←dec_left, sub.def, dec.neg, inc_right, ←dec_inc_compare, ←sub.def]
      apply ih

#print axioms int.add.compare_swap

def int.add.right_iff_sub { a b k: int }: a + k = b ↔ a = b - k := by
  apply Iff.intro
  intros h
  apply TotalOrder.eq_of_compare_eq
  rw [←int.add.compare_swap]
  cases h
  apply TotalOrder.compare_eq_refl
  intros h
  apply TotalOrder.eq_of_compare_eq
  rw [int.add.compare_swap]
  cases h
  apply TotalOrder.compare_eq_refl

#print axioms int.add.right_iff_sub

def int.add.left_iff_sub { a b k: int }: k + a = b ↔ a = b - k := by
  rw [add.comm]
  apply int.add.right_iff_sub

#print axioms int.add.left_iff_sub

def int.add.lt_right_iff_sub { a b k: int }: a + k < b ↔ a < b - k := by
  apply Iff.intro
  intros h
  rw [TotalOrder.unfold_lt]
  rw [←int.add.compare_swap]
  assumption
  intros h
  rw [TotalOrder.unfold_lt]
  rw [int.add.compare_swap]
  assumption

#print axioms int.add.lt_right_iff_sub

def int.add.lt_left_iff_sub { a b k: int }: k + a < b ↔ a < b - k := by
  rw [add.comm]
  apply int.add.lt_right_iff_sub

#print axioms int.add.lt_left_iff_sub

def int.add.le_right_iff_sub { a b k: int }: a + k ≤ b ↔ a ≤ b - k := by
  apply Iff.intro
  intros h
  rw [TotalOrder.unfold_le]
  rw [←int.add.compare_swap]
  assumption
  intros h
  rw [TotalOrder.unfold_le]
  rw [int.add.compare_swap]
  assumption

#print axioms int.add.lt_right_iff_sub

def int.add.le_left_iff_sub { a b k: int }: k + a ≤ b ↔ a ≤ b - k := by
  rw [add.comm]
  apply int.add.le_right_iff_sub

#print axioms int.add.le_left_iff_sub

def int.add.gt_right_iff_sub { a b k: int }: a + k > b ↔ a > b - k := by
  apply Iff.intro
  intros h
  apply TotalOrder.gt_of_compare
  rw [←int.add.compare_swap]
  apply TotalOrder.compare_of_gt
  assumption
  intros h
  apply TotalOrder.gt_of_compare
  rw [int.add.compare_swap]
  apply TotalOrder.compare_of_gt
  assumption

#print axioms int.add.gt_right_iff_sub

def int.add.gt_left_iff_sub { a b k: int }: k + a > b ↔ a > b - k := by
  rw [add.comm]
  apply int.add.gt_right_iff_sub

#print axioms int.add.gt_left_iff_sub

def int.add.ge_right_iff_sub { a b k: int }: a + k ≥ b ↔ a ≥ b - k := by
  apply Iff.intro
  intros h
  apply TotalOrder.ge_of_compare
  rw [←int.add.compare_swap]
  apply TotalOrder.compare_of_ge
  assumption
  intros h
  apply TotalOrder.ge_of_compare
  rw [int.add.compare_swap]
  apply TotalOrder.compare_of_ge
  assumption

#print axioms int.add.ge_right_iff_sub

def int.add.ge_left_iff_sub { a b k: int }: k + a ≥ b ↔ a ≥ b - k := by
  rw [add.comm]
  apply int.add.ge_right_iff_sub

#print axioms int.add.ge_left_iff_sub

def int.add.ne_right_iff_sub { a b k: int }: a + k ≠ b ↔ a ≠ b - k := by
  apply Iff.intro
  intros h
  apply TotalOrder.ne_of_compare
  rw [←int.add.compare_swap]
  apply TotalOrder.compare_of_ne
  assumption
  intros h
  apply TotalOrder.ne_of_compare
  rw [int.add.compare_swap]
  apply TotalOrder.compare_of_ne
  assumption

#print axioms int.add.ge_right_iff_sub

def int.add.ne_left_iff_sub { a b k: int }: k + a ≠ b ↔ a ≠ b - k := by
  rw [add.comm]
  apply int.add.ne_right_iff_sub

#print axioms int.add.ne_left_iff_sub

def int.add.lift_nat { a b: nat } : (of_nat (a + b)) = (of_nat a) + (of_nat b) := by
  induction b generalizing a with
  | zero =>
    conv => {
      rhs; rhs; unfold of_nat; simp
    }
    rw [nat.zero_eq, zero_eq, add.zero_right, nat.add_zero]
  | succ b ih =>
    rw [nat.add_succ, ←nat.succ_add, inc.of_nat_succ, inc_right, ←inc_left, ←inc.of_nat_succ]
    apply ih

#print axioms int.add.lift_nat

def int.sub.lift_nat { a b: nat } : b ≤ a -> (of_nat (a - b)) = (of_nat a) - (of_nat b) := by
  intro b_le_a
  induction b generalizing a with
  | zero =>
    conv => {
      rhs; rhs; unfold of_nat; simp
    }
    rfl
  | succ b ih =>
    cases a with
    | zero => cases nat.le_zero b_le_a
    | succ a =>
    rw [nat.succ_sub_succ]
    repeat rw [inc.of_nat_succ]
    rw [sub.def, inc.neg, add.dec_right, add.inc_left, inc_dec_inv, ←sub.def]
    apply ih b_le_a

#print axioms int.sub.lift_nat

def int.add_nat.neg { a: int } { b: nat }  : -int.add_nat a b = int.sub_nat (-a) b := by
  induction b generalizing a with
  | zero => rfl
  | succ b ih =>
    unfold add_nat sub_nat
    rw [add_nat.inc,  sub_nat.dec, int.inc.neg,ih]

#print axioms int.add_nat.neg

def int.sub_nat.neg { a: int } { b: nat }  : -int.sub_nat a b = int.add_nat (-a) b := by
  induction b generalizing a with
  | zero => rfl
  | succ b ih =>
    unfold add_nat sub_nat
    rw [add_nat.inc,  sub_nat.dec, int.dec.neg,ih]

#print axioms int.sub_nat.neg

def int.add.neg { a b: int } : -(a + b) = -a + -b := by
  cases b with
  | zero => rw [zero_eq, zero_right, neg.zero, zero_right]
  | pos_succ b =>
    rw [add.def]
    unfold add
    simp only
    rw [int.add_nat.neg, neg.pos_succ, add.def, inc.neg]
    rfl
  | neg_succ b =>
    rw [add.def]
    unfold add
    simp only
    rw [int.sub_nat.neg, neg.neg_succ, add.def, dec.neg]
    rfl

#print axioms int.add.neg

def int.add.sign_mul { s: int.Sign } { a b: nat } :  s * (a + b) = s * a + s * b := by
  cases a with
  | zero => rw [nat.zero_eq, nat.zero_add, int.Sign.int_zero_nat, zero_left]
  | succ a =>
    rw [nat.succ_add, ←nat.add_succ]
    cases s with
    | zero =>
      repeat rw [int.Sign.int_zero]
      rfl
    | pos =>
      repeat rw [int.Sign.int_pos]
      rw [←int.add.lift_nat]
      rw [nat.succ_add, nat.add_succ]
    | neg =>
      repeat rw [int.Sign.int_neg]
      apply int.neg.inj
      rw [int.add.neg]
      repeat rw [neg_neg]
      rw [←int.add.lift_nat]
      rw [nat.succ_add, nat.add_succ]

#print axioms int.add.sign_mul

def int.sub.sign_mul { s: int.Sign } { a b: nat } : b ≤ a -> s * (a - b) = s * a - s * b := by
  intro b_le_a
  induction a generalizing s b with
  | zero =>
    cases nat.le_zero b_le_a
    rw [nat.zero_eq, nat.sub_zero, int.Sign.int_zero_nat]
    rfl
  | succ a ih =>
    cases b with
    | zero => rw [nat.zero_eq, nat.sub_zero, int.Sign.int_zero_nat, sub.def, neg.zero, add.zero_right]
    | succ b =>
    have b_le_a : b ≤ a := b_le_a
    cases s with
    | zero =>
      repeat rw [int.Sign.int_zero]
      rfl
    | pos =>
      repeat rw [int.Sign.int_pos]
      apply sub.lift_nat
      assumption
    | neg =>
      repeat rw [int.Sign.int_neg]
      apply int.neg.inj
      rw [sub.def, int.add.neg]
      repeat rw [neg_neg]
      rw [←sub.def]
      apply int.sub.lift_nat
      assumption

#print axioms int.sub.sign_mul

def int.add.lift_pos_pos_to_nat { a b: nat } : (int.pos_succ a) + (int.pos_succ b) = int.pos_succ ((a + b).succ) := by
  rw [add.def]
  unfold add
  simp

  induction b generalizing a with
  | zero =>
    unfold add_nat
    rw [pos_succ.succ, nat.zero_eq, nat.add_zero]
  | succ b ih =>
    unfold add_nat
    rw [nat.add_succ, ←nat.succ_add]
    apply ih

#print axioms int.add.lift_pos_pos_to_nat

def int.add.lift_neg_neg_to_nat { a b: nat } : (int.neg_succ a) + (int.neg_succ b) = int.neg_succ ((a + b).succ) := by
  apply int.neg.inj
  rw [int.add.neg]
  apply int.add.lift_pos_pos_to_nat

#print axioms int.add.lift_neg_neg_to_nat

def int.add.lift_pos_neg_gt_to_nat { a b: nat } : a > b -> (int.pos_succ a) + (int.neg_succ b) = int.pos_succ (a - b.succ) := by
  intro a_gt_b

  rw [add.def]
  unfold add
  simp only

  induction b generalizing a with
  | zero =>
    unfold sub_nat
    match a with
    | .succ a =>
    rw [nat.zero_eq, nat.succ_sub_succ, nat.sub_zero, pos_succ.succ, inc_dec_inv]
  | succ b ih =>
    unfold sub_nat
    cases a with
    | zero => exact False.elim <| nat.not_lt_zero a_gt_b
    | succ a =>
    rw [nat.succ_sub_succ, pos_succ.succ, inc_dec_inv]
    apply ih
    apply nat.lt_of_succ_lt_succ
    exact a_gt_b

#print axioms int.add.lift_pos_neg_gt_to_nat

def int.add.lift_pos_neg_lt_to_nat { a b: nat } : a < b -> (int.pos_succ a) + (int.neg_succ b) = int.neg_succ (b - a.succ) := by
  intro a_lt_b

  rw [add.def]
  unfold add
  simp only

  induction b generalizing a with
  | zero =>
    exact False.elim <| nat.not_lt_zero a_lt_b
  | succ b ih =>
    unfold sub_nat
    cases a with
    | zero =>
      rw [nat.zero_eq, nat.succ_sub_succ, nat.sub_zero]
      unfold dec
      rw [←nat.zero_eq]
      simp
      rw [neg_one_eq, sub_nat.neg_one]
    | succ a =>
      rw [nat.succ_sub_succ, pos_succ.succ, inc_dec_inv]
      apply ih
      assumption

#print axioms int.add.lift_pos_neg_lt_to_nat

def int.add.lift_neg_pos_gt_to_nat { a b: nat } : a > b -> (int.neg_succ a) + (int.pos_succ b) = int.neg_succ (a - b.succ) := by
  intro a_gt_b
  rw [add.comm]
  apply int.add.lift_pos_neg_lt_to_nat
  assumption

#print axioms int.add.lift_neg_pos_gt_to_nat

def int.add.lift_neg_pos_lt_to_nat { a b: nat } : a < b -> (int.neg_succ a) + (int.pos_succ b) = int.pos_succ (b - a.succ) := by
  intro a_lt_b
  rw [add.comm]
  apply int.add.lift_pos_neg_gt_to_nat
  assumption

#print axioms int.add.lift_neg_pos_lt_to_nat

def int.induction
  (motive: int -> Prop)
  (if_zero: motive 0)
  (from_inc: ∀(x: int), motive (x.inc) -> motive x)
  (from_dec: ∀(x: int), motive (x.dec) -> motive x):
  ∀x, motive x := by
    intro x
    cases x with
    | zero => exact if_zero
    | pos_succ x =>
      apply from_dec
      cases x with
      | zero => exact if_zero
      | succ x =>
        rw [pos_succ.succ, inc_dec_inv]
        apply int.induction <;> assumption
    | neg_succ x =>
      apply from_inc
      cases x with
      | zero => exact if_zero
      | succ x =>
        rw [neg_succ.succ, dec_inc_inv]
        apply int.induction <;> assumption
termination_by x => int.abs x
decreasing_by
  apply nat.lt_succ_self
  apply nat.lt_succ_self

#print axioms int.induction

def int.inc.inj (a b: int) : a.inc = b.inc -> a = b := by
  intro a_eq_b
  rw [int.inc.eq_add_one, int.inc.eq_add_one] at a_eq_b
  have : (a + 1) - 1 = (a + 1) - 1 := rfl
  conv at this => {
    conv => {
      rhs
      rw [a_eq_b]
    }
    rw [int.sub.def, int.sub.def,  int.add.assoc, int.add.assoc, int.add.neg_self, int.add_zero, int.add_zero]
  }
  assumption

#print axioms int.inc.inj

def int.dec.inj (a b: int) : a.dec = b.dec -> a = b := by
  intro a_eq_b
  rw [int.dec.eq_sub_one, int.dec.eq_sub_one] at a_eq_b
  have : (a - 1) + 1 = (a - 1) + 1 := rfl
  conv at this => {
    conv => {
      rhs
      rw [a_eq_b]
    }
    rw [int.sub.def, int.sub.def,  int.add.assoc, int.add.assoc, @int.add.comm _ 1, int.add.neg_self, int.add_zero, int.add_zero]
  }
  assumption

#print axioms int.dec.inj
