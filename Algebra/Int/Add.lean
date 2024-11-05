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

instance int.add.inst : Add int := ⟨ int.add ⟩
instance int.sub.inst : Sub int where
  sub a b := a + (-b)

def int.add.def { a b: int } : a + b = int.add a b := rfl
def int.sub.def { a b: int } : a - b = a + (-b) := rfl

def int.add_zero { a: int } : a + 0 = a := by cases a <;> rfl
def int.sub_zero { a: int } : a - 0 = a := by cases a <;> rfl

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

def int.dec.neg { i: int } : -i.dec = (-i).inc := by
  cases i
  any_goals rfl
  rename_i i
  cases i <;> rfl

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

def int.add_nat.dec { x: int } { y: nat } : int.add_nat x.dec y = (int.add_nat x y).dec := by
  cases y with
  | zero => rfl
  | succ y =>
    unfold add_nat
    rw [
    int.dec_inc_inv x,
    int.add_nat.inc,
    int.inc_dec_inv]

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

def int.sub_nat.inc { x: int } { y: nat } : int.sub_nat x.inc y = (int.sub_nat x y).inc := by
  cases y with
  | zero => rfl
  | succ y =>
    unfold sub_nat
    rw [
    int.inc_dec_inv x,
    int.sub_nat.dec,
    int.dec_inc_inv]

def int.pos_succ.def : int.pos_succ x = int.inc x := by cases x <;> rfl
def int.neg_succ.def : int.neg_succ x = int.dec (-x) := by cases x <;> rfl
def int.pos_succ.of_nat : nat.succ x = int.pos_succ x := by cases x <;> rfl
def int.pos_succ.succ : int.pos_succ (nat.succ x) = int.inc (int.pos_succ x) := by cases x <;> rfl
def int.neg_succ.succ : int.neg_succ (nat.succ x) = int.dec (int.neg_succ x) := by cases x <;> rfl
def int.inc.of_nat_succ : of_nat (nat.succ x) = int.inc (of_nat x) := by cases x <;> rfl

def int.strong_induction
  (motive: int -> Prop)
  (zero: motive 0)
  (inc: ∀(x: int), motive x -> motive x.inc)
  (dec: ∀(x: int), motive x -> motive x.dec):
  ∀x, motive x := by
    intro x
    cases x with
    | zero => exact zero
    | pos_succ x =>
      induction x with
      | zero =>
        rw [int.one_eq, ←int.inc.zero]
        apply inc
        exact zero
      | succ x ih =>
        have : pos_succ x.succ = (pos_succ x).inc := rfl
        rw [this]
        apply inc
        apply ih
    | neg_succ x =>
      induction x with
      | zero =>
        rw [int.neg_one_eq, ←int.dec.zero]
        apply dec
        exact zero
      | succ x ih =>
        have : neg_succ x.succ = (neg_succ x).dec := rfl
        rw [this]
        apply dec
        apply ih

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

def int.add_nat.one : int.add_nat 1 x = int.pos_succ x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [←one_eq] at *
    unfold add_nat
    rw [add_nat.inc, ih]
    rfl

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

def int.sub_nat.neg_one : int.sub_nat (-1) x = int.neg_succ x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [←neg_one_eq] at *
    unfold sub_nat
    rw [sub_nat.dec, ih]
    rfl

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

def int.add.neg_one_right { a: int } : a + -1 = a.dec := by cases a <;> rfl
def int.add.one_right { a: int } : a + 1 = a.inc := by cases a <;> rfl

def int.inc_add { a b: int } : a.inc + b = (a + b).inc := by
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

def int.dec_add { a b: int } : a.dec + b = (a + b).dec := by
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

def int.add.inc_add_dec { a b: int } : a + b.inc = (a + b).inc ∧ a + b.dec = (a + b).dec := by
  induction a using strong_induction generalizing b with
  | zero =>
    rw [zero_add, zero_add, zero_add]
    trivial
  | inc a ih =>
    repeat rw [inc_add]
    rw [ih.left, ih.right]
    rw [dec_inc_inv, inc_dec_inv]
    trivial
  | dec a ih =>
    repeat rw [dec_add]
    rw [ih.left, ih.right]
    rw [dec_inc_inv, inc_dec_inv]
    trivial

def int.add_inc { a b: int } : a + b.inc = (a + b).inc := by
  apply int.add.inc_add_dec.left

def int.add_dec { a b: int } : a + b.dec = (a + b).dec := by
  apply int.add.inc_add_dec.right

def int.inc_sub { a b : int } : a.inc - b = (a - b).inc := by
  apply int.inc_add

def int.sub_inc { a b : int } : a - b.inc = (a - b).dec := by
  rw [sub.def, inc.neg]
  apply int.add_dec

def int.dec_sub { a b : int } : a.dec - b = (a - b).dec := by
  apply int.dec_add

def int.sub_dec { a b : int } : a - b.dec = (a - b).inc := by
  rw [sub.def, dec.neg]
  apply int.add_inc

def int.sub.inc { a b : int } : a.inc - b.inc = a - b := by
  rw [inc_sub, sub_inc, dec_inc_inv]

def int.sub.dec { a b : int } : a.dec - b.dec = a - b := by
  rw [dec_sub, sub_dec, inc_dec_inv]

def int.add_nat.pos_succ { a b: nat } : (int.pos_succ a).add_nat b = int.pos_succ (a + b) := by
  induction b generalizing a with
  | zero => erw [nat.zero_eq, nat.add_zero]; rfl
  | succ b ih =>
    unfold add_nat
    rw [add_nat.inc, ih, int.inc.pos_succ, nat.add_succ]

def int.add_nat.comm_pos { a b: nat } : (int.pos_succ a).add_nat b = (int.pos_succ b).add_nat a := by
  induction b generalizing a with
  | zero =>
    rw [one_eq, add_nat.one]
    rfl
  | succ b ih =>
    conv => { lhs; unfold add_nat }
    rw [pos_succ.succ, add_nat.inc, ih, add_nat.inc]

def int.add_nat.comm_neg { a b: nat } : ((int.neg_succ a).add_nat b).inc = ((int.pos_succ b).sub_nat a).dec := by
  induction b generalizing a with
  | zero =>
    rw [one_eq, sub_nat.one, inc_dec_inv]
    unfold add_nat
    rw [neg_succ.def, dec_inc_inv]
  | succ b ih =>
    unfold add_nat
    rw [add_nat.inc, ih, dec_inc_inv, pos_succ.succ, sub_nat.inc, inc_dec_inv]

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

def int.sub_nat.comm_neg { a b: nat } : (int.neg_succ a).sub_nat b = (int.neg_succ b).sub_nat a := by
  induction b generalizing a with
  | zero =>
    rw [neg_one_eq, sub_nat.neg_one]
    rfl
  | succ b ih =>
    conv => { lhs; unfold sub_nat }
    rw [neg_succ.succ, sub_nat.dec, sub_nat.dec, ih]

def int.add.comm (a b: int) : a + b = b + a := by
  induction a using strong_induction with
  | zero => rw [zero_add, add_zero]
  | inc a ih => rw [inc_add, add_inc, ih]
  | dec a ih => rw [dec_add, add_dec, ih]

def int.add.assoc (a b c: int) : (a + b) + c = a + (b + c) := by
  induction a using strong_induction with
  | zero => rw [zero_add, zero_add]
  | inc a ih =>
    repeat rw [inc_add]
    rw [ih]
  | dec a ih =>
    repeat rw [dec_add]
    rw [ih]

def int.add.right_comm (a b c: int) :
  a + b + c = a + c + b := by rw [int.add.assoc, int.add.comm b, int.add.assoc]

def int.add.left_comm (a b c: int) :
  a + b + c = c + b + a := by rw [int.add.comm _ c, int.add.comm a, int.add.assoc]

def int.add.comm_left (a b c: int) :
  a + (b + c) = b + (a + c) := by
  rw [←int.add.assoc, ←int.add.assoc, int.add.comm a]

def int.add.comm_right (a b c: int) :
  a + (b + c) = c + (b + a) := by
  rw [int.add.comm _ c, int.add.comm a, int.add.assoc]

def int.add.neg_self { a: int } : a + -a = 0 := by
  induction a using strong_induction with
  | zero => rw [zero_add, neg.zero]
  | inc a ih => rw [inc_add, inc.neg, add_dec, dec_inc_inv, ih]
  | dec a ih => rw [dec_add, dec.neg, add_inc, inc_dec_inv, ih]

def int.sub.self { a: int } : a - a = 0 := int.add.neg_self

def int.add.zero_left { a: int } : 0 + a = a := by
  rw [add.def]
  cases a <;> (unfold add; simp)
  rfl
  rw [inc.zero, add_nat.one]
  rw [dec.zero, sub_nat.neg_one]

def int.add.zero_right { a: int } : a + 0 = a := rfl

def int.sub.zero_left { a: int } : 0 - a = -a := by
  rw [sub.def, add.zero_left]

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

def int.inc_eq_iff_eq_dec {a b: int} : a.inc = b ↔ a = b.dec := by
  apply Iff.intro
  intro h
  apply inc.inj
  rw [h, dec_inc_inv]
  intro h
  apply inc.inj
  rw [h, dec_inc_inv]

def int.eq_inc_iff_dec_eq {a b: int} : a = b.inc ↔ a.dec = b := by
  apply Iff.trans
  apply Iff.intro Eq.symm Eq.symm
  apply flip Iff.trans
  apply Iff.intro Eq.symm Eq.symm
  apply int.inc_eq_iff_eq_dec

def int.inc_dec_le' : ∀{a b: int}, a ≤ b -> a.inc ≤ b.inc ∧ a.dec ≤ b.dec := by
  intro a b h
  cases h with
  | neg_pos =>
    rename_i a b
    cases a
    apply And.intro
    exact .zero_pos
    cases b
    exact .neg_zero
    exact .neg_pos
    apply And.intro
    exact .neg_pos
    cases b
    exact .neg_zero
    exact .neg_pos
  | zero_pos =>
    rename_i b
    apply And.intro
    exact .pos (nat.zero_le _)
    cases b
    exact .neg_zero
    exact .neg_pos
  | neg_zero =>
    rename_i a
    apply And.intro
    cases a
    exact .zero_pos
    exact .neg_pos
    exact .neg (nat.zero_le _)
  | zero => apply And.intro <;> rfl
  | pos =>
    apply And.intro
    apply int.LE.pos
    apply nat.succ_le_succ
    assumption
    rename_i a b h
    cases h
    cases b
    rfl
    exact .zero_pos
    rename_i h
    exact .pos h
  | neg =>
    apply And.intro
    rename_i a b h
    cases h
    cases b
    rfl
    exact .neg_zero
    rename_i h
    exact .neg h
    apply int.LE.neg
    apply nat.succ_le_succ
    assumption

def int.inc.le : ∀{a b: int}, a ≤ b ↔ a.inc ≤ b.inc := by
  intro a b
  apply Iff.intro
  intro h
  exact (inc_dec_le' h).left
  intro h
  have := (inc_dec_le' h).right
  rw [inc_dec_inv, inc_dec_inv] at this
  exact this

def int.dec.le : ∀{a b: int}, a ≤ b ↔ a.dec ≤ b.dec := by
  intro a b
  apply Iff.intro
  intro h
  exact (inc_dec_le' h).right
  intro h
  have := (inc_dec_le' h).left
  rw [dec_inc_inv, dec_inc_inv] at this
  exact this

def int.inc_le_iff_le_dec : ∀{a b: int}, a.inc ≤ b ↔ a ≤ b.dec := by
  intro a b
  apply Iff.intro
  intro h
  have := dec.le.mp h
  rw [inc_dec_inv] at this
  exact this
  intro h
  have := inc.le.mp h
  rw [dec_inc_inv] at this
  exact this

def int.le_inc_iff_dec_le : ∀{a b: int}, a ≤ b.inc ↔ a.dec ≤ b := by
  intro a b
  apply Iff.intro
  intro h
  have := dec.le.mp h
  rw [inc_dec_inv] at this
  exact this
  intro h
  have := inc.le.mp h
  rw [dec_inc_inv] at this
  exact this

def int.lt_inc_of_le {a b: int} : a ≤ b -> a < b.inc := by
  intro h
  cases h
  exact .neg_pos
  exact .zero_pos
  exact .neg_pos
  exact .zero_pos
  rename_i a b h
  cases a
  exact .neg_zero
  exact .neg (nat.lt_of_succ_le h)
  rename_i h
  exact .pos (nat.lt_of_succ_le (nat.succ_le_succ h))

def int.lt_of_inc_le {a b: int} : a.inc ≤ b -> a < b := by
  intro h
  have := lt_inc_of_le (dec.le.mp h)
  rw [inc_dec_inv, dec_inc_inv] at this
  exact this

def int.inc_le_of_lt {a b: int} : a < b -> a.inc ≤ b := by
  intro h
  cases h
  rename_i a _
  cases a
  exact .zero_pos
  exact .neg_pos
  exact .pos (nat.zero_le _)
  rename_i a
  cases a
  rfl
  exact .neg_zero
  rename_i h
  cases h
  exact .neg (nat.zero_le _)
  rename_i h
  exact .neg (nat.succ_le_of_lt h)
  rename_i h
  exact .pos (nat.succ_le_of_lt h)

def int.le_of_lt_inc {a b: int} : a < b.inc -> a ≤ b := by
  intro h
  apply inc.le.mpr
  exact inc_le_of_lt h

def int.lt_inc_iff_le {a b: int} : a < b.inc ↔ a ≤ b := ⟨le_of_lt_inc,lt_inc_of_le⟩

def int.inc_le_iff_lt {a b: int} : a.inc ≤ b ↔ a < b := ⟨lt_of_inc_le,inc_le_of_lt⟩

def int.inc.lt : ∀{a b: int}, a < b ↔ a.inc < b.inc := by
  intro a b
  apply Iff.trans int.inc_le_iff_lt.symm
  apply Iff.trans _ int.inc_le_iff_lt
  exact le

def int.dec.lt : ∀{a b: int}, a < b ↔ a.dec < b.dec := by
  intro a b
  apply Iff.trans int.inc_le_iff_lt.symm
  apply Iff.trans _ int.inc_le_iff_lt
  rw [dec_inc_inv]
  exact inc_le_iff_le_dec

def int.inc_lt_iff_lt_dec : ∀{a b: int}, a.inc < b ↔ a < b.dec := by
  intro a b
  apply Iff.intro
  intro h
  have := dec.lt.mp h
  rw [inc_dec_inv] at this
  exact this
  intro h
  have := inc.lt.mp h
  rw [dec_inc_inv] at this
  exact this

def int.lt_inc_iff_dec_lt : ∀{a b: int}, a < b.inc ↔ a.dec < b := by
  intro a b
  apply Iff.intro
  intro h
  have := dec.lt.mp h
  rw [inc_dec_inv] at this
  exact this
  intro h
  have := inc.lt.mp h
  rw [dec_inc_inv] at this
  exact this

def int.dec_lt_iff_lt_inc : ∀{a b: int}, a.dec < b ↔ a < b.inc := lt_inc_iff_dec_lt.symm

def int.lt_dec_iff_inc_lt : ∀{a b: int}, a < b.dec ↔ a.inc < b := inc_lt_iff_lt_dec.symm

def int.add.le_left {a b k: int} : a ≤ b ↔ a + k ≤ b + k := by
  induction k using strong_induction generalizing a b with
  | zero => rw [add_zero, add_zero]
  | inc k ih =>
    rw [add_inc, add_inc]
    exact Iff.trans ih inc.le
  | dec k ih =>
    rw [add_dec, add_dec]
    exact Iff.trans ih dec.le

def int.add.lt_left {a b k: int} : a < b ↔ a + k < b + k := by
  induction k using strong_induction generalizing a b with
  | zero => rw [add_zero, add_zero]
  | inc k ih =>
    rw [add_inc, add_inc]
    exact Iff.trans ih inc.lt
  | dec k ih =>
    rw [add_dec, add_dec]
    exact Iff.trans ih dec.lt

def int.add.le_right {a b k: int} : a ≤ b ↔ k + a ≤ k + b := by
  rw [add.comm k, add.comm k]
  apply int.add.le_left

def int.add.lt_right {a b k: int} : a < b ↔ k + a < k + b := by
  rw [add.comm k, add.comm k]
  apply int.add.lt_left

def int.add_le_iff_le_sub {a b k: int} : a + k ≤ b ↔ a ≤ b - k := by
  induction k using strong_induction generalizing a b with
  | zero => rw [add_zero, sub_zero]
  | inc k ih =>
    rw [add_inc, sub_inc, ←dec_sub]
    apply Iff.trans inc_le_iff_le_dec ih
  | dec k ih =>
    rw [add_dec, sub_dec, ←inc_sub]
    apply Iff.trans le_inc_iff_dec_le.symm ih

def int.le_add_iff_sub_le {a b k: int} : a ≤ b + k ↔ a - k ≤ b := by
  induction k using strong_induction generalizing a b with
  | zero => rw [add_zero, sub_zero]
  | inc k ih =>
    rw [add_inc, sub_inc, ←dec_sub]
    apply Iff.trans le_inc_iff_dec_le ih
  | dec k ih =>
    rw [add_dec, sub_dec, ←inc_sub]
    apply Iff.trans inc_le_iff_le_dec.symm ih

def int.add_lt_iff_lt_sub {a b k: int} : a + k < b ↔ a < b - k := by
  induction k using strong_induction generalizing a b with
  | zero => rw [add_zero, sub_zero]
  | inc k ih =>
    rw [add_inc, sub_inc, ←dec_sub]
    apply Iff.trans inc_lt_iff_lt_dec ih
  | dec k ih =>
    rw [add_dec, sub_dec, ←inc_sub]
    apply Iff.trans lt_inc_iff_dec_lt.symm ih

def int.lt_add_iff_sub_lt {a b k: int} : a < b + k ↔ a - k < b := by
  induction k using strong_induction generalizing a b with
  | zero => rw [add_zero, sub_zero]
  | inc k ih =>
    rw [add_inc, sub_inc, ←dec_sub]
    apply Iff.trans lt_inc_iff_dec_lt ih
  | dec k ih =>
    rw [add_dec, sub_dec, ←inc_sub]
    apply Iff.trans inc_lt_iff_lt_dec.symm ih

def int.add.lift_nat { a b: nat } : (of_nat (a + b)) = (of_nat a) + (of_nat b) := by
  induction b generalizing a with
  | zero =>
    conv => {
      rhs; rhs; unfold of_nat; simp
    }
    rw [nat.zero_eq, zero_eq, add.zero_right, nat.add_zero]
  | succ b ih =>
    rw [nat.add_succ, ←nat.succ_add, inc.of_nat_succ, add_inc, ←inc_add, ←inc.of_nat_succ]
    apply ih

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
    rw [sub.def, inc.neg, add_dec, inc_add, inc_dec_inv, ←sub.def]
    apply ih (nat.le_of_succ_le_succ b_le_a)

def int.add_nat.neg { a: int } { b: nat }  : -int.add_nat a b = int.sub_nat (-a) b := by
  induction b generalizing a with
  | zero => rfl
  | succ b ih =>
    unfold add_nat sub_nat
    rw [add_nat.inc,  sub_nat.dec, int.inc.neg,ih]

def int.sub_nat.neg { a: int } { b: nat }  : -int.sub_nat a b = int.add_nat (-a) b := by
  induction b generalizing a with
  | zero => rfl
  | succ b ih =>
    unfold add_nat sub_nat
    rw [add_nat.inc,  sub_nat.dec, int.dec.neg,ih]

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

def int.sub.neg { a b: int } : -(a - b) = b - a := by
  rw [sub.def, sub.def, add.neg, neg_neg, add.comm]

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

def int.sub.sign_mul { s: int.Sign } { a b: nat } : b ≤ a -> s * (a - b) = s * a - s * b := by
  intro b_le_a
  cases a with
  | zero =>
    cases nat.le_zero b_le_a
    rw [nat.zero_eq, nat.sub_zero, int.Sign.int_zero_nat]
    rfl
  | succ a =>
    cases b with
    | zero => rw [nat.zero_eq, nat.sub_zero, int.Sign.int_zero_nat, sub.def, neg.zero, add.zero_right]
    | succ b =>
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

def int.add.lift_neg_neg_to_nat { a b: nat } : (int.neg_succ a) + (int.neg_succ b) = int.neg_succ ((a + b).succ) := by
  apply int.neg.inj
  rw [int.add.neg]
  apply int.add.lift_pos_pos_to_nat

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
      apply nat.lt_of_succ_lt_succ
      assumption

def int.add.lift_neg_pos_gt_to_nat { a b: nat } : a > b -> (int.neg_succ a) + (int.pos_succ b) = int.neg_succ (a - b.succ) := by
  intro a_gt_b
  rw [add.comm]
  apply int.add.lift_pos_neg_lt_to_nat
  assumption

def int.add.lift_neg_pos_lt_to_nat { a b: nat } : a < b -> (int.neg_succ a) + (int.pos_succ b) = int.pos_succ (b - a.succ) := by
  intro a_lt_b
  rw [add.comm]
  apply int.add.lift_pos_neg_gt_to_nat
  assumption

def int.add.le {a b c d: int}: a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro ac bd
  apply le_trans
  apply int.add.le_left.mp
  assumption
  apply int.add.le_right.mp
  assumption

def int.add.lt {a b c d: int}: a < c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply int.add.lt_left.mp
  assumption
  apply int.add.lt_right.mp
  assumption

def int.add_lt_of_lt_of_le { a b c d: int } : a < b -> c ≤ d -> (a + c) < (b + d) := by
  intro ac bd
  apply lt_of_lt_of_le
  apply int.add.lt_left.mp
  assumption
  apply int.add.le_right.mp
  assumption

def int.add_lt_of_le_of_lt { a b c d: int } : a ≤ b -> c < d -> (a + c) < (b + d) := by
  intro ac bd
  apply lt_of_le_of_lt
  apply int.add.le_left.mp
  assumption
  apply int.add.lt_right.mp
  assumption

def int.sub.lt { a b c d: int } : a < b -> c > d -> (a - c) < (b - d) := by
  intro ab cd
  rw [sub.def, sub.def]
  apply add.lt
  assumption
  apply neg.swap_lt.mp
  assumption

def int.sub.lt_of_lt_of_le { a b c d: int } : a < b -> c ≥ d -> (a - c) < (b - d) := by
  intro ab cd
  rw [sub.def, sub.def]
  apply add_lt_of_lt_of_le
  assumption
  apply neg.swap_le.mp
  assumption

def int.sub.lt_of_le_of_lt { a b c d: int } : a ≤ b -> c > d -> (a - c) < (b - d) := by
  intro ab cd
  rw [sub.def, sub.def]
  apply add_lt_of_le_of_lt
  assumption
  apply neg.swap_lt.mp
  assumption

def int.sub.le { a b c d: int } : a ≤ b -> c ≥ d -> (a - c) ≤ (b - d) := by
  intro ab cd
  rw [sub.def, sub.def]
  apply add.le
  assumption
  apply neg.swap_le.mp
  assumption

def int.neg.inc (a: int) : -a.inc = (-a).dec := by
  cases a
  rfl
  rename_i a
  cases a <;> rfl
  rename_i a
  cases a <;> rfl

def int.neg.dec (a: int) : -a.dec = (-a).inc := by
  cases a
  rfl
  rename_i a
  cases a <;> rfl
  rename_i a
  cases a <;> rfl

def int.add_eq_iff_eq_sub {a b k: int} : a + k = b ↔ a = b - k := by
  induction k using strong_induction generalizing a b with
  | zero => rw [add_zero, sub_zero]
  | inc k ih =>
    rw [sub_inc, add_inc]
    apply Iff.trans inc_eq_iff_eq_dec
    rw [←dec_sub]
    apply ih
  | dec k ih =>
    rw [sub_dec, add_dec]
    apply Iff.trans eq_inc_iff_dec_eq.symm
    rw [←inc_sub]
    apply ih

def int.eq_add_iff_sub_eq {a b k: int} : a = b + k ↔ a - k = b := by
  apply Iff.trans
  apply Iff.intro Eq.symm Eq.symm
  apply flip Iff.trans
  apply Iff.intro Eq.symm Eq.symm
  apply int.add_eq_iff_eq_sub

def int.add.zero_le (a b: int) : 0 ≤ a -> 0 ≤ b -> 0 ≤ a + b := by
  intro h₀ h₁
  rw [←add_zero (a := 0)]
  apply add.le <;> assumption

def int.of_nat.of_zero_le {a: int} : 0 ≤ a -> ∃n, a = int.of_nat n := by
  intro h
  cases h
  rename_i n
  exists n.succ
  exists 0

def int.of_nat.of_zero_lt {a: int} : 0 < a -> ∃n, a = .pos_succ n := by
  intro h
  cases h
  rename_i n
  exists n

def int.of_nat.of_lt_zero {a: int} : a < 0 -> ∃n, a = .neg_succ n := by
  intro h
  cases h
  rename_i n
  exists n

def int.of_nat.of_le_zero {a: int} : a ≤ 0 -> ∃n, a = -int.of_nat n := by
  intro h
  cases h
  rename_i n
  exists n.succ
  exists 0
