import Algebra.Int.Neg

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

def int.add.def : a + b = int.add a b := rfl
def int.sub.def : a - b = a + (-b) := rfl

def int.add_zero { a: int } : a + 0 = a := by cases a <;> rfl

def int.inc.pos : (int.pos_succ a).inc = int.pos_succ a.succ := rfl
def int.dec.neg : (int.neg_succ a).dec = int.neg_succ a.succ := rfl

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
        rw [←int.inc.pos, add_nat.inc, ih]
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
        rw [←int.dec.neg, sub_nat.dec, ih]
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

