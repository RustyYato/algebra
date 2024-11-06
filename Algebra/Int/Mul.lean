import Algebra.Int.Add
import Algebra.Int.Abs
import Algebra.Nat.Mul
import Algebra.ClassicLogic

def int.mul (a b: int) : int := a.sign * b.sign * (‖a‖ * ‖b‖)

instance int.mul.inst : Mul int := ⟨ int.mul ⟩

def int.mul.def { a b: int } : a * b = int.mul a b := rfl

def int.zero_mul { b: int } : 0 * b = 0 := by
  rw [mul.def]
  unfold mul
  rw [int.sign.zero, int.Sign.zero_left, int.Sign.int_zero]

def int.mul_zero { b: int } : b * 0 = 0 := by
  rw [mul.def]
  unfold mul
  rw [int.sign.zero, int.Sign.zero_right, int.Sign.int_zero]

def int.one_mul { b: int } : 1 * b = b := by
  rw [mul.def]
  unfold mul
  rw [←one_eq, sign.pos, int.Sign.pos_left]
  conv => {
    lhs; rhs; lhs
    unfold abs
    simp
  }
  erw [abs.one, nat.one_mul, abs.sign]

def int.neg_one_mul { b: int } : -1 * b = -b := by
  rw [mul.def]
  unfold mul
  rw [←one_eq, neg.pos_succ, sign.neg, int.Sign.neg_left]
  conv => {
    lhs; rhs; lhs
    unfold abs
    simp
  }
  erw [abs.neg_one, nat.one_mul, abs.flip_sign]

def int.neg_mul { a b: int } : -a * b = -(a * b) := by
  cases a <;> cases b <;> rfl

def int.mul_neg { a b: int } : a * -b = -(a * b) := by
  cases a <;> cases b <;> rfl

def int.mul.comm (a b: int) : a * b = b * a := by
  rw [mul.def, mul.def]
  unfold mul
  rw [nat.mul.comm]
  congr 1
  cases a <;> cases b <;> rfl

def int.mul_one { b: int } :  b * 1 = b := by
  rw [int.mul.comm, one_mul]

def int.mul_neg_one { b: int } :  b * -1 = -b := by
  rw [int.mul.comm, neg_one_mul]

def int.mul.assoc (a b c: int) : a * b * c = a * (b * c) := by
  repeat rw [mul.def]
  unfold mul
  rw [int.abs.sign_mul]
  rw [int.sign.of_sign_mul]
  rw [int.sign.of_sign_mul]
  congr 1
  { -- sign eq
    cases a <;> cases b <;> cases c <;> rfl
  }
  rw [int.abs.sign_mul]
  apply nat.mul.assoc
  {
    cases b <;> cases c
    any_goals (apply Or.inr; rfl)
    any_goals (apply Or.inl; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }
  {
    cases b <;> cases c
    any_goals (apply Or.inl; rfl)
    any_goals (apply Or.inr; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }
  {
    cases a <;> cases b
    any_goals (apply Or.inl; rfl)
    any_goals (apply Or.inr; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }
  {
    cases a <;> cases b
    any_goals (apply Or.inr; rfl)
    any_goals (apply Or.inl; intro; contradiction)
    all_goals (rw [zero_eq, abs.zero, nat.mul_zero]; apply Or.inr; rfl)
  }

def int.mul.right_comm (a b c: int) :
  a * b * c = a * c * b := by rw [int.mul.assoc, int.mul.comm b, int.mul.assoc]

def int.mul.left_comm (a b c: int) :
  a * b * c = c * b * a := by rw [int.mul.comm _ c, int.mul.comm a, int.mul.assoc]

def int.mul.comm_left (a b c: int) :
  a * (b * c) = b * (a * c) := by
  rw [←int.mul.assoc, ←int.mul.assoc, int.mul.comm a]

def int.mul.comm_right (a b c: int) :
  a * (b * c) = c * (b * a) := by
  rw [int.mul.comm _ c, int.mul.comm a, int.mul.assoc]

def int.mul.abs_sign_mul_pos : ∀(x: nat) (y: int), y.sign * (nat.succ x * y.abs) = (int.pos_succ x) * y := by intro x y; cases y <;> rfl
def int.mul.abs_sign_mul_neg : ∀(x: nat) (y: int), y.sign.flip * (nat.succ x * y.abs) = (int.neg_succ x) * y := by intro x y; cases y <;> rfl

def int.inc_mul (a b: int) : a.inc * b = a * b + b := by
  rw [mul.def, mul.def]
  unfold mul
  cases a with
  | zero =>
    erw [int.zero_eq, inc.zero, sign.zero, sign.pos, nat.one_mul]
    rw [Sign.pos_left, Sign.zero_left, Sign.int_zero, zero_add, int.abs.sign]
  | pos_succ a =>
    conv => {
      lhs; rhs
      rw [inc.pos_succ, abs.pos_succ, nat.succ_mul]
    }
    rw [int.add.sign_mul,  ←mul, inc.pos_succ, int.sign.pos]
    conv in Sign.pos * _ * (a.succ * ‖b‖) => {
      rw [←int.abs.pos_succ (a := a), ←int.sign.pos (x := a)]
    }
    rw [←mul, Sign.pos_left, int.abs.sign, int.add.comm]
  | neg_succ a =>
    cases a with
    | zero =>
      erw [int.sign.zero, int.sign.neg, Sign.zero_left, Sign.int_zero, nat.one_mul,
        Sign.neg_left, int.abs.flip_sign, int.add.comm, ←int.sub.def, int.sub.self]
    | succ a =>
      erw [int.sign.neg, int.abs.neg_succ, int.abs.neg_succ]
      conv in Sign.neg * _ * (a.succ.succ * ‖b‖) => {
        rw [nat.succ_mul, int.add.sign_mul]
        lhs
        rw [Sign.neg_left, int.abs.flip_sign]
      }
      rw [int.add.comm, ←add.assoc, ←sub.def, sub.self, zero_add]

def int.mul_inc (a b: int) : a * b.inc = a * b + a := by
  rw [mul.comm, inc_mul, mul.comm]

def int.dec_mul (a b: int) : a.dec * b = a * b - b := by
  apply neg.inj
  rw [←neg_mul, int.dec.neg, inc_mul, sub.neg, add.comm, sub.def, neg_mul]

def int.mul_dec (a b: int) : a * b.dec = a * b - a := by
  rw [mul.comm, dec_mul, mul.comm]

def int.add_mul { a b k: int } : (a + b) * k = a * k + b * k := by
  induction k using strong_induction generalizing a b with
  | zero => rw [mul_zero, mul_zero, mul_zero, add_zero]
  | inc k ih => rw [mul_inc, mul_inc, mul_inc, ih, add.assoc,
    add.comm_left (b * _), ←add.assoc]
  | dec k ih => rw [mul_dec, mul_dec, mul_dec, ih, sub.def, sub.def, sub.def,
    add.neg, add.assoc, add.comm_left (b * _), ←add.assoc]

def int.mul_add { a b k: int } : k * (a + b) = k * a + k * b := by
  repeat rw [int.mul.comm k]
  apply int.add_mul

def int.sub_mul { a b k: int } : (a - b) * k = a * k - b * k := by
  rw [sub.def, sub.def, add_mul, neg_mul]

def int.mul_sub { a b k: int } : k * (a - b) = k * a - k * b := by
  rw [sub.def, sub.def, mul_add, mul_neg]

def int.mul.sub_left { a b k: int } : (a - b) * k = a * k - b * k := by
  rw [sub.def, add_mul, neg_mul, ←sub.def]

def int.mul.sub_right { a b k: int } : k * (a - b) = k * a - k * b := by
  rw [sub.def, mul_add, mul_neg, ←sub.def]

def int.mul.pos_pos_is_pos { a b: int } : 0 < a -> 0 < b -> 0 < a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  any_goals exact .zero_pos
  all_goals contradiction

def int.mul.neg_neg_is_pos { a b: int } : 0 > a -> 0 > b -> 0 < a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  any_goals exact .zero_pos
  all_goals contradiction

def int.mul.pos_neg_is_neg { a b: int } : 0 < a -> 0 > b -> 0 > a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  any_goals exact .neg_zero
  all_goals contradiction

def int.mul.neg_pos_is_neg { a b: int } : 0 > a -> 0 < b -> 0 > a * b := by
  intros pos_a pos_b
  cases a <;> cases b
  any_goals assumption
  any_goals exact .neg_zero
  all_goals contradiction

def int.mul.eq_zero { a b: int } : a * b = 0 -> a = 0 ∨ b = 0 := by
  intro ab_eq_zero
  cases a <;> cases b
  any_goals (apply Or.inl; rfl)
  any_goals (apply Or.inr; rfl)
  all_goals contradiction

def int.mul.eq_pos { a b: int } : a * b > 0 -> (a < 0 ∧ b < 0) ∨ (a > 0 ∧ b > 0) := by
  intro ab_gt_zero
  cases a <;> cases b
  any_goals contradiction
  apply Or.inr <;> apply And.intro <;> exact .zero_pos
  apply Or.inl <;> apply And.intro <;> exact .neg_zero

def int.mul.eq_neg { a b: int } : a * b < 0 -> (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) := by
  intro ab_lt_zero
  cases a <;> cases b
  any_goals contradiction
  apply Or.inr <;> exact And.intro .zero_pos .neg_zero
  apply Or.inl <;> exact And.intro .neg_zero .zero_pos

def int.sign_mul.mul_of_nat { s: int.Sign } { a b: nat } : s * a * (b: int) = s * (a * b) := by
  cases b with
  | zero =>
    unfold of_nat
    simp only
    rw [zero_eq, mul_zero, nat.zero_eq, nat.mul_zero]
    cases s <;> rfl
  | succ b =>
  cases a with
  | zero =>
    cases s <;> rfl
  | succ a =>
    unfold of_nat
    simp only

    rw [int.mul.def]
    unfold mul
    rw [sign.of_sign_mul, sign.pos, int.Sign.pos_right, abs.pos_succ]
    {
      cases s with
      | zero => rfl
      | pos =>
        repeat rw [int.Sign.int_pos]
        rw [abs.of_nat]
      | neg =>
        repeat rw [int.Sign.int_neg]
        rw [abs.neg_of_nat]
    }
    {
      apply Or.inr
      apply nat.noConfusion
    }

def int.mul.lift_nat (a b: nat) : (a: int) * (b: int) = of_nat (a * b) := by
  induction b with
  | zero =>
    have : of_nat 0 = 0 := rfl
    rw [nat.zero_eq, nat.mul_zero, this, mul_zero]
  | succ b ih =>
    rw [int.inc.of_nat_succ, int.mul_inc, nat.mul_succ, int.add.lift_nat, ih, int.add.comm]

def int.mul.of_eq (a b: int) : ∀k, k ≠ 0 -> a * k = b * k -> a = b := by
  intro k k_ne_zero eq
  induction a using strong_induction generalizing b with
  | zero =>
    rw [zero_mul] at eq
    cases int.mul.eq_zero eq.symm
    symm; assumption
    contradiction
  | inc a ih =>
    rw [inc_mul] at eq
    have := int.add_eq_iff_eq_sub.mp eq
    rw [←dec_mul] at this
    rw [ih _ this, dec_inc_inv]
  | dec a ih =>
    rw [dec_mul] at eq
    have := int.eq_add_iff_sub_eq.mpr eq
    rw [←inc_mul] at this
    rw [ih _ this, inc_dec_inv]

def int.abs.mul (a b: int) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  cases a <;> cases b
  any_goals rfl
  all_goals rw [zero_eq, int.mul_zero, int.abs.zero, nat.mul_zero]

def int.mul.le_mul_pos { a b: int } :
  ∀{k}, 0 < k -> (a ≤ b ↔ a * k ≤ b * k)
| .pos_succ k, h => by
  clear h
  suffices (0 ≤ b - a ↔ 0 ≤ (b - a) * .pos_succ k) by
    apply Iff.trans _ (Iff.trans this _)
    conv in a ≤ b => { rw [←@zero_add a] }
    exact add_le_iff_le_sub
    conv in a * pos_succ k => { rw [←@zero_add (a * pos_succ k)] }
    symm
    rw [sub_mul]
    exact add_le_iff_le_sub
  apply Iff.intro
  intro h
  have ⟨n,prf⟩ := of_nat.of_zero_le h
  rw [prf]
  cases n
  exact .zero
  exact .zero_pos
  intro h
  have ⟨n,nprf⟩ := of_nat.of_zero_le h
  apply Decidable.byContradiction
  intro h₀
  have ⟨m,mprf⟩ := of_nat.of_lt_zero (lt_of_not_le h₀)
  rw [mprf] at nprf
  cases n <;> contradiction

def int.mul.inj_mul_pos { a b k: int } : 0 < k -> a * k = b * k -> a = b := by
  intro k_pos h
  apply le_antisymm
  apply (int.mul.le_mul_pos k_pos).mpr
  rw [h]
  apply (int.mul.le_mul_pos k_pos).mpr
  rw [h]

def int.mul.lt_mul_pos { a b: int } :
  ∀{k}, 0 < k -> (a < b ↔ a * k < b * k)
| .pos_succ k, h => by
  clear h
  suffices (0 < b - a ↔ 0 < (b - a) * .pos_succ k) by
    apply Iff.trans _ (Iff.trans this _)
    conv in a < b => { rw [←@zero_add a] }
    exact add_lt_iff_lt_sub
    conv in a * pos_succ k => { rw [←@zero_add (a * pos_succ k)] }
    symm
    rw [sub_mul]
    exact add_lt_iff_lt_sub
  apply Iff.intro
  intro h
  have ⟨n,prf⟩ := of_nat.of_zero_lt h
  rw [prf]
  exact .zero_pos
  intro h
  have ⟨n,nprf⟩ := of_nat.of_zero_lt h
  apply Decidable.byContradiction
  intro h₀
  have ⟨m,mprf⟩ := of_nat.of_le_zero (le_of_not_lt h₀)
  rw [mprf] at nprf
  cases m <;> contradiction

def int.mul.le_mul_neg { a b: int } :
  ∀{k}, k < 0 -> (a ≤ b ↔ b * k ≤ a * k)
| .neg_succ k, _ => by
  apply Iff.trans _ neg.swap_le.symm
  rw [←mul_neg, ←mul_neg, neg.neg_succ]
  apply int.mul.le_mul_pos
  exact pos_lt_zero

def int.mul.lt_mul_neg { a b: int } :
  ∀{k}, k < 0 -> (a < b ↔ b * k < a * k)
| .neg_succ k, _ => by
  apply Iff.trans _ neg.swap_lt.symm
  rw [←mul_neg, ←mul_neg, neg.neg_succ]
  apply int.mul.lt_mul_pos
  exact pos_lt_zero

def int.abs.inc_succ (a: int) : ‖a.inc‖ ≤ ‖a‖.succ := by
  cases a
  rfl
  rfl
  rename_i a
  cases a
  apply nat.zero_le
  unfold inc
  dsimp
  rw [int.abs.neg_succ, int.abs.neg_succ]
  apply le_trans
  apply le_of_lt
  apply nat.lt_succ_self
  apply le_of_lt
  apply nat.lt_succ_self

def int.abs.dec_succ (a: int) : ‖a.dec‖ ≤ ‖a‖.succ := by
  rw [←int.abs.neg, int.neg.dec]
  apply le_trans
  apply int.abs.inc_succ
  rw [int.abs.neg]

def int.abs.tri (a b: int) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  have : ∀a b: nat, ‖int.pos_succ a + int.neg_succ b‖ ≤ a.succ + b.succ := by
    clear a b
    intro a b
    rw [int.add.def, add]
    dsimp
    rw [int.sub_nat.dec]
    induction b generalizing a with
    | zero =>
      rw [int.sub_nat, nat.one_eq, nat.add_one]
      cases a
      decide
      rename_i a
      rw [int.dec]
      dsimp
      rw [int.abs.pos_succ]
      apply le_trans
      apply le_of_lt
      apply nat.lt_succ_self
      apply le_of_lt
      apply nat.lt_succ_self
    | succ b ih =>
      rw [sub_nat, sub_nat.dec]
      apply le_trans
      apply int.abs.dec_succ
      rw [nat.add_succ]
      apply nat.succ_le_succ
      apply ih

  cases a <;> cases b
  rfl
  any_goals rw [int.zero_eq]
  any_goals rw [int.abs.zero]
  any_goals rw [int.add.zero_left]
  any_goals rw [int.add.zero_right]
  any_goals rw [nat.zero_add]
  any_goals rw [nat.add_zero]
  any_goals repeat rw [int.abs.pos_succ]
  any_goals repeat rw [int.abs.neg_succ]
  · rw [int.add.def, add]
    dsimp
    unfold inc
    dsimp
    rw [int.add_nat.pos_succ, int.abs.pos_succ, nat.add_succ]
  · apply this
  · rw [int.add.comm, nat.add.comm]
    apply this
  · rw [←int.abs.neg, int.add.neg, int.neg.neg_succ, int.neg.neg_succ]
    rw [int.add.def, add]
    dsimp
    unfold inc
    dsimp
    rw [int.add_nat.pos_succ, int.abs.pos_succ, nat.add_succ]

def int.abs.tri_lt' (a b: nat) : ‖int.pos_succ a + int.neg_succ b‖ < ‖int.pos_succ a‖ + ‖int.neg_succ b‖ := by
rw [int.add.def, int.add]
dsimp
rw [int.sub_nat.dec]
induction b with
| zero =>
  rw [int.sub_nat]
  cases a
  trivial
  rw [int.dec]
  dsimp
  rename_i a
  rw [int.abs.pos_succ, int.abs.pos_succ, int.abs.neg_succ]
  rw [nat.one_eq, nat.add_one]
  apply lt_trans
  apply nat.lt_succ_self
  apply nat.lt_succ_self
| succ b ih =>
  rw [int.sub_nat, int.sub_nat.dec]
  apply lt_of_le_of_lt
  apply int.abs.dec_succ
  apply lt_of_lt_of_le
  apply nat.succ_lt_succ
  apply ih
  clear ih
  rw [int.abs.pos_succ, int.abs.neg_succ, int.abs.neg_succ, nat.add_succ _ b.succ]

def int.abs.tri_lt (a b: int) : (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b) -> ‖a + b‖ < ‖a‖ + ‖b‖ := by
  intro h
  cases a <;> cases b
  all_goals (
    cases h <;> rename_i h
    <;> cases h <;> rename_i l r
  )
  any_goals contradiction
  all_goals (rename_i a b; clear l r)
  apply int.abs.tri_lt'
  rw [int.add.comm, nat.add.comm]
  apply int.abs.tri_lt'

def int.mul.pos_succ_pos_succ (a b: nat) :
  int.pos_succ a * int.pos_succ b = int.of_nat (a.succ * b.succ) := rfl

def int.mul.pos_succ_neg_succ (a b: nat) :
  int.pos_succ a * int.neg_succ b = -int.of_nat (a.succ * b.succ) := rfl

def int.mul.neg_succ_pos_succ (a b: nat) :
  int.neg_succ a * int.pos_succ b = -int.of_nat (a.succ * b.succ) := rfl

def int.mul.neg_succ_neg_succ (a b: nat) :
  int.neg_succ a * int.neg_succ b = int.of_nat (a.succ * b.succ) := rfl
