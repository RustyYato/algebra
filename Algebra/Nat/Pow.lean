import Algebra.Nat.Mul

def nat.pow (n m: nat) := match m with
  | .zero => 1
  | .succ m => n * n.pow m

#print axioms nat.pow

instance nat.pow.inst : Pow nat nat where
  pow := nat.pow

#print axioms nat.pow.inst

def nat.pow.zero { n: nat } : n ^ (0: nat) = 1 := rfl
def nat.pow.succ { n m: nat }: n ^ m.succ = n * n ^ m := rfl

def nat.pow.mul { a b c: nat } : (a ^ b) * (a ^ c) = a ^ (b + c) := by
  induction c generalizing b with
  | zero => rw [zero_eq, nat.pow.zero, mul_one, add_zero]
  | succ c ih =>
    rw [pow.succ, ←mul.assoc, mul.comm _ a, ←pow.succ, add_succ, ←succ_add]
    apply ih

#print axioms nat.pow.mul

def nat.pow.reduce { a b c: nat } : (a ^ b) ^ c = a ^ (b * c) := by
  induction c generalizing b with
  | zero => rw [zero_eq, mul_zero, pow.zero, pow.zero]
  | succ c ih => rw [pow.succ, mul_succ, ←pow.mul, ih]

#print axioms nat.pow.reduce

def nat.pow.of_zero { n: nat } : 0 < n -> (0: nat) ^ n = 0 := by
  intro n_nz
  cases n with
  | zero => contradiction
  | succ n => rw [pow.succ, zero_mul]

#print axioms nat.pow.of_zero

def nat.pow.eq_zero { a b: nat } : a ^ b = 0 -> a = 0 ∧ 0 < b := by
  intro a_pow_b_eq_zero
  cases b with
  | zero => contradiction
  | succ b =>
    apply And.intro _ zero_lt_succ
    cases a with
    | zero => rfl
    | succ a =>
      rw [pow.succ] at a_pow_b_eq_zero
      cases mul.eq_zero a_pow_b_eq_zero with
      | inl h => contradiction
      | inr h =>
        have ⟨ _, _ ⟩ := nat.pow.eq_zero h
        contradiction

#print axioms nat.pow.eq_zero

def nat.pow.of_one { n: nat } : (1: nat) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow.succ, one_mul, ih]

#print axioms nat.pow.of_one

def nat.pow.eq_one { a b: nat } : a ^ b = 1 -> a = 1 ∨ b = 0 := by
  intro a_pow_b_eq_one
  cases b with
  | zero =>
    apply Or.inr
    rfl
  | succ b =>
    rw [pow.succ] at a_pow_b_eq_one
    have ⟨ _, _ ⟩  := mul.eq_one a_pow_b_eq_one
    apply Or.inl
    assumption

#print axioms nat.pow.eq_zero

def nat.pow.ge_of_nz_exp { a b: nat } : 0 < b -> a ^ b ≥ a := by
  intro b_nz
  match b with
  | .succ b =>
  cases a with
  | zero =>
    rw [zero_eq, of_zero]
    apply le_refl
    exact zero_lt_succ
  | succ a =>
  rw [pow.succ]
  apply nat.mul.ge
  cases decEq (nat.succ a ^ b) 0 with
  | isTrue h =>
    have ⟨ _, _ ⟩ := eq_zero h
    contradiction
  | isFalse h =>
    apply lt_of_le_and_ne
    apply zero_le
    intro g
    exact h g.symm

#print axioms nat.pow.ge_of_nz_exp

def nat.pow.gt { a b: nat } : 1 < b -> 1 < a -> a ^ b > a := by
  intro one_lt_b one_lt_a
  cases lt_or_eq_of_le <| @nat.pow.ge_of_nz_exp a b (lt_trans zero_lt_succ one_lt_b) with
  | inl h => assumption
  | inr h =>
    match b with
    | .succ (.succ b) =>
    clear one_lt_b
    apply False.elim
    rw [pow.succ] at h
    conv at h => {
      lhs
      rw [←mul_one a]
    }
    have h := nat.mul.cancel_left a 1 (a ^ b.succ) (lt_trans zero_lt_succ one_lt_a) h
    cases eq_one h.symm
    rename_i h; cases h
    contradiction
    contradiction

#print axioms nat.pow.gt
