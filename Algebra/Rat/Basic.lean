import Algebra.Int.Mul
import Algebra.Nat.Gcd

structure rat where
  num: int
  den: nat
  den_nz: 0 < den
  is_reduced: num.abs.gcd den = 1
deriving Repr, DecidableEq

def rat.new (num den: int) (den_nz: den ≠ 0) : rat := 
  rat.mk
    (den.sign * num.sign * (num.abs / (num.abs.gcd den.abs)))
    (den.abs / (num.abs.gcd den.abs))
    (by
      generalize int.abs num = n
      generalize d_def:int.abs den = d
      have := nat.gcd.dvd_right n d
      apply Decidable.byContradiction
      intro div_eq_zero
      cases nat.div.of_eq_zero (nat.le_zero <| TotalOrder.not_lt_implies_ge div_eq_zero) with
      | inl gcd_eq_zero =>
        have ⟨ _, d_eq_zero ⟩ := nat.gcd.eq_zero gcd_eq_zero
        rw [←d_def] at d_eq_zero
        apply den_nz
        cases den
        rfl
        repeat contradiction
      | inr d_lt_gcd =>
        apply TotalOrder.not_lt_and_ge d_lt_gcd
        apply nat.dvd.le _ (nat.gcd.dvd_right n d)
        cases d 
        apply False.elim
        apply den_nz
        cases den
        rfl
        repeat contradiction
        apply nat.zero_lt_succ
      )
    (by
      cases num with
      | zero => 
        rw [int.zero_eq, int.sign.zero, int.Sign.zero_right, int.Sign.int_zero, int.abs.zero, nat.gcd.comm, nat.gcd.right_zero, nat.gcd.comm, nat.gcd.right_zero, nat.div.self]
        cases den
        contradiction
        repeat apply nat.zero_lt_succ
      | pos_succ num =>
        rw [int.sign.pos, int.Sign.pos_right, int.abs.pos_succ, int.abs.sign_mul]
        {
          cases den
          any_goals contradiction
          any_goals rw [int.abs.pos_succ]
          any_goals rw [int.abs.neg_succ]
          all_goals (
            rename_i den
            rw [nat.gcd.div_common, nat.div.self]
            {
              apply Decidable.byContradiction
              intro gcd_eq_zero
              have gcd_eq_zero := nat.le_zero <| TotalOrder.not_lt_implies_ge gcd_eq_zero
              cases nat.gcd.eq_zero gcd_eq_zero
              contradiction
            }
            apply nat.gcd.dvd_left
            apply nat.gcd.dvd_right
          )
        }
        cases den
        any_goals contradiction
        apply Or.inl
        intro; contradiction
        apply Or.inl
        intro; contradiction
      | neg_succ num =>
        rw [int.sign.neg, int.Sign.neg_right, int.abs.neg_succ, int.abs.sign_mul]
        {
          cases den
          any_goals contradiction
          any_goals rw [int.abs.pos_succ]
          any_goals rw [int.abs.neg_succ]
          all_goals (
            rename_i den
            rw [nat.gcd.div_common, nat.div.self]
            {
              apply Decidable.byContradiction
              intro gcd_eq_zero
              have gcd_eq_zero := nat.le_zero <| TotalOrder.not_lt_implies_ge gcd_eq_zero
              cases nat.gcd.eq_zero gcd_eq_zero
              contradiction
            }
            apply nat.gcd.dvd_left
            apply nat.gcd.dvd_right
          )
        }
        cases den
        any_goals contradiction
        apply Or.inl
        intro; contradiction
        apply Or.inl
        intro; contradiction)

#print axioms rat.new

def rat.zero : rat := rat.mk 0 1 (by decide) (by decide)

def rat.neg (a: rat) : rat := rat.new (-a.num) a.den (by
  cases a with
  | mk _ a a_nz _ =>
  simp only
  cases a
  contradiction
  intro; contradiction)

#print axioms rat.neg

instance rat.neg.inst : Neg rat := ⟨ rat.neg ⟩

-- a.n / a.d + b.n / b.d
-- (a.n * b.d) / (a.d * b.d) + (a.d * b.n) / (a.d * b.d)
-- (a.n * b.d + a.d * b.n) / (a.d * b.d)
def rat.add (a b: rat) : rat := rat.new (
    a.num * b.den + a.den * b.num
  ) (
    a.den * b.den
  ) (by
    cases a with
    | mk _ a a_nz _ =>
    cases b with
    | mk _ b b_nz _ =>
    match a with
    | .succ a =>
    match b with
    | .succ b =>
      intro; contradiction
  )

#print axioms rat.add

instance rat.add.inst : Add rat := ⟨ rat.add ⟩ 

def rat.sub (a b: rat) : rat := a + -b

#print axioms rat.sub

instance rat.sub.inst : Sub rat := ⟨ rat.sub ⟩ 

def rat.mul (a b: rat) : rat := rat.new (
    a.num * b.den + a.den * b.num
  ) (
    a.den * b.den
  ) (by
    cases a with
    | mk _ a a_nz _ =>
    cases b with
    | mk _ b b_nz _ =>
    match a with
    | .succ a =>
    match b with
    | .succ b =>
      intro; contradiction
  )

#print axioms rat.add

instance rat.mul.inst : Mul rat := ⟨ rat.mul ⟩

def rat.invert (a: rat) : a.num ≠ 0 -> rat := rat.new a.den a.num

postfix:max " ⁻¹ " => rat.invert

#print axioms rat.invert

def rat.div (a b: rat) : b.num ≠ 0 -> rat := fun h => a * (b⁻¹ h)

instance : Div rat where
  div a b := match h:b.num with
     | .zero => rat.zero
     | .pos_succ _ | .neg_succ _ => rat.div a b (by intro g; rw [h] at g; contradiction)



