import Algebra.Nat.Gcd
import Algebra.Int.Mul

structure fract where
  num: int
  den: nat
  den_nz: 0 < den
deriving Repr, DecidableEq

structure rat where
  num: int
  den: nat
  den_nz: 0 < den
  is_reduced: num.abs.gcd den = 1
deriving Repr, DecidableEq

def fract.equiv (a b: fract) : Prop := a.num * b.den = b.num * a.den

def fract.to_rat (r: fract) : rat := rat.mk
    (r.num.sign * (r.num.abs / (r.num.abs.gcd r.den)))
    (r.den / (r.num.abs.gcd r.den))
    (by
      cases r with
      | mk num den den_nz =>
      generalize int.abs num = n
      generalize d_def:int.abs den = d
      have := nat.gcd.dvd_right n d
      apply Decidable.byContradiction
      intro div_eq_zero
      cases nat.div.of_eq_zero (nat.le_zero <| TotalOrder.not_lt_implies_ge div_eq_zero) with
      | inl gcd_eq_zero =>
        have ⟨ _, d_eq_zero ⟩ := nat.gcd.eq_zero gcd_eq_zero
        cases d_eq_zero
        contradiction
      | inr d_lt_gcd =>
        simp only at d_lt_gcd
        apply TotalOrder.not_lt_and_ge d_lt_gcd
        apply nat.dvd.le _ (nat.gcd.dvd_right n den)
        assumption
      )
    (by
      cases r with
      | mk num den den_nz =>
      cases num with
      | zero => 
        rw [int.zero_eq, int.sign.zero, int.Sign.int_zero, int.abs.zero, nat.gcd.comm, nat.gcd.right_zero, nat.gcd.comm, nat.gcd.right_zero, nat.div.self]
        assumption
      | pos_succ num =>
        rw [int.sign.pos, int.abs.pos_succ, int.abs.sign_mul]
        simp only
        {
          cases den
          any_goals contradiction
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
      | neg_succ num =>
        rw [int.sign.neg, int.abs.neg_succ, int.abs.sign_mul]
        {
          cases den
          any_goals contradiction
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
        intro; contradiction)

#print axioms fract.to_rat

def rat.to_simple (r: rat) : fract := fract.mk r.num r.den r.den_nz

def rat.new (num den: int) (den_nz: den ≠ 0) : rat := 
  (fract.mk num den.abs (by cases den <;> trivial)).to_rat

#print axioms rat.new

def rat.to_simple_to_rat (r: rat) : r.to_simple.to_rat = r := by
  unfold to_simple fract.to_rat
  simp only
  congr
  rw [r.is_reduced, nat.div.one, int.abs.sign]
  rw [r.is_reduced, nat.div.one]

#print axioms rat.to_simple_to_rat

def nat.div_eq_of_mul_eq: ∀{a b c d: nat},
  0 < b ->
  0 < d ->
  a * d = c * b -> a / b = c / d := by
  intro a b c d b_nz d_nz ad_eq_cb
  apply nat.eq_of_mul_eq b_nz
  apply nat.eq_of_mul_eq d_nz
  -- here is a sketch of the proof
  -- d * (b * (a / b)) = d * (b * (c / d))
  -- d * (a - (a % b)) = b * (d * (c / d))
  -- d * a - d * (a % b) = b * c - b * (c % d)
  -- d * (a % b) = b * (c % d)
  -- ((d * a) % (d * b)) = ((b * c) % (b * d))
  -- d * b = b * d
  have div_mul_eq : ∀{a b: nat} (b_nz: 0 < b), a / b * b = a - a % b := by
    intro a b b_nz
    have ab_div_def := nat.div_def a b b_nz
    have : a - (a % b) = a - (a % b) := rfl
    conv at this => {
      lhs; lhs
      rw [ab_div_def]
    }
    rw [nat.add_sub_inv] at this
    assumption
  rw [nat.mul.comm b, ←nat.mul.assoc d b, nat.mul.comm d b, nat.mul.assoc, nat.mul.comm d (_ / _), div_mul_eq b_nz, div_mul_eq d_nz]
  rw [nat.mul_sub, nat.mul_sub]
  congr 1
  rw [nat.mul.comm, ad_eq_cb, nat.mul.comm]
  rw [nat.mul.comm, ←nat.mul_mod, nat.mul.comm b (_ % _), ←nat.mul_mod]
  congr 1
  rw [nat.mul.comm]

def nat.mul_gcd_eq: ∀{a b c d: nat},
    a * d = c * b -> a * (nat.gcd d c) = c * (nat.gcd b a) := by
    intro a d c b
    intro ab_eq_de
    rw [←nat.gcd.common_left, ←nat.gcd.common_left, ab_eq_de, nat.mul.comm a c]

def rat.eq_of_equiv (a b: fract) : a.equiv b -> a.to_rat = b.to_rat := by
  intro a_eq_b
  cases a with
  | mk anum aden aden_nz =>
  cases b with
  | mk bnum bden bden_nz =>
  unfold fract.to_rat
  simp only at *
  unfold fract.equiv at a_eq_b
  simp only at a_eq_b
  match aden with
  | .succ aden =>
  match bden with
  | .succ bden =>
  congr 1 <;> clear aden_nz bden_nz
  {
    congr 1
    cases anum <;> cases bnum <;> trivial
    apply nat.div_eq_of_mul_eq
    apply nat.gcd.gt_zero
    apply Or.inr nat.zero_lt_succ
    apply nat.gcd.gt_zero
    apply Or.inr nat.zero_lt_succ
    repeat rw [nat.gcd.comm _ (.succ _)]
    apply nat.mul_gcd_eq
    cases anum <;> cases bnum
    any_goals contradiction
    rw [int.zero_eq, int.abs.zero, nat.zero_mul, nat.zero_mul]
    rename_i anum bnum
    rw [int.abs.pos_succ, int.abs.pos_succ]
    conv at a_eq_b => {
      repeat rw [int.mul.def, int.mul]
      unfold int.of_nat
      simp only
      repeat rw [int.sign.pos]
      repeat rw [int.Sign.pos_left]
      repeat rw [int.Sign.int_pos]
      repeat rw [int.abs.pos_succ]
    }
    apply int.of_nat.inj
    assumption
    rename_i anum bnum
    rw [int.abs.neg_succ, int.abs.neg_succ]
    have : int.Sign.pos.flip = int.Sign.neg := rfl
    conv at a_eq_b => {
      repeat rw [int.mul.def, int.mul]
      unfold int.of_nat
      simp only
      repeat rw [int.sign.neg]
      repeat rw [int.sign.pos]
      repeat rw [int.Sign.neg_left]
      rw [this]
      repeat rw [int.Sign.int_neg]
      repeat rw [int.abs.neg_succ]
    }
    apply int.of_nat.inj
    apply int.neg.inj
    assumption
  }
  {
    apply nat.div_eq_of_mul_eq
    apply nat.gcd.gt_zero
    apply Or.inr nat.zero_lt_succ
    apply nat.gcd.gt_zero
    apply Or.inr nat.zero_lt_succ
    apply nat.mul_gcd_eq
    cases anum <;> cases bnum
    any_goals trivial
    rw [int.zero_eq, int.abs.zero, nat.mul_zero, nat.mul_zero]

    rename_i anum bnum
    rw [int.abs.pos_succ, int.abs.pos_succ]
    conv at a_eq_b => {
      unfold int.of_nat
      simp only
      rw [int.mul.def, int.mul, int.mul.def, int.mul, int.sign.pos, int.sign.pos,
        int.Sign.pos_left, int.Sign.int_pos, int.sign.pos, int.sign.pos, int.Sign.pos_left, int.Sign.int_pos]
      repeat rw [int.abs.pos_succ]
    }
    apply int.of_nat.inj
    apply Eq.symm
    rw [nat.mul.comm, a_eq_b, nat.mul.comm]
    conv at a_eq_b => {
      unfold int.of_nat
      simp only
      rw [int.mul.def, int.mul, int.mul.def, int.mul, int.sign.neg, int.sign.neg,
        int.sign.pos, int.sign.pos, int.Sign.neg_left]
      unfold int.Sign.flip
      simp only
      rw [int.Sign.int_neg, int.Sign.int_neg]
      repeat rw [int.abs.neg_succ]
      repeat rw [int.abs.pos_succ]
    }
    rw [int.abs.neg_succ, int.abs.neg_succ]
    apply int.of_nat.inj
    apply int.neg.inj
    rw [nat.mul.comm (.succ aden), nat.mul.comm (.succ bden)]
    exact a_eq_b.symm
  }

#print axioms rat.eq_of_equiv

def fract.equiv_refl (a: fract) : a.equiv a := rfl

def fract.to_rat_to_simple (a: fract) : a.to_rat.to_simple.equiv a := by
  unfold to_rat rat.to_simple
  unfold equiv
  rw [@int.mul.def a.num]
  unfold int.mul
  simp only
  rw [int.sign_mul.mul_of_nat]
  congr 1
  {
    cases a with
    | mk num den den_nz =>
    simp only
    cases num with
    | zero =>
      rw [int.zero_eq, int.sign.zero, int.Sign.zero_left]
    | pos_succ a =>
      rw [int.sign.pos, int.Sign.pos_left, int.abs.pos_succ]
      cases h:(den / nat.gcd a.succ den)
      {
        cases nat.div.of_eq_zero h with
        | inl h =>
          have ⟨ _, _ ⟩ := nat.gcd.eq_zero h
          contradiction
        | inr h =>
          apply False.elim
          apply TotalOrder.not_lt_and_ge h
          apply nat.dvd.le
          assumption
          apply nat.gcd.dvd_right
      }
      {
        unfold int.of_nat
        simp only
        rw [int.sign.pos]
      }
    | neg_succ a =>
      rw [int.sign.neg, int.Sign.neg_left, int.abs.neg_succ]
      cases h:(den / nat.gcd a.succ den)
      {
        cases nat.div.of_eq_zero h with
        | inl h =>
          have ⟨ _, _ ⟩ := nat.gcd.eq_zero h
          contradiction
        | inr h =>
          apply False.elim
          apply TotalOrder.not_lt_and_ge h
          apply nat.dvd.le
          assumption
          apply nat.gcd.dvd_right
      }
      {
        unfold int.of_nat
        simp only
        rw [int.sign.pos]
        rfl
      }
  }
  {
    cases a with
    | mk num den den_nz =>
    simp only
    match den with
    | .succ den =>
    clear den_nz
    cases h:(den.succ / nat.gcd (int.abs num) den.succ)
    {
    cases nat.div.of_eq_zero h with
    | inl h =>
      have ⟨ _, _ ⟩ := nat.gcd.eq_zero h
      contradiction
    | inr h =>
      apply False.elim
      apply TotalOrder.not_lt_and_ge h
      apply nat.dvd.le
      apply nat.zero_lt_succ
      apply nat.gcd.dvd_right
    }
    {
      unfold int.of_nat
      simp only
      rw [int.abs.pos_succ]
      rw [←h]
      clear h; rename_i n; clear n; revert den; clear den; intro den
      rw [nat.mul.comm]
      rw [nat.dvd.mul_div, nat.dvd.mul_div, nat.mul.comm]
      apply nat.gcd.dvd_right
      apply nat.gcd.dvd_left
    }
  }

#print axioms fract.to_rat_to_simple

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

def fract.add (a b: fract) : fract := fract.mk (
    a.num * b.den + a.den * b.num
  ) (
    a.den * b.den
  ) (by
    cases a
    cases b
    simp only
    rename_i a _ _ b _
    match a with
    | .succ a =>
    match b with
    | .succ b =>
    rfl
  )

#print axioms fract.add

instance fract.add.inst : Add fract := ⟨ fract.add ⟩ 

-- a.n / a.d + b.n / b.d
-- (a.n * b.d) / (a.d * b.d) + (a.d * b.n) / (a.d * b.d)
-- (a.n * b.d + a.d * b.n) / (a.d * b.d)
def rat.add (a b: rat) : rat :=
  (a.to_simple + b.to_simple).to_rat

#print axioms rat.add

instance rat.add.inst : Add rat := ⟨ rat.add ⟩

def rat.add.def { a b: rat } : a + b = (a.to_simple + b.to_simple).to_rat := rfl

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

def rat.new.def (num: int) (den: nat) : ∀den_nz g h, rat.new num den den_nz = rat.mk num den g h := by
  intro den_nz zero_lt_den is_reduced
  unfold new
  congr
  {
    cases den with
    | zero => contradiction
    | succ den =>
      unfold int.of_nat 
      simp only
      rw [int.sign.pos, int.Sign.pos_left, int.abs.pos_succ, is_reduced, nat.div.one, int.abs.sign]
  }
  {
    cases den with
    | zero => contradiction
    | succ den =>
      unfold int.of_nat 
      simp only
      rw [int.abs.pos_succ, is_reduced, nat.div.one]
  }

#print axioms rat.new.def
def rat.neg.def (r: rat) : ∀g h, -r = rat.mk (-r.num) r.den g h := by
  intro g h
  cases r
  conv => {
    lhs
    unfold Neg.neg
  }
  unfold rat.neg.inst
  simp only
  unfold rat.neg
  unfold new
  apply fract.to_rat.def
  rw [rat.new.def]

#print axioms rat.new.def

def rat.add.comm (a b : rat ) : a + b = b + a := by
  cases a with
  | mk a_num a_den a_den_nz a_is_reduced =>
  cases b with
  | mk b_num b_den b_den_nz b_is_reduced =>
  unfold HAdd.hAdd instHAdd Add.add inst 
  simp only
  unfold add
  simp only
  congr 1
  {
    rw [int.add.comm, int.mul.comm]
    congr 1
    apply int.mul.comm
  }
  {
    rw [int.mul.comm]
  }

#print axioms rat.add.comm

def rat.add.assoc (a b c: rat ) : (a + b) + c = a + (b + c) := by
  cases a with
  | mk a_num a_den a_den_nz a_is_reduced =>
  cases b with
  | mk b_num b_den b_den_nz b_is_reduced =>
  cases c with
  | mk c_num c_den c_den_nz c_is_reduced =>
  unfold HAdd.hAdd instHAdd Add.add inst 
  simp only
  unfold add

  apply rat.eq_of_equiv
  conv =>{
    arg 1
    conv => {
      arg 1
      arg 1
      unfold to_simple
    }
    conv => {
      arg 2 
      unfold to_simple
    }
  }
  conv =>{
    arg 2
    conv => {
      arg 2
      arg 1
      unfold to_simple
    }
    conv => {
      arg 1 
      unfold to_simple
    }
  }
  simp only
  admit

#print axioms rat.add.assoc

