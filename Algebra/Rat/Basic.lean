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

def rat.equiv (anum bnum: int) (aden bden: nat) := anum * bden = bnum * aden 

def rat.eq_of_equiv (anum bnum: int) (aden bden: nat) (aden_nz: (aden: int) ≠ 0) (bden_nz: (bden: int) ≠ 0) : 
  rat.equiv anum bnum aden bden ->
  rat.new anum aden aden_nz = rat.new bnum bden bden_nz := by
  intro equiv
  unfold rat.equiv at equiv
  match aden with 
  | .succ aden =>
  match bden with 
  | .succ bden =>
  unfold new
  have this_fst : ∀{a b c d: nat},
    0 < b ->
    0 < d ->
    a * d = c * b -> a / b = c / d := by
    clear equiv bden_nz bden aden_nz anum bnum
    clear aden bden
    clear aden
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

  have this_snd : ∀{a b c d: nat},
    a * d = c * b -> a * (nat.gcd d c) = c * (nat.gcd b a) := by
    clear this_fst
    clear equiv bden_nz bden aden_nz anum bnum
    clear aden bden
    clear aden
    intro a d c b
    intro ab_eq_de
    rw [←nat.gcd.common_left, ←nat.gcd.common_left, ab_eq_de, nat.mul.comm a c]

  conv at equiv => {
    rw [int.mul.def, int.mul.def, int.mul, int.mul]
    unfold int.of_nat
    simp only
    rw [int.sign.pos, int.sign.pos, int.Sign.pos_right, int.Sign.pos_right, int.abs.pos_succ, int.abs.pos_succ]
  }
  congr 1
  {
    unfold int.of_nat
    simp only
    rw [int.sign.pos, int.sign.pos, int.Sign.pos_left, int.Sign.pos_left]
    congr 1 
    {
      cases anum <;> cases bnum
      any_goals rfl
      all_goals contradiction
    }
    {
      rw [int.abs.pos_succ, int.abs.pos_succ]
      apply this_fst

      cases h:nat.gcd anum.abs aden.succ
      have ⟨ _, _ ⟩ := nat.gcd.eq_zero h
      contradiction
      apply nat.zero_lt_succ
      cases h:nat.gcd bnum.abs bden.succ
      have ⟨ _, _ ⟩ := nat.gcd.eq_zero h
      contradiction
      apply nat.zero_lt_succ

      repeat rw [nat.gcd.comm _ (.succ _)]
      apply @this_snd anum.abs aden.succ bnum.abs bden.succ
      cases anum <;> cases bnum
      any_goals contradiction
      rw [int.zero_eq, int.abs.zero, nat.zero_mul, nat.zero_mul]
      rename_i anum bnum
      rw [int.abs.pos_succ, int.abs.pos_succ]
      conv at equiv => {
        rw [int.sign.pos, int.sign.pos, int.Sign.int_pos, int.Sign.int_pos]
        rw [int.abs.pos_succ, int.abs.pos_succ]
      }
      apply int.of_nat.inj
      assumption
      rename_i anum bnum
      rw [int.abs.neg_succ, int.abs.neg_succ]
      conv at equiv => {
        rw [int.sign.neg, int.sign.neg, int.Sign.int_neg, int.Sign.int_neg]
        rw [int.abs.neg_succ, int.abs.neg_succ]
      }
      apply int.of_nat.inj
      apply int.neg.inj
      assumption
    }
  }
  {
    apply this_fst

    cases h:nat.gcd anum.abs (int.abs aden.succ)
    have ⟨ _, _ ⟩ := nat.gcd.eq_zero h
    contradiction
    apply nat.zero_lt_succ
    cases h:nat.gcd bnum.abs (int.abs bden.succ)
    have ⟨ _, _ ⟩ := nat.gcd.eq_zero h
    contradiction
    apply nat.zero_lt_succ

    unfold int.of_nat
    rw [int.abs.pos_succ, int.abs.pos_succ]
    apply this_snd
    apply Eq.symm
    rw [nat.mul.comm, nat.mul.comm (.succ _)]
    cases anum <;> cases bnum
    any_goals contradiction
    rw [int.zero_eq, int.abs.zero, nat.zero_mul, nat.zero_mul]
    rename_i anum bnum
    rw [int.abs.pos_succ, int.abs.pos_succ]
    conv at equiv => {
      rw [int.sign.pos, int.sign.pos, int.Sign.int_pos, int.Sign.int_pos]
      rw [int.abs.pos_succ, int.abs.pos_succ]
    }
    apply int.of_nat.inj
    assumption
    conv at equiv => {
      rw [int.sign.neg, int.sign.neg, int.Sign.int_neg, int.Sign.int_neg]
      rw [int.abs.neg_succ, int.abs.neg_succ]
    }
    rw [int.abs.neg_succ, int.abs.neg_succ]
    apply int.of_nat.inj
    apply int.neg.inj
    assumption
  }

#print axioms rat.eq_of_equiv

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
