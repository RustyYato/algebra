import Algebra.Nat.Gcd
import Algebra.Int.Mul
import Algebra.Order.Basic

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

instance fract.ofNatInst : OfNat fract n where
  ofNat := fract.mk n 1 (by trivial)

instance rat.ofNatInst : OfNat rat n where
  ofNat := rat.mk n 1 (by trivial) (by rw [nat.gcd.one_right])

instance fract.equiv.instEquiv : Equivalence fract.equiv where
  refl := fun _ => rfl
  symm := by
    intro x y
    unfold equiv
    intro x_eq_y
    rw [x_eq_y]
  trans := by
    intro x y z
    unfold equiv
    intro x_eq_y y_eq_z

    -- xnum * yden = ynum * xden
    -- xnum * yden * zden = ynum * xden * zden
    -- (xnum * zden) * yden = ynum * xden * zden

    -- ynum * zden = znum * yden
    -- ynum * zden * xden = znum * yden * xden
    -- ynum * (zden * xden) = znum * yden * xden
    -- ynum * (xden * zden) = znum * yden * xden
    -- (xden * zden) * ynum = znum * yden * xden
    -- (xden * zden) * ynum = znum * yden  * xden
    --                       (xnum * zden) * yden = ynum * xden * zden -- from before
    --                       (znum * xden) * yden = ynum * xden * zden
    --                       (znum * yden) * xden = ynum * xden * zden
    --
    -- (xden * zden) * ynum = ynum * xden * zden
    cases y with
    | mk ynum yden yden_nz =>

    simp only at *
    cases g:ynum with
    | zero =>
      cases g
      rw [int.zero_eq] at *
      rw [int.mul.zero_left] at *
      cases int.mul.eq_zero x_eq_y with
      | inr h => cases yden <;> contradiction
      | inl h =>
      rw [h]
      clear h
      cases int.mul.eq_zero y_eq_z.symm with
      | inr h => cases yden <;> contradiction
      | inl h =>
      rw [h]
      clear h
      repeat rw [int.mul.zero_left]
    | pos_succ ynum' | neg_succ ynum' =>
      have x_eq_y' : (x.num * yden) * z.den = (x.num * yden) * z.den := rfl
      conv at x_eq_y' => {
        rhs
        rw [x_eq_y]
      }
      have y_eq_z': (ynum * z.den) * x.den = (ynum * z.den) * x.den := rfl
      conv at y_eq_z' => {
        rhs
        rw [y_eq_z]
      }
      conv at y_eq_z' => {
        lhs
        rw [int.mul.assoc, int.mul.comm z.den, ←int.mul.assoc]
      }
      have x_eq_z := Eq.trans x_eq_y' y_eq_z'
      apply int.mul.of_eq
      intro x
      have : int.of_nat yden = int.of_nat 0 := x
      cases int.of_nat.inj this
      contradiction
      clear x_eq_y' y_eq_z' g y_eq_z x_eq_y ynum' yden_nz ynum
      rw [int.mul.assoc, int.mul.comm z.den, ←int.mul.assoc, x_eq_z]
      rw [int.mul.assoc, int.mul.comm yden, ←int.mul.assoc]

instance fract.setoid : Setoid fract where
  r := fract.equiv
  iseqv := fract.equiv.instEquiv

#print axioms fract.equiv.instEquiv

instance fract.equiv.transInst : Trans fract.equiv fract.equiv fract.equiv := ⟨ fract.equiv.instEquiv.trans ⟩

instance : HasEquiv fract := ⟨ fract.equiv ⟩

def fract.equiv.trans {a b c: fract} : a ≈ b -> b ≈ c -> a ≈ c := fract.equiv.instEquiv.trans
def fract.equiv.symm {a b: fract} : a ≈ b -> b ≈ a := fract.equiv.instEquiv.symm

def fract.equiv.def (a b: fract) : (a ≈ b) = (fract.equiv a b) := rfl

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
  have div_mul_eq : ∀{a b: nat} (_b_nz: 0 < b), a / b * b = a - a % b := by
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

def rat.eq_of_equiv (a b: fract) : a ≈ b -> a.to_rat = b.to_rat := by
  intro a_eq_b
  cases a with
  | mk anum aden aden_nz =>
  cases b with
  | mk bnum bden bden_nz =>
  unfold fract.to_rat
  simp only at *
  rw [fract.equiv.def] at a_eq_b
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

def rat.equiv_of_eq (a b: rat) : a = b -> a.to_simple ≈ b.to_simple := by
  intro h
  subst h
  rfl

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

def fract.neg (a: fract) : fract := fract.mk (-a.num) a.den a.den_nz

def rat.neg (a: rat) : rat := rat.mk (-a.num) a.den a.den_nz (by
  rw [int.abs.neg]
  exact a.is_reduced)

#print axioms rat.neg

instance fract.neg.inst : Neg fract := ⟨ fract.neg ⟩
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

def fract.add.def (a b: fract) : a + b = fract.mk (a.num * b.den + a.den * b.num) (a.den * b.den) (
  by
    apply Decidable.byContradiction
    intro h
    have := nat.le_zero <| TotalOrder.le_of_not_gt h
    cases nat.mul.eq_zero this <;> rename_i h
    have := a.den_nz
    rw [h] at this
    contradiction
    have := b.den_nz
    rw [h] at this
    contradiction
) := rfl

#print axioms fract.add.def
def rat.add.def { a b: rat } : a + b = (a.to_simple + b.to_simple).to_rat := rfl

def rat.sub (a b: rat) : rat := a + -b

#print axioms rat.sub

instance rat.sub.inst : Sub rat := ⟨ rat.sub ⟩

def rat.neg.def (r: rat) : -r = rat.mk (-r.num) r.den r.den_nz (by
  rw [int.abs.neg]
  exact r.is_reduced
  ) := by rfl

#print axioms rat.neg.def

def rat.add.to_simple (a b : rat) : (a + b).to_simple ≈ a.to_simple + b.to_simple := fract.to_rat_to_simple _

def fract.add.comm (a b : fract ) : (a + b) ≈ (b + a) := by
  cases a with
  | mk anum aden aden_nz =>
  cases b with
  | mk bnum bden bden_nz =>
  rw [fract.add.def, fract.add.def]
  simp only
  rw [fract.equiv.def]
  unfold equiv
  simp only
  rw [int.add.comm, int.mul.comm bnum, int.mul.comm anum, nat.mul.comm]

#print axioms fract.add.comm

def rat.add.comm (a b : rat ) : a + b = b + a := by
  apply rat.eq_of_equiv
  apply fract.add.comm

#print axioms rat.add.comm

def fract.add.equiv_left (a b k: fract) : fract.equiv a k -> fract.equiv (a + b) (k + b) := by
  intro a_eq_k
  unfold equiv
  rw [fract.add.def, fract.add.def]
  simp only
  unfold equiv at a_eq_k
  repeat rw [←int.mul.lift_nat]
  repeat rw [int.mul.add_left, int.mul.add_left]
  repeat rw [int.mul.comm _ b.den]
  repeat rw [int.mul.comm _ b.num]
  repeat rw [int.mul.assoc]
  repeat rw [←int.mul.assoc _ b.den]
  repeat rw [int.mul.comm _ b.den]
  repeat rw [←int.mul.assoc]
  repeat rw [int.mul.comm b.num b.den]
  repeat rw [int.mul.assoc]
  repeat rw [←int.mul.add_right]
  congr 1
  rw [a_eq_k]
  congr 2
  rw [int.mul.comm]

#print axioms fract.add.equiv_left

def fract.add.equiv_right (a b k: fract) : a ≈ k -> (b + a) ≈ (b + k) := by
  intro a_eq_k
  apply equiv.instEquiv.trans (fract.add.comm b a)
  apply equiv.instEquiv.trans _ (fract.add.comm k b)
  apply fract.add.equiv_left
  assumption

#print axioms fract.add.equiv_right

def fract.add.of_equiv (a b c d: fract) : a ≈ c -> b ≈ d -> (a + b) ≈ (c + d) := by
  intro a_eq_c b_eq_d
  exact equiv.instEquiv.trans
    (fract.add.equiv_left a b c a_eq_c)
    (fract.add.equiv_right b c d b_eq_d)

#print axioms fract.add.of_equiv

def fract.add.assoc (a b c: fract) : (a + b) + c ≈ a + (b + c) := by
  repeat rw [fract.add.def]
  dsimp
  rw [fract.equiv.def, fract.equiv]
  dsimp
  repeat (
    first|
    rw [int.mul.add_left]|
    rw [int.mul.add_right]|
    rw [←int.mul.assoc]|
    rw [←int.add.assoc]|
    rw [←int.mul.lift_nat]
  )

def rat.add.assoc (a b c: rat) : (a + b) + c = a + (b + c) := by
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
  apply fract.equiv.trans
  apply fract.add.of_equiv
  apply fract.to_rat_to_simple
  rfl
  apply fract.equiv.trans _
  apply fract.add.of_equiv
  rfl
  apply fract.equiv.symm (fract.to_rat_to_simple _)
  apply fract.add.assoc

def fract.add.cancel_left (a b k: fract) : a + k ≈ b + k -> a ≈ b := by
  intro h
  cases a with | mk an ad adnz =>
  cases b with | mk bn bd bdnz =>
  cases k with | mk kn kd kdnz =>
  rw [equiv.def, equiv, add.def, add.def] at h
  rw [equiv.def, equiv]
  dsimp at *
  have : ∀x y,
    x * int.of_nat kd * (y * int.of_nat kd) =
    x * y * (int.of_nat kd * int.of_nat kd) := by
    intro x y
    clear h
    rw [int.mul.assoc, ←int.mul.assoc _ y, int.mul.comm _ y, ←int.mul.assoc, ←int.mul.assoc, ←int.mul.assoc]
  have this2 : ∀x y,
    x * kn * (y * int.of_nat kd) =
    x * y * (kn * int.of_nat kd) := by
    intro x y
    clear h
    rw [int.mul.assoc, ←int.mul.assoc _ y, int.mul.comm _ y, ←int.mul.assoc, ←int.mul.assoc, ←int.mul.assoc]
  conv at h => {
    repeat (
      first|
      rw [←int.mul.lift_nat]|
      rw [int.mul.add_left]|
      rw [this]|
      rw [this2]
    )
  }
  clear this this2
  rw [int.mul.comm (int.of_nat bd)] at h
  replace h := int.add.right_iff_sub.mp h
  rw [int.sub.def, int.add.assoc, ←int.sub.def, int.sub.refl, int.add.zero_right] at h
  apply int.mul.of_eq _ _ _ _
  assumption
  intro h
  cases int.mul.eq_zero h <;> rename_i h
  cases kd <;> contradiction
  cases kd <;> contradiction

def rat.add.cancel_left (a b k: rat) : a + k = b + k -> a = b := by
  intro h
  have := equiv_of_eq _ _ h
  replace this := fract.equiv.trans this (add.to_simple _ _)
  replace this := fract.equiv.trans (fract.equiv.symm (add.to_simple _ _)) this
  replace this := fract.add.cancel_left _ _ _ this
  replace this := eq_of_equiv _ _ this
  rw [to_simple_to_rat, to_simple_to_rat] at this
  exact this

#print axioms rat.add.cancel_left

def rat.add.cancel_right (a b k: rat) : k + a = k + b -> a = b := by
  intro h
  rw [add.comm k, add.comm k] at h
  apply add.cancel_left
  assumption

#print axioms rat.add.cancel_right

def rat.abs (a: rat) : rat := rat.mk a.num.abs a.den a.den_nz <| by
  rw [int.abs.of_nat]
  exact a.is_reduced

def fract.mul (a b: fract) : fract := fract.mk (a.num * b.num) (a.den * b.den) (by
  apply Decidable.byContradiction
  intro h
  replace h := nat.le_zero (TotalOrder.le_of_not_lt h)
  cases nat.mul.eq_zero h
  · cases a with | mk n d nz =>
    dsimp at *
    subst d
    contradiction
  · cases b with | mk n d nz =>
    dsimp at *
    subst d
    contradiction)

def rat.mul (a b: rat) : rat := (fract.mul a.to_simple b.to_simple).to_rat

instance fract.mul.inst : Mul fract := ⟨ fract.mul ⟩
instance rat.mul.inst : Mul rat := ⟨ rat.mul ⟩

def fract.invert (a: fract) : fract :=
  match a.num with
    | .pos_succ num => fract.mk ↑a.den num.succ nat.zero_lt_succ
    | .neg_succ num => fract.mk (-↑a.den) num.succ nat.zero_lt_succ
    | .zero => 0

def rat.invert (a: rat) : rat :=
  match h:a.num with
    | .pos_succ num => rat.mk ↑a.den num.succ nat.zero_lt_succ (by
      rw [int.abs.of_nat, nat.gcd.comm]
      have := a.is_reduced
      have : num.succ = a.num.abs := by
        rw [h]
        rfl
      rw [this]
      exact a.is_reduced)
    | .neg_succ num => rat.mk (-↑a.den) num.succ nat.zero_lt_succ (by
      rw [int.abs.neg, int.abs.of_nat, nat.gcd.comm]
      have := a.is_reduced
      have : num.succ = a.num.abs := by
        rw [h]
        rfl
      rw [this]
      exact a.is_reduced)
    | .zero => 0

postfix:max "⁻¹ " => rat.invert

#print axioms rat.invert

def rat.div (a b: rat) : rat := a * b⁻¹

instance : Div rat := ⟨ rat.div ⟩

def rat.mul.def (a b: rat) : a * b = a.mul b := rfl
def fract.mul.def (a b: fract) : a * b = a.mul b := rfl
def rat.mul.to_simple (a b : rat) : (a * b).to_simple ≈ a.to_simple * b.to_simple := fract.to_rat_to_simple _

def fract.mul.inv_right (a: fract) : ¬(a ≈ 0) -> a * a.invert ≈ 1 := by
  intro a_nz
  cases a with | mk n d d_nz =>
  rw [mul.def, mul, invert]
  dsimp
  cases n with
  | zero =>
    dsimp
    apply False.elim
    apply a_nz
    rw [fract.equiv.def, fract.equiv]
    dsimp
    erw [int.zero_eq, int.mul.zero_left, int.mul.zero_left]
  | pos_succ n =>
    dsimp
    rw [fract.equiv.def, fract.equiv]
    dsimp
    erw [int.mul.one_right, int.mul.one_left, ←int.mul.lift_nat, int.mul.comm]
    rfl
  | neg_succ n =>
    dsimp
    rw [fract.equiv.def, fract.equiv]
    dsimp
    erw [int.mul.one_right, int.mul.one_left, ←int.mul.lift_nat, int.mul.comm]
    cases d
    contradiction; rename_i d
    rw [←int.of_nat.pos, int.neg.pos_succ]
    rw [←int.neg.pos_succ, ←int.neg.pos_succ, ←int.mul.neg_left, ←int.mul.neg_right, int.neg_neg]
    rfl

def rat.mul.inv_right (a: rat) : a ≠ 0 -> a * a⁻¹ = 1 := by
  intro a_nz
  cases a with | mk n d nz red =>
  rw [mul.def, mul]
  have : 1 = fract.to_rat 1 := rfl
  rw [this]
  apply eq_of_equiv
  dsimp
  unfold invert
  cases n <;> dsimp
  rw [int.zero_eq, int.abs.zero, nat.gcd.left_zero] at red
  subst d
  contradiction
  rename_i n
  apply fract.mul.inv_right
  intro h
  have : (0: fract) ≈ ⟨ 0, 1, nat.zero_lt_succ⟩ := rfl
  have := (fract.equiv.instEquiv.trans h this)
  unfold fract.equiv at this
  dsimp at this
  have of_nat_one : int.of_nat 1 = 1 := rfl
  rw [int.mul.zero_left, of_nat_one, int.mul.one_right] at this
  contradiction
  apply fract.mul.inv_right
  intro h
  have : (0: fract) ≈ ⟨ 0, 1, nat.zero_lt_succ⟩ := rfl
  have := (fract.equiv.instEquiv.trans h this)
  unfold fract.equiv at this
  dsimp at this
  have of_nat_one : int.of_nat 1 = 1 := rfl
  rw [int.mul.zero_left, of_nat_one, int.mul.one_right] at this
  contradiction

def fract.mul.comm (a b: fract) : a * b ≈ b * a := by
  cases a with | mk anum aden aden_pos =>
  cases b with | mk bnum bden bden_pos =>
  rw [mul.def, mul, mul.def, mul, equiv.def, equiv]
  dsimp
  rw [←int.mul.lift_nat, ←int.mul.lift_nat]
  congr 1
  rw [int.mul.comm]
  rw [int.mul.comm]

def rat.mul.comm (a b: rat) : a * b = b * a := by
  cases a with | mk anum aden aden_pos =>
  cases b with | mk bnum bden bden_pos =>
  rw [mul.def, mul, mul.def, mul]
  apply eq_of_equiv
  apply fract.mul.comm

def fract.add.congr (a b c d: fract) :
  a ≈ c ->
  b ≈ d ->
  a + b ≈ c + d := by
  cases a with | mk anum aden aden_pos =>
  cases b with | mk bnum bden bden_pos =>
  cases c with | mk cnum cden cden_pos =>
  cases d with | mk dnum dden dden_pos =>
  repeat rw [add.def]
  repeat rw [equiv.def, equiv]
  dsimp
  intro ac bd
  have : ∀x, 0 < x -> 0 < int.of_nat x := by
    intro x x_pos
    have : 0 = int.of_nat 0 := rfl
    apply TotalOrder.lt_of_compare
    rw [this, int.of_nat.compare]
    assumption
  repeat rw [←int.mul.lift_nat]
  rw [int.mul.add_left, int.mul.add_left]
  repeat rw [int.mul.assoc]
  congr 1
  rw [int.mul.comm_left _ cden, int.mul.comm_left _ aden, int.mul.comm dden]
  rw [←int.mul.assoc, ←int.mul.assoc cnum]
  apply TotalOrder.eq_of_compare_eq
  rw [←int.mul.compare_left_pos]
  rw [ac]
  apply TotalOrder.compare_eq_refl
  apply TotalOrder.lt_of_compare
  rw [int.mul.pos_pos_is_pos]
  exact this _ bden_pos
  exact this _ dden_pos
  rw [int.mul.comm_left _ cden,
    int.mul.comm_left _ aden]
  rw [←int.mul.assoc, ←int.mul.assoc cden]
  rw [int.mul.comm, int.mul.comm cden, int.mul.comm (aden * _)]
  apply TotalOrder.eq_of_compare_eq
  rw [←int.mul.compare_left_pos]
  rw [bd]
  apply TotalOrder.compare_eq_refl
  apply TotalOrder.lt_of_compare
  rw [int.mul.pos_pos_is_pos]
  exact this _ aden_pos
  exact this _ cden_pos

def fract.mul.congr (a b c d: fract) :
  a ≈ c ->
  b ≈ d ->
  a * b ≈ c * d := by
  cases a with | mk anum aden aden_pos =>
  cases b with | mk bnum bden bden_pos =>
  cases c with | mk cnum cden cden_pos =>
  cases d with | mk dnum dden dden_pos =>
  repeat rw [mul.def, mul]
  repeat rw [equiv.def, equiv]
  dsimp
  intro ac bd
  repeat rw [←int.mul.lift_nat]
  rw [int.mul.assoc, int.mul.assoc, int.mul.comm_left bnum, int.mul.comm_left dnum]
  rw [←int.mul.assoc anum, ←int.mul.assoc cnum]
  congr 1

def fract.mul.assoc (a b c: fract) : a * b * c ≈ a * (b * c) := by
  cases a with | mk anum aden aden_pos =>
  cases b with | mk bnum bden bden_pos =>
  cases c with | mk cnum cden cden_pos =>
  repeat rw [mul.def, mul]
  rw [equiv.def, equiv]
  dsimp
  repeat rw [←int.mul.lift_nat]
  congr 1
  rw [int.mul.assoc]
  rw [int.mul.assoc]

def rat.mul.assoc (a b c: rat) : a * b * c = a * (b * c) := by
  repeat rw [mul.def]
  unfold mul
  apply eq_of_equiv
  apply fract.equiv.trans
  apply fract.mul.congr
  apply fract.to_rat_to_simple
  rfl
  apply flip fract.equiv.trans
  apply fract.mul.congr
  rfl
  apply fract.equiv.symm
  apply fract.to_rat_to_simple
  apply fract.mul.assoc

def rat.div.self (a: rat) : a ≠ 0 -> a / a = 1 := rat.mul.inv_right a

def rat.div.def (a b: rat) : a / b = a * b⁻¹ := rfl

def rat.div.mul_left (a b c: rat) : a * b / c = a * (b / c) := by
  rw [div.def, div.def, rat.mul.assoc]

def rat.neg_neg (a: rat) : - -a = a := by
  rw [rat.neg.def, rat.neg.def]
  dsimp
  congr
  rw [int.neg_neg]

def fract.add.mul_left (a b k: fract) :
  k * (a + b) ≈ k * a + k * b := by
  repeat first|rw [add.def]|rw [mul.def]|rw [mul]|rw [add]
  rw [equiv.def, equiv]
  dsimp
  repeat rw [←int.mul.lift_nat]
  repeat first|rw [int.mul.add_right]|rw [int.mul.add_left]
  repeat rw [int.mul.assoc]
  congr 1
  congr 2
  rw [int.mul.comm_left]
  congr 2
  rw [int.mul.comm_left]
  repeat rw [int.mul.comm_left _ k.num]
  congr 1
  repeat rw [int.mul.comm_left _ k.den]

def rat.add.mul_left (a b k: rat) :
  k * (a + b) = k * a + k * b := by
  apply eq_of_equiv
  apply fract.equiv.trans
  apply fract.mul.congr
  rfl
  apply rat.add.to_simple
  apply flip fract.equiv.trans
  apply fract.equiv.symm
  apply fract.add.congr
  apply rat.mul.to_simple
  apply rat.mul.to_simple
  apply fract.add.mul_left

def rat.add.mul_right (a b k: rat) :
  (a + b) * k = a * k + b * k := by
  repeat rw [mul.comm _ k]
  apply rat.add.mul_left
