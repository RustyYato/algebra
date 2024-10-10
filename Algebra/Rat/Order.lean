import Algebra.Rat.Basic

def fract.order (a b: fract) : Ordering := compare (a.num * int.of_nat b.den) (b.num * int.of_nat a.den)
def rat.order (a b: rat) : Ordering := compare (a.num * int.of_nat b.den) (b.num * int.of_nat a.den)

instance fract.OrdInst : Ord fract := ⟨ order ⟩
instance rat.OrdInst : Ord rat := ⟨ order ⟩

instance rat.TotalOrderInst : TotalOrder rat where
  eq_of_compare_eq := by
    intro a b h
    unfold compare OrdInst order at h
    dsimp only at h
    have := rat.eq_of_equiv a.to_simple b.to_simple (TotalOrder.eq_of_compare_eq h)
    rw [to_simple_to_rat, to_simple_to_rat] at this
    assumption
  compare_eq_refl := by
    intro a
    unfold compare OrdInst order
    dsimp only
    rw [TotalOrder.compare_eq_refl]
  compare_antisymm := by
    intro a b
    unfold compare OrdInst order
    dsimp only
    rw [TotalOrder.compare_antisymm]
  compare_transitive := by
    intro a b c o  ab bc
    unfold compare OrdInst order at *
    dsimp only at *

    have lift_nat_pos : ∀n: nat, 0 < n -> (0: int) < n := by
      intro n h
      cases n
      contradiction
      trivial

    replace ab : compare (a.num * int.of_nat b.den * int.of_nat c.den) (b.num * int.of_nat a.den * int.of_nat c.den) = o := by
      rw [←int.mul.compare_left_pos]
      assumption
      apply lift_nat_pos
      exact c.den_nz
    replace bc : compare (b.num * int.of_nat c.den * int.of_nat a.den) (c.num * int.of_nat b.den * int.of_nat a.den) = o := by
      rw [←int.mul.compare_left_pos]
      assumption
      apply lift_nat_pos
      exact a.den_nz
    have : ∀a b c: int, a * b * c = a * c * b := by
      intros a b c
      rw [int.mul.assoc, @int.mul.comm b, ←int.mul.assoc]
    conv at bc in b.num * int.of_nat c.den * int.of_nat a.den => {
      rw [this]
    }
    have cmp := TotalOrder.compare_transitive ab bc
    rw [this _ b.den, this _ b.den] at cmp
    rw [←int.mul.compare_left_pos] at cmp
    assumption
    apply lift_nat_pos
    exact b.den_nz

def fract.compare_def (a b: fract) : compare a b = order a b := rfl

def rat.compare_of_fract { a b: fract } :
   compare a b = compare a.to_rat b.to_rat := by
    cases a with | mk anum aden aden_nz =>
    cases b with | mk bnum bden bden_nz =>
    unfold compare  fract.OrdInst OrdInst
    dsimp
    unfold order fract.order
    unfold fract.to_rat
    dsimp

    have : 0 < int.of_nat aden := by
      cases aden <;> trivial
    have : 0 < int.of_nat bden := by
      cases bden <;> trivial

    have of_nat_one : int.of_nat 1 = 1 := rfl
    have gcd_ne_zero : ∀x y: nat, 0 < y -> x.succ / x.succ.gcd y ≠ 0 := by
      intro x y _ h
      cases nat.div.of_eq_zero h <;> rename_i h
      · cases nat.gcd.eq_zero h
        contradiction
      · have := nat.dvd.le nat.zero_lt_succ (nat.gcd.dvd_left x.succ y)
        have := TotalOrder.not_lt_and_ge h this
        contradiction

    have gcd_pos : ∀x y: nat, 0 < y -> 0 < x -> 0 < x / x.gcd y := by
      intro x y y_pos x_pos
      cases x; contradiction
      rename_i x
      have := gcd_ne_zero x y y_pos
      apply Decidable.byContradiction
      intro h
      replace h := nat.le_zero (TotalOrder.le_of_not_lt h)
      contradiction

    have neg_pos_compare : ∀a b: int, 0 < a -> b < 0 -> b < a := by
      intro a b
      intro h g
      apply TotalOrder.lt_trans <;> assumption

    cases anum <;> rw [int.sign] <;> dsimp
    · rw [int.zero_eq, int.mul.zero_left, int.mul.zero_left]
      cases bnum <;> rw [int.sign] <;> dsimp
      · rw [int.zero_eq, int.mul.zero_left, int.mul.zero_left]
      · rename_i bnum
        rw [int.abs.pos_succ]
        have : bnum.succ / bnum.succ.gcd bden ≠ 0 := gcd_ne_zero bnum bden bden_nz
        split
        · rename_i h
          apply (this h).elim
        · rename_i m n _
          clear m
          match aden with
          | nat.succ aden =>
          rw [int.of_nat]
          dsimp
          rw [int.mul.pos_pos_is_pos]
          any_goals trivial
          rw [int.mul.pos_pos_is_pos]
          any_goals trivial
          apply Decidable.byContradiction
          intro g
          apply g
          rw [int.abs.zero, nat.gcd.comm, nat.gcd.right_zero, nat.div.self]
          trivial
          assumption
      · rename_i bnum
        rw [int.abs.neg_succ]
        have : bnum.succ / bnum.succ.gcd bden ≠ 0 := gcd_ne_zero bnum bden bden_nz
        split
        · rename_i h
          apply (this h).elim
        · rename_i m n _
          clear m
          match aden with
          | nat.succ aden =>
          rw [int.of_nat]
          dsimp
          rw [TotalOrder.compare_of_gt (int.mul.neg_pos_is_neg _ _)]
          any_goals trivial
          rw [TotalOrder.compare_of_gt (int.mul.neg_pos_is_neg _ _)]
          any_goals trivial
          apply Decidable.byContradiction
          intro g
          apply g
          rw [int.abs.zero, nat.gcd.comm, nat.gcd.right_zero, nat.div.self]
          trivial
          assumption
    · rename_i anum
      rw [int.abs.pos_succ]
      have : anum.succ / anum.succ.gcd aden ≠ 0 := gcd_ne_zero anum aden aden_nz
      split
      contradiction
      rename_i m n h
      clear m
      cases bnum
      · rw [int.sign]
        dsimp
        rw [int.zero_eq, int.abs.zero, nat.gcd.left_zero, nat.div.self, of_nat_one,
          int.mul.one_right, int.mul.zero_left, int.mul.zero_left,
          TotalOrder.swap_compare (int.mul.pos_pos_is_pos _ _),
          Ordering.swap]
        any_goals trivial
      · rename_i bnum
        have := gcd_ne_zero bnum bden bden_nz
        rw [int.abs.pos_succ]
        rw [int.sign.pos]
        dsimp
        split
        contradiction
        rename_i m n' h'
        clear m
        repeat rw [int.of_nat.pos, int.mul.lift_nat]
        rw [←h, ←h', int.of_nat.compare, int.of_nat.compare]
        clear h' h this
        clear this gcd_ne_zero of_nat_one n n'
        rw [nat.dvd.mul_div, nat.dvd.mul_div,
           nat.mul.comm (_ / _),  nat.mul.comm (_ / _),
           nat.dvd.mul_div, nat.dvd.mul_div]
        any_goals apply nat.gcd.dvd_left
        any_goals apply nat.gcd.dvd_right
        rw [nat.div_div, nat.div_div, nat.mul.comm (nat.gcd _ _),
          nat.div.compare_strict, nat.mul.comm bden, nat.mul.comm bnum.succ]
        apply Decidable.byContradiction
        intro h
        replace h := nat.le_zero (TotalOrder.le_of_not_lt h)
        cases nat.mul.eq_zero h <;> rename_i h <;> cases nat.gcd.eq_zero h
        contradiction
        contradiction
        apply nat.dvd.mul
        apply nat.gcd.dvd_right
        apply nat.gcd.dvd_left
        rw [nat.mul.comm]
        apply nat.dvd.mul
        apply nat.gcd.dvd_right
        apply nat.gcd.dvd_left
      · rename_i bnum
        have : bnum.succ / bnum.succ.gcd bden ≠ 0 := gcd_ne_zero bnum bden bden_nz
        rw [int.sign.neg]
        dsimp
        rw [int.abs.neg_succ]
        split
        contradiction
        rename_i m n' _
        clear m
        rw [TotalOrder.swap_compare rfl, neg_pos_compare]
        rw [TotalOrder.swap_compare rfl, neg_pos_compare]
        apply int.mul.pos_pos_is_pos
        trivial
        apply TotalOrder.lt_of_compare
        erw [int.of_nat.zero, int.of_nat.compare]
        apply TotalOrder.compare_of_lt
        rw [nat.gcd.comm]
        apply gcd_pos <;> trivial
        apply int.mul.neg_pos_is_neg
        trivial
        apply TotalOrder.lt_of_compare
        erw [int.of_nat.zero, int.of_nat.compare]
        apply TotalOrder.compare_of_lt
        rw [nat.gcd.comm]
        apply gcd_pos <;> trivial
        apply int.mul.pos_pos_is_pos
        trivial
        apply TotalOrder.lt_of_compare
        erw [int.of_nat.zero, int.of_nat.compare]
        apply TotalOrder.compare_of_lt
        trivial
        apply int.mul.neg_pos_is_neg
        trivial
        apply TotalOrder.lt_of_compare
        erw [int.of_nat.zero, int.of_nat.compare]
        apply TotalOrder.compare_of_lt
        trivial
    · rename_i anum
      rw [int.abs.neg_succ]
      have : anum.succ / anum.succ.gcd aden ≠ 0 := gcd_ne_zero anum aden aden_nz
      split
      contradiction
      rename_i m n h
      clear m
      cases bnum
      · rw [int.sign]
        dsimp
        rw [int.zero_eq, int.abs.zero, nat.gcd.left_zero, nat.div.self, of_nat_one,
          int.mul.one_right, int.mul.zero_left, int.mul.zero_left,
          (int.mul.neg_pos_is_neg _ _)]
        any_goals trivial
      · rename_i bnum
        have := gcd_ne_zero bnum bden bden_nz
        rw [int.abs.pos_succ]
        rw [int.sign.pos]
        dsimp
        split
        contradiction
        rename_i m n' _
        clear m
        rw [int.of_nat.pos n', int.mul.lift_nat]
        rw [←@int.neg.pos_succ n, int.of_nat.pos n,
          ←int.mul.neg_left, int.mul.lift_nat]
        rw [neg_pos_compare, neg_pos_compare]

        rw [int.of_nat.zero]
        apply TotalOrder.lt_of_compare
        rw [int.of_nat.compare]
        apply TotalOrder.compare_of_lt
        rw [nat.succ_mul]
        apply nat.lt_of_lt_of_le _ (nat.add.le_left _ _)
        rw [nat.gcd.comm]
        apply gcd_pos <;> trivial

        rw [←int.neg.zero]
        apply int.neg.swap_lt.mp

        rw [int.of_nat.zero]
        apply TotalOrder.lt_of_compare
        rw [int.of_nat.compare]
        apply TotalOrder.compare_of_lt
        rw [nat.succ_mul]
        apply nat.lt_of_lt_of_le _ (nat.add.le_left _ _)
        rw [nat.gcd.comm]
        apply gcd_pos <;> trivial

        apply TotalOrder.lt_of_compare
        rw [int.mul.pos_pos_is_pos _ _]
        trivial
        trivial

        apply TotalOrder.lt_of_compare
        rw [int.mul.neg_pos_is_neg _ _]
        trivial
        trivial

      · rename_i bnum
        have := gcd_ne_zero bnum bden bden_nz
        rw [int.abs.neg_succ]
        rw [int.sign.neg]
        dsimp
        split
        contradiction
        rename_i m n' h'
        clear m
        repeat rw [←int.neg.pos_succ]
        repeat rw [int.of_nat.pos]
        repeat rw [←int.mul.neg_left]
        rw [int.neg.swap_cmp, int.neg.swap_cmp]
        rw [←h, ←h']
        repeat rw [int.mul.lift_nat]
        rw [int.of_nat.compare, int.of_nat.compare]
        clear h' h this
        clear this gcd_ne_zero of_nat_one n n'
        rw [nat.dvd.mul_div, nat.dvd.mul_div,
           nat.mul.comm (_ / _),  nat.mul.comm (_ / _),
           nat.dvd.mul_div, nat.dvd.mul_div]
        any_goals apply nat.gcd.dvd_left
        any_goals apply nat.gcd.dvd_right
        rw [nat.div_div, nat.div_div, nat.mul.comm (nat.gcd _ _),
          nat.div.compare_strict, nat.mul.comm bden, nat.mul.comm bnum.succ]
        apply Decidable.byContradiction
        intro h
        replace h := nat.le_zero (TotalOrder.le_of_not_lt h)
        cases nat.mul.eq_zero h <;> rename_i h <;> cases nat.gcd.eq_zero h
        contradiction
        contradiction
        apply nat.dvd.mul
        apply nat.gcd.dvd_right
        apply nat.gcd.dvd_left
        rw [nat.mul.comm]
        apply nat.dvd.mul
        apply nat.gcd.dvd_right
        apply nat.gcd.dvd_left

#print axioms rat.compare_of_fract

def fract.add.compare_strict { a b: fract } { o: Ordering } :
   compare a c = o ->
   compare b d = o ->
   compare (a + b) (c + d) = o := by
    intro ab cd
    rw [fract.add.def, fract.add.def, fract.compare_def, order]
    dsimp
    repeat rw [←int.mul.lift_nat]
    cases a with | mk anum aden aden_pos =>
    cases b with | mk bnum bden bden_pos =>
    cases c with | mk cnum cden cden_pos =>
    cases d with | mk dnum dden dden_pos =>
    dsimp
    cases aden with
    | zero => contradiction
    | succ aden =>
    cases bden with
    | zero => contradiction
    | succ bden =>
    cases cden with
    | zero => contradiction
    | succ cden =>
    cases dden with
    | zero => contradiction
    | succ dden =>
    rw [fract.compare_def, order] at ab cd
    dsimp at ab cd
    clear aden_pos bden_pos cden_pos dden_pos
    repeat rw [←int.of_nat.pos]
    rw [int.mul.add_left, int.mul.add_left,
      @int.mul.comm _ bnum, @int.mul.comm _ dnum]
    repeat rw [int.mul.assoc]
    apply int.add.compare_strict
    rw [int.mul.comm_left (int.pos_succ bden), int.mul.comm_left (int.pos_succ dden),
      @int.mul.comm (int.pos_succ dden)]
    rw [←@int.mul.assoc anum, ←@int.mul.assoc cnum]
    rw [←int.mul.compare_left_pos]
    assumption
    trivial
    rw [int.mul.comm_right (int.pos_succ aden), int.mul.comm_right (int.pos_succ cden),
      @int.mul.comm (int.pos_succ cden)]
    rw [←@int.mul.assoc bnum, ←@int.mul.assoc dnum]
    rw [←int.mul.compare_left_pos]
    assumption
    trivial

def rat.add.compare_strict { a b c d: rat } { o: Ordering } :
   compare a b = o ->
   compare c d = o ->
   compare (a + c) (b + d) = o := by
   intro ab cd
   erw [←rat.compare_of_fract]
   apply fract.add.compare_strict
   assumption
   assumption

#print axioms rat.add.compare_strict
