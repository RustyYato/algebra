import Algebra.Rat.Basic

def fract.order (a b: fract) : Ordering := compare (a.num * int.of_nat b.den) (b.num * int.of_nat a.den)
def rat.order (a b: rat) : Ordering := compare (a.num * int.of_nat b.den) (b.num * int.of_nat a.den)

instance fract.OrdInst : Ord fract := ⟨ order ⟩
instance rat.OrdInst : Ord rat := ⟨ order ⟩

instance : LT fract where
  lt a b := compare a b = Ordering.lt
instance : LE fract where
  le a b := compare a b = Ordering.lt ∨ compare a b = Ordering.eq

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
      rw [int.mul.assoc, int.mul.comm b, ←int.mul.assoc]
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
def rat.compare_def (a b: rat) : compare a b = order a b := rfl

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
      int.mul.comm _ bnum, int.mul.comm _ dnum]
    repeat rw [int.mul.assoc]
    apply int.add.compare_strict
    rw [int.mul.comm_left (int.pos_succ bden), int.mul.comm_left (int.pos_succ dden),
      int.mul.comm (int.pos_succ dden)]
    rw [←int.mul.assoc anum, ←int.mul.assoc cnum]
    rw [←int.mul.compare_left_pos]
    assumption
    trivial
    rw [int.mul.comm_right (int.pos_succ aden), int.mul.comm_right (int.pos_succ cden),
      int.mul.comm (int.pos_succ cden)]
    rw [←int.mul.assoc bnum, ←int.mul.assoc dnum]
    rw [←int.mul.compare_left_pos]
    assumption
    trivial

def fract.add.compare_left { a b k: fract } { o: Ordering } :
   compare a b = o ->
   compare (k + a) (k + b) = o := by
    intro ab
    cases a with | mk anum aden aden_pos =>
    cases b with | mk bnum bden bden_pos =>
    cases k with | mk knum kden kden_pos =>
    repeat rw [fract.add.def]
    rw [compare_def, order]
    dsimp
    cases aden with
    | zero => contradiction
    | succ aden =>
    cases bden with
    | zero => contradiction
    | succ bden =>
    cases kden with
    | zero => contradiction
    | succ kden =>
    repeat rw [←int.mul.lift_nat]
    repeat rw [←int.of_nat.pos]
    rw [compare_def, order] at ab
    dsimp at ab
    rw [int.mul.add_left, int.mul.add_left,
      int.mul.comm _ anum, int.mul.comm _ bnum,
      int.mul.assoc, int.mul.assoc, int.mul.assoc, int.mul.assoc,
      int.mul.comm_right (int.pos_succ kden),
      int.mul.comm_right (int.pos_succ kden),
      int.mul.comm (int.pos_succ kden) (int.pos_succ aden),
      int.mul.comm (int.pos_succ kden) (int.pos_succ bden),
      int.mul.comm_left (int.pos_succ bden) (int.pos_succ aden)]
    repeat rw [←int.mul.assoc]
    rw [←int.add.compare_right]
    rw [int.mul.assoc, int.mul.assoc _ _ (int.pos_succ _)]
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

def rat.add.compare_left { a b k: rat } { o: Ordering } :
   compare a b = o ->
   compare (k + a) (k + b) = o := by
   intro ab
   erw [←rat.compare_of_fract]
   apply fract.add.compare_left
   assumption

#print axioms rat.add.compare_strict

def rat.add.compare_right { a b k: rat } { o: Ordering } :
   compare a b = o ->
   compare (a + k) (b + k) = o := by
   intro ab
   rw [rat.add.comm _ k, rat.add.comm _ k]
   apply rat.add.compare_left
   assumption

#print axioms rat.add.compare_strict

def rat.add.compare' { a b c d: rat } { o: Ordering } :
   compare a b = o ∨ a = b ->
   compare c d = o ∨ c = d ->
   ¬((a = b) ∧ (c = d)) ->
   compare (a + c) (b + d) = o := by
    intro ab cd h
    cases ab <;> rename_i ab <;> cases cd <;> rename_i cd
    · apply rat.add.compare_strict <;> assumption
    · subst d
      apply rat.add.compare_right
      assumption
    · subst b
      apply rat.add.compare_left
      assumption
    · have := h ⟨ ab, cd ⟩
      contradiction

#print axioms rat.add.compare'

def rat.add.lt_of_add_left { a b k: rat } :
  a < b ->
  k + a < k + b := by
  intro ab
  apply rat.add.compare_left
  assumption

def rat.add.lt_of_add_right { a b k: rat } :
  a < b ->
  a + k < b + k := by
  intro ab
  rw [add.comm _ k, add.comm _ k]
  apply rat.add.lt_of_add_left
  assumption

def rat.add.le_of_add_left { a b k: rat } :
  a ≤ b ->
  k + a ≤ k + b := by
  intro ab
  cases ab
  apply Or.inl
  apply rat.add.compare_left
  assumption
  cases TotalOrder.eq_of_compare_eq (by assumption)
  apply TotalOrder.le_refl

def rat.add.le_of_add_right { a b k: rat } :
  a ≤ b ->
  a + k ≤ b + k := by
  intro ab
  rw [add.comm _ k, add.comm _ k]
  apply rat.add.le_of_add_left
  assumption

def rat.add.le_of_le { a b c d: rat } :
  a ≤ b -> c ≤ d ->
  a + c ≤ b + d := by
  intro ab cd
  apply TotalOrder.le_trans
  apply rat.add.le_of_add_left
  assumption
  apply rat.add.le_of_add_right
  assumption

def rat.add.lt_of_lt { a b c d: rat } :
  a < b -> c < d ->
  a + c < b + d := by
  intro ab cd
  apply TotalOrder.lt_trans
  apply rat.add.lt_of_add_left
  assumption
  apply rat.add.lt_of_add_right
  assumption

def rat.add.lt_of_le_of_lt { a b c d: rat } :
  a ≤ b -> c < d ->
  a + c < b + d := by
  intro ab cd
  apply TotalOrder.lt_of_le_of_lt
  apply rat.add.le_of_add_right
  assumption
  apply rat.add.lt_of_add_left
  assumption

def rat.add.lt_of_lt_of_le { a b c d: rat } :
  a < b -> c ≤ d ->
  a + c < b + d := by
  intro ab cd
  apply TotalOrder.lt_of_lt_of_le
  apply rat.add.lt_of_add_right
  assumption
  apply rat.add.le_of_add_left
  assumption

def rat.neg.swap_cmp (a b: rat) :
  compare (-a) (-b) = compare b a := by
  rw [neg.def, neg.def]
  unfold Ord.compare OrdInst order
  dsimp
  cases a with | mk anum aden aden_pos ared =>
  cases b with | mk bnum bden bden_pos bred =>
  dsimp
  clear ared bred
  have cmp_0_pos : ∀x n, 0 < n -> compare 0 (int.pos_succ x * int.of_nat n) = Ordering.lt := by
    intros x n n_pos
    cases n
    contradiction
    rfl
  have cmp_pos_0 : ∀x n, 0 < n -> compare (int.pos_succ x * int.of_nat n) 0 = Ordering.gt := by
    intros x n n_pos
    cases n
    contradiction
    rfl
  have cmp_0_neg : ∀x n, 0 < n -> compare 0 (int.neg_succ x * int.of_nat n) = Ordering.gt := by
    intros x n n_pos
    cases n
    contradiction
    rfl
  have cmp_neg_0 : ∀x n, 0 < n -> compare (int.neg_succ x * int.of_nat n) 0 = Ordering.lt := by
    intros x n n_pos
    cases n
    contradiction
    rfl
  have cmp_neg_pos : ∀x n y m, 0 < n -> 0 < m -> compare (int.neg_succ x * int.of_nat n) (int.pos_succ y * int.of_nat m) = Ordering.lt := by
    intros x n y m n_pos m_pos
    cases n
    contradiction
    cases m
    contradiction
    rfl
  have cmp_pos_neg : ∀x n y m, 0 < n -> 0 < m -> compare (int.pos_succ y * int.of_nat m) (int.neg_succ x * int.of_nat n) = Ordering.gt := by
    intros x n y m n_pos m_pos
    cases n
    contradiction
    cases m
    contradiction
    rfl

  cases anum <;> cases bnum
  any_goals rw [int.zero_eq]
  all_goals repeat first|rw [←int.neg.def]|rw[int.neg.zero]|rw[int.neg.pos_succ]|rw[int.neg.neg_succ]
  all_goals repeat rw [int.mul.zero_left]
  any_goals rw [cmp_0_pos]
  any_goals rw [cmp_0_neg]
  any_goals rw [cmp_neg_0]
  any_goals rw [cmp_pos_0]
  any_goals assumption
  any_goals rw [cmp_pos_neg, cmp_pos_neg]
  any_goals rw [cmp_neg_pos, cmp_neg_pos]
  any_goals assumption
  · rw [←int.neg.pos_succ, ←int.neg.pos_succ,
      ←int.mul.neg_left, ←int.mul.neg_left,
      int.neg.swap_cmp]
  · rw [←int.neg.pos_succ, ←int.neg.pos_succ,
      ←int.mul.neg_left, ←int.mul.neg_left,
      int.neg.swap_cmp]

def fract.mul.pos_left (k a b: fract) :
  0 < k -> compare (k * a) (k * b) = compare a b := by
  intro k_pos
  rw [mul.def, mul.def]
  unfold mul
  rw [compare_def, compare_def]
  unfold order
  dsimp
  rw [←int.mul.lift_nat, ←int.mul.lift_nat,
      int.mul.comm k.num a.num, int.mul.comm k.num b.num,
      int.mul.assoc, int.mul.assoc,
      int.mul.comm_right k.num, int.mul.comm_right k.num,
      ←int.mul.assoc a.num, ←int.mul.assoc b.num, ←int.mul.compare_left_pos]
  dsimp
  apply int.mul.pos_pos_is_pos
  have : 0 = int.of_nat 0 := rfl
  apply TotalOrder.lt_of_compare
  erw [this, int.of_nat.compare 0 k.den]
  exact k.den_nz
  have cmp : compare 0 k = Ordering.lt := k_pos
  unfold compare OrdInst order at cmp
  dsimp at cmp
  erw [int.mul.zero_left, int.mul.one_right] at cmp
  assumption

def rat.neg.swap_lt (a b: rat) :
  a < b ->
  -b < -a := by
  intro h
  apply TotalOrder.lt_of_compare
  rw [neg.swap_cmp]
  assumption

def rat.mul.compare_pos_left (k a b: rat) :
  0 < k -> compare (k * a) (k * b) = compare a b := by
  intro k_pos
  erw [←rat.compare_of_fract]
  apply fract.mul.pos_left
  assumption

def rat.mul.compare_pos_right (k a b: rat) :
  0 < k -> compare (a * k) (b * k) = compare a b := by
  intro k_pos
  rw [mul.comm _ k, mul.comm _ k]
  apply mul.compare_pos_left
  assumption

def rat.mul.compare_neg_left (k a b: rat) :
  k < 0 -> compare (k * a) (k * b) = compare b a := by
  intro k_neg
  rw [←rat.neg_neg k]
  repeat rw [neg_left (-_)]
  rw [rat.neg.swap_cmp]
  rw [rat.mul.compare_pos_left]
  rw [←rat.neg.zero]
  apply neg.swap_lt
  assumption

def rat.mul.compare_neg_right (k a b: rat) :
  k < 0 -> compare (a * k) (b * k) = compare b a := by
  intro k_neg
  rw [mul.comm _ k, mul.comm _ k]
  apply mul.compare_neg_left
  assumption

def rat.mul.pos_pos_is_pos (a b: rat) :
  0 < a -> 0 < b -> 0 < a * b := by
  intro a_pos b_pos
  apply TotalOrder.lt_of_compare
  rw [←mul.zero_left b, compare_pos_right]
  assumption
  assumption

def rat.mul.neg_pos_is_neg (a b: rat) :
  a < 0 -> 0 < b -> a * b < 0 := by
  intro a_pos b_pos
  apply TotalOrder.lt_of_compare
  rw [←mul.zero_left b, compare_pos_right]
  assumption
  assumption

def rat.mul.pos_neg_is_neg (a b: rat) :
  0 < a -> b < 0 -> a * b < 0 := by
  intro a_pos b_pos
  apply TotalOrder.lt_of_compare
  rw [←mul.zero_right a, compare_pos_left]
  assumption
  assumption

def rat.mul.neg_neg_is_pos (a b: rat) :
  a < 0 -> b < 0 -> 0 < a * b := by
  intro a_neg b_neg
  apply TotalOrder.lt_of_compare
  rw [←mul.zero_right a, compare_neg_left]
  assumption
  assumption

def rat.mul.lt_pos_left (a b k: rat) :
  a < b -> 0 < k -> k * a < k * b := by
  intro a_neg b_neg
  apply TotalOrder.lt_of_compare
  rw [compare_pos_left]
  assumption
  assumption

def rat.mul.lt_neg_left (a b k: rat) :
  a < b -> k < 0 -> k * b < k * a := by
  intro a_neg b_neg
  apply TotalOrder.lt_of_compare
  rw [compare_neg_left]
  assumption
  assumption

def rat.mul.le_pos_left (a b k: rat) :
  a ≤ b -> 0 < k -> k * a ≤ k * b := by
  intro a_neg b_neg
  apply TotalOrder.le_of_compare
  rw [compare_pos_left]
  assumption
  assumption

def rat.mul.le_neg_left (a b k: rat) :
  a ≤ b -> k < 0 -> k * b ≤ k * a := by
  intro a_neg b_neg
  apply TotalOrder.le_of_compare
  rw [compare_neg_left]
  assumption
  assumption

def rat.mul.lt_pos_right (a b k: rat) :
  a < b -> 0 < k -> a * k < b * k := by
  intro a_neg b_neg
  apply TotalOrder.lt_of_compare
  rw [compare_pos_right]
  assumption
  assumption

def rat.mul.lt_neg_right (a b k: rat) :
  a < b -> k < 0 -> b * k < a * k := by
  intro a_neg b_neg
  apply TotalOrder.lt_of_compare
  rw [compare_neg_right]
  assumption
  assumption

def rat.mul.le_pos_right (a b k: rat) :
  a ≤ b -> 0 < k -> a * k ≤ b * k := by
  intro a_neg b_neg
  apply TotalOrder.le_of_compare
  rw [compare_pos_right]
  assumption
  assumption

def rat.mul.le_neg_right (a b k: rat) :
  a ≤ b -> k < 0 -> b * k ≤ a * k := by
  intro a_neg b_neg
  apply TotalOrder.le_of_compare
  rw [compare_neg_right]
  assumption
  assumption

def rat.abs.not_gt (a: rat) :
  ¬(0 > a.abs) := by
  cases a with | mk n d d_pos red =>
  rw [abs]
  dsimp
  intro h
  replace h := TotalOrder.compare_of_gt h
  rw [compare_def, order] at h
  dsimp at h
  erw [int.mul.zero_left, int.mul.one_right] at h
  rw [int.of_nat.zero, int.of_nat.compare] at h
  replace h := TotalOrder.gt_of_compare h
  exact nat.not_lt_zero h

def rat.abs.nonneg (a: rat) :
  0 ≤ a.abs := by
  apply TotalOrder.le_of_not_gt
  apply rat.abs.not_gt

def rat.div.pos_of_gt_one (a b: rat) :
  1 < b -> 0 < a -> a / b < a := by
  intro b_gt_one a_pos
  rw [div.def]
  conv => { rhs; rw [←mul.one_right a] }
  apply TotalOrder.lt_of_compare
  rw [mul.compare_pos_left]
  rw [←mul.compare_pos_left b, mul.inv_right, mul.one_right]
  any_goals assumption
  intro h
  cases h
  contradiction
  apply TotalOrder.lt_trans _ b_gt_one
  trivial

def rat.div.neg_of_gt_one (a b: rat) :
  1 < b -> a < 0 -> a < a / b := by
  intro b_gt_one a_pos
  rw [div.def]
  conv => { lhs; rw [←mul.one_right a] }
  apply TotalOrder.lt_of_compare
  rw [mul.compare_neg_left]
  rw [←mul.compare_pos_left b, mul.inv_right, mul.one_right]
  any_goals assumption
  intro h
  cases h
  contradiction
  apply TotalOrder.lt_trans _ b_gt_one
  trivial

def rat.add.midpoint (a b: rat) :
  a < b ->
  a < (a + b) / 2 ∧ (a + b) / 2 < b := by
  intro a_lt_b
  rw [div.def, add.mul_right, ←div.def, ←div.def]
  apply And.intro
  · apply flip TotalOrder.lt_of_le_of_lt
    · apply add.lt_of_le_of_lt
      · apply TotalOrder.le_refl
      · rw [div.def]
        apply TotalOrder.lt_of_compare
        rw [mul.compare_pos_right]
        assumption
        trivial
    · rw [div.def, ←add.mul_right, ←mul_two, mul.assoc, mul.inv_right, mul.one_right]
      trivial
  · apply TotalOrder.lt_of_lt_of_le
    · apply add.lt_of_lt_of_le
      · rw [div.def]
        apply TotalOrder.lt_of_compare
        rw [mul.compare_pos_right]
        assumption
        trivial
      · apply TotalOrder.le_refl
    · rw [div.def, ←add.mul_right, ←mul_two, mul.assoc, mul.inv_right, mul.one_right]
      trivial

def fract.abs.tri (a b: fract) : fract.abs (a + b) ≤ fract.abs a + fract.abs b := by
  cases a with | mk anum aden aden_pos =>
  cases b with | mk bnum bden bden_pos =>
  repeat rw [add.def]
  repeat rw [abs]
  dsimp
  unfold LE.le instLEFract compare OrdInst order
  dsimp
  have : 0 < int.of_nat aden := by cases aden; contradiction; rfl
  have : 0 < int.of_nat bden := by cases bden; contradiction; rfl
  suffices compare (int.of_nat (anum * int.of_nat bden + int.of_nat aden * bnum).abs * int.of_nat (aden * bden))
      ((int.of_nat anum.abs * int.of_nat bden + int.of_nat aden * int.of_nat bnum.abs) * int.of_nat (aden * bden)) ≠ Ordering.gt from by
        cases h:compare (int.of_nat (anum * int.of_nat bden + int.of_nat aden * bnum).abs * int.of_nat (aden * bden)) ((int.of_nat anum.abs * int.of_nat bden + int.of_nat aden * int.of_nat bnum.abs) * int.of_nat (aden * bden))
        exact Or.inl rfl
        exact Or.inr rfl
        contradiction
  intro h
  rw [←int.mul.compare_left_pos] at h
  · cases anum <;> cases bnum
    all_goals repeat (
      first|
      erw [int.zero_eq] at h|
      erw [int.mul.zero_left] at h|
      erw [int.mul.zero_right] at h|
      rw [int.add.zero_left] at h|
      rw [int.add.zero_right] at h|
      rw [int.abs.zero] at h
    )
    · contradiction
    any_goals rw [int.abs.mul] at h
    any_goals repeat rw [int.abs.of_nat] at h
    any_goals repeat rw [int.abs.pos_succ] at h
    any_goals repeat rw [int.abs.neg_succ] at h
    any_goals rw [←int.mul.lift_nat] at h
    any_goals rw [int.pos_succ.of_nat] at h
    any_goals rw [TotalOrder.compare_eq_refl] at h
    any_goals contradiction
    all_goals rename_i a b
    all_goals rw [int.pos_succ.of_nat] at h
    ·
      sorry
    · sorry
    · sorry
    · sorry
  · rw [←int.mul.lift_nat]
    apply int.mul.pos_pos_is_pos <;> assumption

def rat.abs.tri (a b: rat) : rat.abs (a + b) ≤ rat.abs a + rat.abs b := by
  rw [add.def, add.def, fract.abs.to_rat]
  apply TotalOrder.le_of_compare
  erw [←compare_of_fract]
  apply fract.abs.tri
