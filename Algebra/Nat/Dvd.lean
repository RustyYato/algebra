import Algebra.Nat.Div

def nat.dvd (a b: nat) := ∃k: nat, a * k = b

instance nat.dvd_inst : Dvd nat where
  dvd := nat.dvd

def nat.dvd.zero (a: nat) : a ∣ 0 := by
  exists 0
  rw [mul_zero]

#print axioms nat.dvd.zero

def nat.dvd.by_one (b: nat) : 1 ∣ b := by
  exists b
  rw [one_mul]

#print axioms nat.dvd.by_one

def nat.dvd.refl (a: nat) : a ∣ a := by
  exists 1
  rw [mul_one]

#print axioms nat.dvd.refl

def nat.dvd.mul_left (a b: nat) : a ∣ a * b := by
  exists b

#print axioms nat.dvd.mul_left

def nat.dvd.mul_right (a b: nat) : a ∣ b * a := by
  exists b
  rw [mul.comm]

#print axioms nat.dvd.mul_right

def nat.dvd.eq_zero_of_by_zero {b: nat} : 0 ∣ b -> b = 0 := by
  match b with
  | .zero => intro; rfl
  | .succ _ =>
    intro zero_dvd
    have ⟨ k, prf ⟩ := zero_dvd
    rw [zero_mul] at prf
    contradiction

#print axioms nat.dvd.eq_zero_of_by_zero

def nat.dvd.eq_one_of_by_one (a: nat) : a ∣ 1 -> a = 1 := by
  intro a_dvd_one
  have ⟨ x, xprf ⟩ := a_dvd_one
  have ⟨ _, _ ⟩ := nat.mul.eq_one xprf
  assumption

#print axioms nat.dvd.eq_one_of_by_one

def nat.dvd.trans { a b c: nat } : a ∣ b -> b ∣ c -> a ∣ c := by
  intros a_dvd_b b_dvd_c
  have ⟨ x, xdef ⟩ := a_dvd_b
  have ⟨ y, ydef ⟩ := b_dvd_c
  exists x * y
  rw [←mul.assoc, xdef, ydef]

#print axioms nat.dvd.trans

inductive FindDivisor (a b: nat) where
  | Found : a ∣ b -> FindDivisor a b
  | NotFound : (∀k, a * k ≠ b) -> FindDivisor a b

def nat.find_divisor (a b: nat) (n: nat) (prev: ∀k, n < k -> a * k ≠ b) : FindDivisor a b := by
  match decEq (a * n) b with
    | .isTrue h =>
      apply FindDivisor.Found
      exists n
    | .isFalse h =>
       match n with
       | .zero =>
         apply FindDivisor.NotFound
         intro k
         match k with
         | .zero =>
          assumption
         | .succ k =>
          apply prev
          rfl
        | .succ n =>
          apply nat.find_divisor a b n
          intro k n_lt_k
          match k with
          | .zero =>
            have := not_lt_zero n_lt_k
            contradiction
          | .succ k =>
            match lt_or_eq_of_le <| le_of_lt_succ n_lt_k with
            | .inl n_lt_k => exact prev k.succ n_lt_k
            | .inr n_eq_k =>
              rw [←n_eq_k]
              assumption

#print axioms nat.find_divisor

instance nat.dvd.dec (a b: nat) : Decidable (a ∣ b) := by
  match b with
  | .zero =>
    apply Decidable.isTrue
    apply dvd.zero
  | .succ b =>
  have := nat.find_divisor a b.succ b.succ (by
    intro k b_lt_k ak_eq_b
    match k with
    | .zero =>
      have := not_lt_zero b_lt_k
      contradiction
    | .succ k =>
    match a with
    | .zero =>
      rw [zero_eq, zero_mul] at ak_eq_b
      contradiction
    | .succ a =>
    have := nat.mul.ge k.succ a.succ rfl
    rw [mul.comm] at this
    rw [←ak_eq_b] at b_lt_k
    exact not_lt_and_ge b_lt_k this
    )
  match this with
  | .Found h => exact Decidable.isTrue h
  | .NotFound h =>
    apply Decidable.isFalse
    intro dvd
    have ⟨ k, prf ⟩ := dvd
    have := h k
    contradiction

#print axioms nat.dvd.dec

def nat.dvd.le { a b: nat } ( b_nz: 0 < b ) (a_dvd_b: a ∣ b) : a ≤ b := by
  match b with
  | .succ b =>
  have ⟨ k, prf ⟩ := a_dvd_b
  clear b_nz
  match k with
  | .zero =>
    rw [zero_eq, mul_zero] at prf
    contradiction
  | .succ k =>
  match a with
  | .zero =>
    rw [zero_eq, zero_mul] at prf
    contradiction
  | .succ a =>
    have := mul.ge a.succ k.succ rfl
    rw [prf] at this
    exact this

#print axioms nat.dvd.le

def nat.dvd.antisymm { a b: nat } : a ∣ b -> b ∣ a -> a = b := by
  intro a_dvd_b b_dvd_a
  match b with
  | .zero =>
    have := eq_zero_of_by_zero b_dvd_a
    rw [this]
    rfl
  | .succ b =>
  match a with
  | .zero =>
    have := eq_zero_of_by_zero a_dvd_b
    rw [this]
    rfl
  | .succ a =>
  apply le_antisymm
  exact nat.dvd.le rfl a_dvd_b
  exact nat.dvd.le rfl b_dvd_a

#print axioms nat.dvd.antisymm

def nat.dvd.add { a b c: nat } : a ∣ (b + c) -> a ∣ b -> a ∣ c := by
  intro a_dvd_bc a_dvd_b
  have ⟨ x, x_prf ⟩ := a_dvd_bc
  have ⟨ y, y_prf ⟩ := a_dvd_b
  rw [←y_prf] at x_prf
  clear a_dvd_b a_dvd_bc y_prf
  exists (x - y)
  rw [nat.mul_sub, x_prf]
  rw [add.comm, ←add_sub, sub.refl, add_zero]
  apply nat.le_refl

#print axioms nat.dvd.add

def nat.dvd.sub { a b: nat } : a ≤ b -> a ∣ b -> a ∣ (b - a) := by
  intro a_le_b a_dvd_b
  have ⟨ k, prf ⟩ := a_dvd_b
  match k with
  | .zero =>
    rw [zero_eq, mul_zero] at prf
    rw [←prf] at a_dvd_b a_le_b
    rw [←prf]
    rw [le_zero a_le_b]
    exists 0
  | .succ k =>
    exists k
    rw [←prf]
    rw [mul_succ, add.comm, ←add_sub, sub.refl, add_zero]
    exact le_refl _

#print axioms nat.dvd.sub

def nat.dvd.mod_eq_zero: ∀{ a b: nat }, b ∣ a -> a % b = 0 := by
  intro a b
  cases b with
  | zero => intros; rfl
  | succ b =>
  intro succ_b_dvd_a
  apply nat.div_mod.induction (fun a b _ => b ∣ a -> a % b = 0)
  {
    intro a b a_lt_b b_dvd_a
    rw [nat.mod.if_lt]
    cases a with
    | zero => rfl
    | succ a =>
      apply False.elim <| TotalOrder.not_lt_and_ge a_lt_b _
      exact nat.dvd.le zero_lt_succ b_dvd_a
    apply zero_lt_of_lt a_lt_b
    assumption
  }
  {
    intro a b b_nz a_ge_b ih b_dvd_a
    cases a with
      | zero => rw [zero_eq, nat.zero_mod]
      | succ a =>
      rw [nat.mod.if_ge]
      apply ih
      apply nat.dvd.sub
      apply nat.dvd.le zero_lt_succ b_dvd_a
      repeat assumption
  }
  apply zero_lt_succ
  assumption

#print axioms nat.dvd.mod_eq_zero

def nat.dvd.of_mod_eq_zero: ∀{ a b: nat }, 0 < b -> a % b = 0 -> b ∣ a := by
  intro a b b_nz a_mod_b_eq_zero
  have := nat.div_def a b b_nz
  rw [a_mod_b_eq_zero, add_zero] at this
  rw [this]
  apply nat.dvd.mul_right

#print axioms nat.dvd.of_mod_eq_zero

def nat.dvd.def { a b: nat } : b ∣ a -> a = (a / b) * b := by
  match b with
  | .zero =>
    intro zero_dvd_a
    rw [eq_zero_of_by_zero zero_dvd_a]
    rfl
  | .succ b =>
  intro b_dvd_a
  have := nat.div_def a b.succ zero_lt_succ
  rw [nat.dvd.mod_eq_zero, add_zero] at this
  exact this
  assumption

#print axioms nat.dvd.def

def nat.dvd.mod { a b c: nat } : c ∣ a -> c ∣ b -> c ∣ (a % b) := by
  intro c_dvd_a c_dvd_b
  have ⟨ x, x_def ⟩ := c_dvd_a
  have ⟨ y, y_def ⟩ := c_dvd_b
  cases b with
  | zero => apply dvd.zero
  | succ b =>
    have := div_def a b.succ zero_lt_succ
    rw [←y_def, ←x_def] at this
    rw [←mul.assoc, mul.comm _ c, mul.assoc] at this
    exists x - (c * x / (c * y) * y)
    rw [mul_sub]
    rw [x_def]
    rw [←mul.assoc, mul.comm, ←mul.assoc, mul.comm _ c]
    rw [y_def]
    clear this y_def x_def y x
    have := div_def a b.succ zero_lt_succ
    conv => {
      lhs
      lhs
      rw [this]
    }
    rw [add.comm, ←add_sub, mul.comm, sub.refl, add_zero]
    rw [mul.comm]
    apply TotalOrder.le_refl

#print axioms nat.dvd.mod

def nat.dvd.of_mod { a b c: nat } : 0 < b -> c ∣ b -> c ∣ (a % b) -> c ∣ a := by
  intro zero_lt_b c_dvd_a c_dvd_ab
  rw [nat.div_def a b]
  have ⟨ x, xdef ⟩ := c_dvd_a
  have ⟨ y, ydef ⟩ := c_dvd_ab
  exists a / b * x + y
  rw [mul_add, ←mul.assoc, mul.comm _ x, ←mul.assoc, ydef, mul.comm _ c, xdef, mul.comm]
  assumption

#print axioms nat.dvd.of_mod

def nat.dvd.of_mul : ∀(a b k: nat), (k * a) ∣ b -> k ∣ b ∧ a ∣ b := by
  intro a b k ka_dvd_b
  have ⟨ x, xprf ⟩ := ka_dvd_b
  apply And.intro
  exists a * x
  rw [←nat.mul.assoc]
  assumption
  exists k * x
  rw [←nat.mul.assoc,  nat.mul.comm a]
  assumption

#print axioms nat.dvd.of_mul

def nat.dvd.mul : ∀(a b c d: nat), a ∣ c -> b ∣ d -> a * b ∣ c * d := by
  rintro a b c d ⟨ x, prfx ⟩ ⟨ y, prfy ⟩
  exists x * y
  rw [←prfx, ←prfy, mul.assoc, ←mul.assoc b, nat.mul.comm b, nat.mul.assoc, ←nat.mul.assoc]

#print axioms nat.dvd.mul

def nat.mul_div (a b: nat) : 0 < a -> (a * b) / a = b := by
  intro a_nz
  have := nat.div_def (a * b) a a_nz
  rw [nat.dvd.mod_eq_zero, nat.add_zero, mul.comm _ a] at this
  apply eq_of_mul_eq
  assumption
  exact this.symm
  apply nat.dvd.mul_left

#print axioms nat.mul_div

def nat.dvd.of_div : ∀(a b k: nat), k ∣ a -> a ∣ b -> (a / k) ∣ (b / k) := by
  intro a b k k_dvd_a a_dvd_b
  cases k with
  | zero => apply dvd.refl
  | succ k =>
  have ⟨ x, xprf ⟩ := k_dvd_a
  have ⟨ y, yprf ⟩ := a_dvd_b
  exists y
  rw [←yprf]
  rw [←xprf]
  rw [mul_div, mul.assoc, mul_div]
  apply zero_lt_succ
  apply zero_lt_succ

#print axioms nat.dvd.of_div

def nat.div.self { a: nat }: 0 < a -> a / a = 1 := by
  intro a_nz
  have def_a := nat.dvd.def (dvd.refl a)
  conv at def_a => {
    lhs
    rw [←one_mul a]
  }
  apply Eq.symm
  apply mul.cancel_right
  assumption
  assumption

#print axioms nat.div.self

def nat.div.compare_strict (a b c: nat) :
  0 < c ->
  c ∣ a ->
  c ∣ b ->
  compare (a / c) (b / c) = compare a b := by
  intro c_pos
  apply nat.div_mod.induction (fun a c _ => ∀b, c ∣ a -> c ∣ b -> compare (a / c) (b / c) = compare a b) _ _ a c c_pos
  all_goals clear a b c_pos c
  · intro a c a_lt_c b c_dvd_a c_dvd_b
    have : 0 < c := nat.lt_of_le_of_lt (nat.zero_le _) a_lt_c
    cases a with
    | succ a =>
      have := fun h => nat.dvd.le h c_dvd_a
      have := this nat.zero_lt_succ
      have := nat.not_lt_and_ge a_lt_c this
      contradiction
    | zero =>
      rw [nat.zero_eq, nat.zero_div]
      rw [nat.div.spec]
      split
      · cases b with
        | succ b =>
          have := fun h => nat.dvd.le h c_dvd_b
          have := this nat.zero_lt_succ
          have := nat.not_lt_and_ge (by assumption) this
          contradiction
        | zero =>
          rfl
      · rename_i b_ge_c
        have := TotalOrder.le_of_not_lt b_ge_c
        have := TotalOrder.lt_of_lt_of_le (by assumption) this
        rw [nat.zero_eq] at this
        rw [this]
        rfl
      · assumption
  · intro a c c_pos a_ge_c ih b c_dvd_a c_dvd_b
    rw [nat.div.if_ge]
    · cases b with
      | zero =>
        rw [nat.zero_eq, nat.zero_div]
        rw [TotalOrder.swap_compare rfl, nat.zero_lt_succ, Ordering.swap]
        dsimp
        apply Eq.symm
        apply TotalOrder.compare_of_gt
        apply nat.lt_of_lt_of_le c_pos
        assumption
      | succ b =>
        rw [nat.div.spec b.succ]
        split
        rw [TotalOrder.swap_compare nat.zero_lt_succ, Ordering.swap]
        dsimp
        apply Eq.symm
        apply TotalOrder.compare_of_gt
        apply nat.lt_of_lt_of_le <;> assumption
        have c_le_bsucc := TotalOrder.le_of_not_lt (by assumption)
        rw [nat.compare.succ]
        rw [ih]
        · rw [nat.sub.compare_strict]
          assumption
          assumption
        exact dvd.sub a_ge_c c_dvd_a
        apply dvd.sub c_le_bsucc c_dvd_b
        assumption
    · assumption
    · assumption
