import Algebra.Nat.Gcd

def nat.prime (p: nat) := 1 < p ∧ ∀k, k ∣ p -> k = 1 ∨ k = p

def nat.coprime (a b: nat) := gcd a b = 1

instance nat.coprime_dec (a b: nat) : Decidable (coprime a b) := (inferInstance: Decidable (_ = _))

def Decidable.not_or { P Q: Prop }
  [Decidable P] [Decidable Q]:
  ¬(P ∨ Q) -> ¬P ∧ ¬Q := by
    intro not_p_or_q
    apply @Decidable.byCases P
    intro p
    have := not_p_or_q <| Or.inl p
    contradiction
    apply @Decidable.byCases Q
    intro q
    have := not_p_or_q <| Or.inr q
    contradiction
    intro not_q not_p
    apply And.intro <;> assumption

def Decidable.not_and { P Q: Prop }
  [Decidable P] [Decidable Q]:
  ¬(P ∧ Q) -> ¬P ∨ ¬Q := by
    intro not_p_or_q
    apply @Decidable.byCases P
    intro p
    apply @Decidable.byCases Q
    intro q
    have := not_p_or_q ⟨ p, q ⟩
    contradiction
    exact Or.inr
    exact Or.inl

def nat.prime.dvd_or_coprime : ∀a b, a.prime -> a ∣ b ∨ coprime a b := by
  intro a b prime_a
  apply Decidable.byContradiction
  intro not_a_dvd_b_or_coprime
  have ⟨ not_dvd, not_coprime ⟩  := Decidable.not_or not_a_dvd_b_or_coprime
  match h:gcd a b with
  | 0 =>
    have ⟨ a_eq_zero, b_eq_zero ⟩  := nat.gcd.eq_zero h
    rw [a_eq_zero, b_eq_zero] at not_dvd
    have := nat.dvd.refl 0
    contradiction
  | 1 => contradiction
  | .succ (.succ c) =>
    cases prime_a.right (gcd a b) (nat.gcd.dvd_left _ _) with
    | inl gcd_eq_one =>
      rw [h] at gcd_eq_one
      exact nat.noConfusion <| nat.succ.inj gcd_eq_one
    | inr gcd_eq_a =>
      have := nat.gcd.dvd_right a b
      rw [gcd_eq_a] at this
      contradiction

def nat.prime.search
  (p limit: nat)
  (p_gt_one: p > 1)
  (progress: ∀k, limit < k -> k ∣ p -> k = 1 ∨ k = p) : Decidable (∀k, k ∣ p -> k = 1 ∨ k = p) := by
  cases limit with
  | zero =>
    apply Decidable.isTrue
    intro k k_dvd_p
    cases k with
    | zero =>
      have p_eq_zero := dvd.eq_zero_of_by_zero  k_dvd_p
      rw [p_eq_zero] at p_gt_one
      contradiction
    | succ k =>
      apply progress
      apply nat.zero_lt_succ
      assumption
  | succ limit =>
    cases (inferInstance: Decidable (limit.succ ∣ p -> limit.succ = 1 ∨ limit.succ = p)) with
    | isFalse current =>
      apply Decidable.isFalse
      intro h
      apply current
      apply h
    | isTrue current =>
    apply nat.prime.search p limit p_gt_one
    intro k limit_lt_k k_dvd_p
    cases lt_or_eq_of_le <| nat.succ_le_of_lt limit_lt_k with
    | inl h => apply progress <;> assumption
    | inr succ_limit_eq_k =>
      rw [←succ_limit_eq_k]
      rw [←succ_limit_eq_k] at k_dvd_p
      clear succ_limit_eq_k limit_lt_k k progress
      apply current k_dvd_p

instance nat.prime.instDec (a: nat) : Decidable a.prime := by
  have : ∀P Q, Decidable P -> Decidable Q -> Decidable (P ∧ Q) := by intros; exact inferInstance
  have one_lt_a : Decidable (1 < a) := inferInstance
  cases one_lt_a with
  | isFalse h =>
    apply Decidable.isFalse
    intros x
    apply h
    exact x.left
  | isTrue h =>
  apply this
  exact .isTrue h
  apply nat.prime.search a a h
  intro k a_lt_k k_dvd_a
  have := nat.dvd.le (lt_trans nat.lt_succ_self h) k_dvd_a
  have := not_lt_of_le this
  contradiction

def nat.first_factor.find (a: nat) (current: nat) (fuel: nat) : nat :=
  match fuel with
  | .zero => current
  | .succ fuel =>
    match (inferInstance : Decidable (current ∣ a)) with
    | .isTrue _ => current
    | .isFalse _ => find a current.succ fuel

def nat.first_factor (a: nat) : nat := first_factor.find a 2 (a - 2)

def nat.first_factor.find.is_factor (a current fuel: nat) : a = fuel + current -> nat.first_factor.find a current fuel ∣ a := by
  induction fuel generalizing current with
  | zero =>
    intro enough_fuel
    rw [zero_eq, zero_add] at enough_fuel
    unfold first_factor.find
    rw [enough_fuel]
    apply dvd.refl
  | succ fuel ih =>
    intros enough_fuel
    unfold first_factor.find
    split
    assumption
    apply ih
    rw [add_succ, ←succ_add]
    assumption

def nat.first_factor.is_factor (a: nat) : 1 < a -> a.first_factor ∣ a := by
  intro one_lt_a
  match a with
  | 0 | 1 => contradiction
  | .succ (.succ _) =>
  apply nat.first_factor.find.is_factor
  have : 2 = nat.zero.succ.succ := rfl
  rw [this, succ_sub_succ, succ_sub_succ, zero_eq, sub_zero]
  rw [add_succ, add_succ, add_zero]

def nat.first_factor.find.lower_bound (a current fuel: nat) :
  current ≤ nat.first_factor.find a current fuel := by
  induction fuel generalizing current with
  | zero =>
    apply le_refl
  | succ fuel ih =>
    unfold find
    split
    apply le_refl
    apply le_trans _ (ih current.succ)
    apply le_of_lt
    apply nat.lt_succ_self

def nat.first_factor.find.is_smallest_factor (a current fuel: nat) :
  a = fuel + current ->
  (∀k, 1 < k -> k < current -> ¬ k ∣ a) ->
  (∀k, 1 < k -> k ∣ a -> nat.first_factor.find a current fuel ≤ k) := by
  induction fuel generalizing current with
  | zero =>
    intro enough_fuel prev k k_gt_1 k_dvd_current
    rw [zero_eq, zero_add] at enough_fuel
    rw [enough_fuel] at k_dvd_current prev
    match current with
    | .succ current =>
      cases lt_or_eq_of_le (nat.dvd.le nat.zero_lt_succ k_dvd_current) with
      | inl h =>
        have := prev k k_gt_1 h
        contradiction
      | inr h =>
        unfold find
        rw [h]
    | .zero =>
    apply zero_le
  | succ fuel ih =>
    intro enough_fuel prev k k_gt_1 k_dvd_a
    unfold find
    split
    {
      rename_i current_dvd_a _
      cases (inferInstance: Decidable (current ≤ k)) with
      | isTrue => assumption
      | isFalse h =>
        have k_lt_current := lt_of_not_le h
        apply False.elim
        have := prev k k_gt_1 k_lt_current
        contradiction
    }
    {
      apply ih
      {
        rw [add_succ, ←succ_add]
        assumption
      }
      {
        intro b b_gt_1 b_lt_succ_current
        cases lt_or_eq_of_le <| le_of_lt_succ b_lt_succ_current with
        | inr b_eq_current =>
          rw [b_eq_current]
          assumption
        | inl b_eq__current =>
          apply prev
          any_goals assumption
      }
      assumption
      assumption
    }

def nat.first_factor.is_smallest_factor (a: nat) : 1 < a -> ∀k, 1 < k -> k ∣ a -> a.first_factor ≤ k := by
  intro one_lt_a k k_gt_1 k_dvd_a
  apply nat.first_factor.find.is_smallest_factor
  {
    match a with
    | .succ (.succ a) =>
    have : 2 = nat.zero.succ.succ := rfl
    rw [this, succ_sub_succ, succ_sub_succ, zero_eq, sub_zero, add_succ, add_succ, add_zero]
  }
  {
    intro b b_gt_one b_lt_two
    match b with
    | 0 | 1 => contradiction
    | .succ (.succ b) =>
      have := nat.not_lt_zero <| nat.lt_of_succ_lt_succ <| nat.lt_of_succ_lt_succ b_lt_two
      contradiction
  }
  repeat assumption

def nat.first_factor.is_prime (a: nat) : 1 < a -> a.first_factor.prime := by
  intro one_lt_a
  have is_factor := nat.first_factor.is_factor a one_lt_a
  have smallest := nat.first_factor.is_smallest_factor a one_lt_a
  apply And.intro
  unfold first_factor
  have := nat.first_factor.find.lower_bound a 2 (a - 2)
  apply lt_of_lt_of_le
  apply nat.lt_succ_self
  exact this
  intro k k_dvd_fst
  have k_dvd_a := nat.dvd.trans k_dvd_fst is_factor
  match k with
  | 0 =>
    apply Or.inr
    apply Eq.symm
    apply nat.dvd.eq_zero_of_by_zero
    assumption
  | 1 => exact Or.inl rfl
  | .succ (.succ k) =>
  have := smallest k.succ.succ (by
    apply nat.succ_lt_succ
    exact nat.zero_lt_succ) k_dvd_a
  apply Or.inr
  apply le_antisymm
  apply nat.dvd.le _ k_dvd_fst
  {
    cases (inferInstance: Decidable (0 < first_factor a)) with
    | isTrue => assumption
    | isFalse h =>
      have := le_of_not_lt h
      rw [nat.le_zero this] at is_factor
      rw [dvd.eq_zero_of_by_zero is_factor] at one_lt_a
      contradiction
  }
  assumption

def nat.coprime.cancel_left { a b c: nat }: coprime a b -> a ∣ (b * c) -> a ∣ c := by
  intro a_coprime_b a_dvd_bc
  have g := gcd.of_dvd (dvd.mul_left a c) a_dvd_bc
  rw [gcd.common_right, a_coprime_b, one_mul] at g
  assumption

def nat.coprime.cancel_right { a b c: nat }: coprime a b -> a ∣ (c * b) -> a ∣ c := by
  rw [mul.comm]
  apply nat.coprime.cancel_left
