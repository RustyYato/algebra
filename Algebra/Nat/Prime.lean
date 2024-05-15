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

#print axioms Decidable.not_or

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

#print axioms Decidable.not_and

def nat.prime_dvd_or_coprime : ∀a b, a.prime -> a ∣ b ∨ coprime a b := by
  intro a b prime_a
  apply Decidable.byContradiction
  intro not_a_dvd_b_or_coprime
  have ⟨ not_dvd, not_coprime ⟩  := Decidable.not_or not_a_dvd_b_or_coprime
  match h:gcd a b with
  | 0 =>
    have ⟨ a_eq_zero, b_eq_zero ⟩  := nat.gcd_eq_zero h
    rw [a_eq_zero, b_eq_zero] at not_dvd
    have := nat.dvd_refl 0
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

#print axioms nat.prime_dvd_or_coprime

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
      have p_eq_zero := nat.eq_zero_of_zero_dvd  k_dvd_p
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
    cases TotalOrder.lt_or_eq_of_le <| nat.succ_le_of_lt limit_lt_k with
    | inl h => apply progress <;> assumption
    | inr succ_limit_eq_k =>
      rw [←succ_limit_eq_k]
      rw [←succ_limit_eq_k] at k_dvd_p
      clear succ_limit_eq_k limit_lt_k k progress
      apply current k_dvd_p

#print axioms nat.prime.search

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
  have := nat.dvd.le (TotalOrder.lt_trans (nat.lt_succ_self _) h) k_dvd_a
  have := TotalOrder.not_lt_and_ge a_lt_k this
  contradiction

#print axioms nat.prime.instDec

