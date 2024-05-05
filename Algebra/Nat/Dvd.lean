import Algebra.Nat.Div

def nat.dvd (a b: nat) := ∃k: nat, a * k = b

instance nat.dvd_inst : Dvd nat where
  dvd := nat.dvd

def nat.dvd_zero (a: nat) : a ∣ 0 := by
  exists 0
  rw [mul_zero]

#print axioms nat.dvd_zero

def nat.one_dvd (b: nat) : 1 ∣ b := by
  exists b
  rw [one_mul]

#print axioms nat.one_dvd

def nat.dvd_refl (a: nat) : a ∣ a := by
  exists 1
  rw [mul_one]

#print axioms nat.dvd_refl

def nat.dvd_mul_left (a b: nat) : a ∣ a * b := by
  exists b

#print axioms nat.dvd_mul_left

def nat.dvd_mul_right (a b: nat) : a ∣ b * a := by
  exists b
  rw [mul_comm]

#print axioms nat.dvd_mul_right

def nat.eq_zero_of_zero_dvd {b: nat} : 0 ∣ b -> b = 0 := by
  match b with
  | .zero => intro; rfl
  | .succ _ =>
    intro zero_dvd
    have ⟨ k, prf ⟩ := zero_dvd
    rw [zero_mul] at prf
    contradiction

#print axioms nat.one_dvd

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

instance nat.dvd_dec (a b: nat) : Decidable (a ∣ b) := by
  match b with
  | .zero =>
    apply Decidable.isTrue
    apply dvd_zero
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
    have := nat.mul_ge k.succ a.succ rfl
    rw [mul_comm] at this
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

#print axioms nat.dvd_dec

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
    have := mul_ge a.succ k.succ rfl
    rw [prf] at this
    exact this

#print axioms nat.dvd.le

def nat.dvd_antisymm { a b: nat } : a ∣ b -> b ∣ a -> a = b := by
  intro a_dvd_b b_dvd_a
  match b with
  | .zero =>
    have := eq_zero_of_zero_dvd b_dvd_a
    rw [this]
    rfl
  | .succ b =>
  match a with
  | .zero => 
    have := eq_zero_of_zero_dvd a_dvd_b
    rw [this]
    rfl
  | .succ a =>
  apply le_antisymm
  exact nat.dvd.le rfl a_dvd_b
  exact nat.dvd.le rfl b_dvd_a

#print axioms nat.dvd_antisymm

def nat.dvd_sub { a b: nat } : a ≤ b -> a ∣ b -> a ∣ (b - a) := by
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
    rw [mul_succ, add_comm, ←add_sub, sub_refl, add_zero]
    exact le_refl _

def nat.dvd_def { a b: nat } : b ∣ a -> a = (a / b) * b := by
  match b with
  | .zero =>
    intro zero_dvd_a
    rw [eq_zero_of_zero_dvd zero_dvd_a]
    rfl
  | .succ b =>
  have : ∀(a b: nat), b ∣ a -> 0 < b -> a = (a / b) * b := by
    intro a b q r
    apply nat.div_mod_induction (fun a b => b ∣ a -> 0 < b -> a = (a / b) * b)
    {
      intro a b a_lt_b b_dvd_a b_nz
      rw [nat.div.is_lt']
      rw [zero_mul]
      match a with
      | .zero => rfl
      | .succ a =>
        have b_le_a_succ := nat.dvd.le rfl b_dvd_a
        have := not_lt_and_ge a_lt_b b_le_a_succ
        contradiction
      repeat assumption
    }
    {
      intro a b a_ge_b ih b_dvd_a b_nz
      rw [nat.div.is_ge', succ_mul, ←ih, add_sub, add_comm, ←add_sub, sub_refl, add_zero]
      apply le_refl
      any_goals assumption
      apply nat.dvd_sub
      repeat assumption

    }
    repeat assumption
  intro b_dvd_a
  apply this
  assumption
  rfl

#print axioms nat.dvd_def

