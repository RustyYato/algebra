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

