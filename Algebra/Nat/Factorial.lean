import Algebra.Nat.Gcd
import Algebra.Nat.Cmp

def nat.fact (n: nat) : nat := match n with
  | 0 => 1
  | succ n => n.succ * n.fact

def nat.partial_fact (n m: nat) : nat :=
  match m with
  | 0 => 1
  | .succ m =>
  match n with
  | 0 => 1
  | succ n => n.succ * (n.partial_fact m)

postfix:max ".!" => nat.fact
postfix:max "!" => nat.fact

def nat.fact.zero : 0! = 1 := rfl
def nat.fact.succ (n) : n.succ ! = n.succ * n ! := rfl

def nat.partial_fact.zero : partial_fact 0 m = 1 := by
  cases m <;> rfl

def nat.fact.nz : 0 < n ! := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fact.succ, succ_mul]
    apply lt_of_lt_of_le
    assumption
    apply add.le_left

def nat.dvd.fact {n m: nat} : 0 < m -> m ≤ n -> m ∣ n ! := by
  intro m_nz m_le_n
  induction n with
  | zero =>
    match m with
    | .succ m =>
      have := nat.le_zero m_le_n
      contradiction
  | succ n ih =>
    cases lt_or_eq_of_le m_le_n with
    | inr h =>
      cases h
      exists n.fact
    | inl h =>
      have ⟨ x, prf ⟩  := ih (le_of_lt_succ h)
      exists (x * n.succ)
      rw [←mul.assoc, prf, mul.comm]
      rfl

def nat.dvd.of_fact {n m: nat} : m ≤ n -> m ! ∣ n ! := by
  intro m_le_n
  induction n with
  | zero =>
    cases nat.le_zero m_le_n
    apply dvd.refl
  | succ n ih =>
    cases lt_or_eq_of_le m_le_n with
    | inr h =>
      cases h
      apply dvd.refl
    | inl h =>
      have ⟨ x, prf ⟩  := ih (le_of_lt_succ h)
      exists (x * n.succ)
      rw [←mul.assoc, prf, mul.comm]
      rfl

def nat.partial_fact.eq_fact_div : m ≤ n -> nat.partial_fact n m = n ! / (n - m) ! := by
  intro m_le_n
  induction n generalizing m with
  | zero =>
    cases le_zero m_le_n
    rfl
  | succ n ih =>
    cases m with
    | zero =>
      unfold partial_fact
      rw [zero_eq, sub_zero]
      rw [div.self]
      apply fact.nz
    | succ m =>
      have m_le_n: m ≤ n := m_le_n
      unfold partial_fact
      simp
      rw [succ_sub_succ]
      rw [ih, nat.dvd.mul_div, ←fact.succ]
      apply nat.dvd.of_fact
      apply nat.sub.le
      assumption

-- TODO: revisit once there is a working theory of the rationals, since that will make this a whole lot easier
-- to prove
--
-- def nat.dvd.partial_fact : m ≤ n -> m ! ∣ partial_fact n m := by
--   intro m_le_n
--   induction m generalizing n with
--   | zero =>
--     rw [zero_eq, fact.zero,]
--     apply nat.dvd.by_one
--   | succ m ih =>
--     cases n with
--     | zero =>
--       cases m_le_n <;> contradiction
--     | succ n =>
--       have m_le_n : m ≤ n := m_le_n
--       unfold partial_fact
--       simp
--       rw [fact.succ]
--       have := ih m_le_n
--
--
--   sorry
--
-- def nat.dvd.for_combo {n m: nat} : m ≤ n -> (m !) * (n - m)! ∣ n ! := by
--   intro m_le_n
--   cases n with
--   | zero =>
--     cases le_zero m_le_n
--     apply dvd.refl
--   | succ n =>
--     cases m with
--     | zero =>
--       rw [zero_eq, sub_zero, fact.zero, one_mul]
--       apply dvd.refl
--     | succ m =>
--       let n_m := @nat.dvd.for_combo n m
--       let n_sm := @nat.dvd.for_combo n m.succ
--       sorry
--
--
-- #print axioms nat.dvd.fact
--
-- def nat.permutations (n r: nat): nat := n ! / (n - r)!
-- def nat.combinations (n r: nat): nat := n ! / ((n - r)! * r !)
--
-- #print axioms nat.permutations
