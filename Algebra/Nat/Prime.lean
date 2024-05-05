import Algebra.Nat.Dvd

def nat.prime (p: nat) := 1 < p ∧ ∀k, k ∣ p -> k ≤ 1 ∨ k = p

