import Algebra.Nat.Prime
import Algebra.List
import Algebra.SortedList.Basic

structure PrimeFactorization (n: nat) where
  factors: SortedList nat
  all_primes: factors.items.allP nat.prime
  product_eq: factors.items.foldl Mul.mul 1 = n

