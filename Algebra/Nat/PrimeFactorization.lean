import Algebra.Nat.Prime
import Algebra.SortedList.Merge
import Algebra.List

def product (xs: List nat) : nat := match xs with
  | [] => 1
  | x::xs => x * product xs

def product.empty : product [] = 1 := rfl
def product.cons : product (x::xs) = x * product xs := rfl

structure PrimeFactorization (n: nat) where
  factors: SortedList nat
  all_primes: factors.items.allP nat.prime
  product_eq: product factors.items = n

def PrimeFactorization.of_prime {n: nat}: n.prime -> PrimeFactorization n := by
  intro prime_n
  apply PrimeFactorization.mk <| SortedList.mk [n] (by trivial)
  apply And.intro
  assumption
  trivial
  apply nat.mul_one

#print axioms PrimeFactorization.of_prime

def PrimeFactorization.mul { a b: nat } : PrimeFactorization a -> PrimeFactorization b -> PrimeFactorization (a * b) := by
  intro factors_a factors_b
  apply PrimeFactorization.mk <| factors_a.factors.merge factors_b.factors
  {
    apply List.allP.of_contains
    intro x x_in_merge
    cases sorted_merge.contains x_in_merge with 
    | inl x_in_a =>
      apply List.allP.contains
      exact factors_a.all_primes
      exact x_in_a
    | inr x_in_b =>
      apply List.allP.contains
      exact factors_b.all_primes
      exact x_in_b
  }
  {
    conv => {
      rhs
      rw [←factors_a.product_eq]
      rw [←factors_b.product_eq]
    }
    apply sorted_induction' (fun xs ys => product (sorted_merge xs ys) = product xs * product ys)
    {
      intros ys
      rw [sorted_merge.left_empty, product.empty, nat.one_mul]
    }
    {
      intros x xs
      rw [sorted_merge.right_empty, product.empty, nat.mul_one]
    }
    {
      intro x y xs ys x_lt_y ih
      rw [sorted_merge.if_lt, product.cons, ih, ←nat.mul_assoc, ←@product.cons x xs]
      assumption
    }
    {
      intro x y xs ys x_gt_y ih
      rw [sorted_merge.if_gt, product.cons, ih, nat.mul_comm, nat.mul_assoc, nat.mul_comm _ y, ←product.cons]
      assumption
    }
    {
      intro x y xs ys x_eq_y ih
      rw [sorted_merge.if_eq, product.cons, product.cons, ih,
        nat.mul_comm (product xs), ←nat.mul_assoc y, ←@product.cons y, nat.mul_comm _ (product xs), ←nat.mul_assoc]
      rfl
      assumption
    }
  }

#print axioms PrimeFactorization.mul

