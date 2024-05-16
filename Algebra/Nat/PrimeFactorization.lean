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

def PrimeFactorization.new (n: nat) : 0 < n -> PrimeFactorization n := by
  intro n_nz
  cases (inferInstance: Decidable (1 < n)) with
  | isFalse h => 
    have := TotalOrder.not_lt_implies_ge h
    match n with 
    | 1 => 
    apply PrimeFactorization.mk (SortedList.mk [] True.intro)
    decide
    decide
  | isTrue h => 
  have is_prime := nat.first_factor.is_prime n h
  have is_factor := nat.first_factor.is_factor n h
  have := nat.dvd_def is_factor
  rw [this]
  apply PrimeFactorization.mul
  apply PrimeFactorization.new
  {
    apply nat.div_gt_zero
    apply TotalOrder.lt_trans
    apply nat.lt_succ_self
    exact is_prime.left
    apply nat.dvd.le _ is_factor
    assumption
  }
  apply PrimeFactorization.of_prime
  assumption
termination_by n
decreasing_by
  apply nat.div.lt
  exact is_prime.left
  assumption

#print axioms PrimeFactorization.new

def product.eq_zero : product list = 0 -> 0 ∈ list := by
  induction list with
  | nil => intro; contradiction
  | cons x xs ih => 
    unfold product
    intro eq_zero
    cases nat.mul_eq_zero _ _ eq_zero with
    | inl h => rw [h]; apply List.Mem.head
    | inr h =>
      apply List.Mem.tail
      apply ih h

#print axioms product.eq_zero

def product.eq_one : product list = 1 -> ∀x, x ∈ list -> x = 1 := by
  intro eq_one y elem
  induction elem with
  | head _ => 
    have ⟨ _, _ ⟩ := nat.mul_eq_one _ _ eq_one
    assumption
  | tail _ _ ih =>
    apply ih
    have ⟨ _, _ ⟩ := nat.mul_eq_one _ _ eq_one
    assumption

#print axioms product.eq_one

def PrimeFactorization.never_zero : PrimeFactorization 0 -> False := by
  intro factorization
  have := product.eq_zero factorization.product_eq
  have := (factorization.all_primes.contains) 0 this
  contradiction

#print axioms PrimeFactorization.never_zero

def PrimeFactorization.is_factor (n p: nat) (f: PrimeFactorization n) : p ∈ f.factors.items -> p ∣ n := by
  cases f with 
  | mk factors is_prime product_eq =>
  cases factors with
  | mk factors sorted =>
  intro elem
  simp only at elem
  induction elem generalizing n with
  | head factors => exists product factors
  | tail head elem ih => 
    rename_i factors
    have ⟨ x, xprf ⟩ := ih (n / head) sorted.pop is_prime.right (by
      simp only
      rw [←product_eq]
      simp only
      rw [product.cons]
      rw [nat.mul_div]
      have := is_prime.left.left
      apply TotalOrder.lt_trans
      apply nat.lt_succ_self
      assumption)
    exists x * head
    rw [←nat.mul_assoc, xprf, ←nat.dvd_def]
    exists product factors

#print axioms PrimeFactorization.is_factor

def PrimeFactorization.is_complete (n p: nat) (f: PrimeFactorization n) : p.prime -> p ∣ n -> p ∈ f.factors.items := by
  intro prime_p p_dvd_n
  
  cases f with 
  | mk factors is_prime product_eq =>
  cases factors with
  | mk factors sorted =>

  simp only at is_prime product_eq
  simp
  clear sorted

  induction factors generalizing n with
  | nil =>
    unfold product at product_eq
    cases product_eq
    cases nat.dvd_one p p_dvd_n
    contradiction
  | cons f factors ih =>
    cases decEq p f with
    | isTrue h =>
       cases h
       exact List.Mem.head _
    | isFalse h =>
      apply List.Mem.tail
      apply ih (n / f)
      {
        rw [product.cons] at product_eq
        cases product_eq
        rw [nat.mul_div]
        apply nat.coprime.cancel_left
        {
          cases nat.prime_dvd_or_coprime p f prime_p with
          | inl p_dvd_f =>
            cases is_prime.left.right p p_dvd_f with
            | inl h => cases h <;> contradiction
            | inr h => contradiction
          | inr p_coprime_f => assumption
        }
        assumption
        apply TotalOrder.lt_trans
        apply nat.lt_succ_self
        exact is_prime.left.left
      }
      exact is_prime.right
      rw [←product_eq, product.cons, nat.mul_div]
      apply TotalOrder.lt_trans
      apply nat.lt_succ_self
      exact is_prime.left.left

#print axioms PrimeFactorization.is_complete

def PrimeFactorization.unique (a b: PrimeFactorization n) : a = b := by
  have a_is_factor := a.is_factor
  have b_is_factor := b.is_factor

  cases a with 
  | mk a_factors a_is_prime a_product_eq =>
  cases a_factors with
  | mk a_factors a_sorted =>
  
  cases b with 
  | mk b_factors b_is_prime b_product_eq =>
  cases b_factors with
  | mk b_factors b_sorted =>

  congr

  induction a_factors generalizing b_factors with
  | nil =>
    simp only at a_product_eq
    unfold product at a_product_eq
    cases a_product_eq
    have b_all_ones := product.eq_one b_product_eq
    cases b_factors with
    | nil => rfl
    | cons b b_factors =>
      have b_eq_one := b_all_ones b (.head _)
      have := b_is_prime.contains b
      simp only at this
      have b_prime := this (.head _)
      rw [b_eq_one] at b_prime
      contradiction
  | cons a a_factors ih => 
    cases b_factors with
    | nil =>
      unfold product at b_product_eq
      cases b_product_eq

      have a_all_ones := product.eq_one a_product_eq
      have a_eq_one := a_all_ones a (.head _)
      have := a_is_prime.contains a
      simp only at this
      have a_prime := this (.head _)
      rw [a_eq_one] at a_prime
      contradiction
    | cons b b_factors =>
      let first_factor := n.first_factor
      have := a_is_factor first_factor
      sorry

#print axioms PrimeFactorization.unique
 
