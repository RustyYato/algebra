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
      rw [sorted_merge.if_lt, product.cons, ih, ←nat.mul.assoc, ←@product.cons x xs]
      assumption
    }
    {
      intro x y xs ys x_gt_y ih
      rw [sorted_merge.if_gt, product.cons, ih, nat.mul.comm, nat.mul.assoc, nat.mul.comm _ y, ←product.cons]
      assumption
    }
    {
      intro x y xs ys x_eq_y ih
      rw [sorted_merge.if_eq, product.cons, product.cons, ih,
        nat.mul.comm (product xs), ←nat.mul.assoc y, ←@product.cons y, nat.mul.comm _ (product xs), ←nat.mul.assoc]
      rfl
      assumption
    }
  }

def PrimeFactorization.new (n: nat) : 0 < n -> PrimeFactorization n := by
  intro n_nz
  cases (inferInstance: Decidable (1 < n)) with
  | isFalse h =>
    have := le_of_not_lt h
    match n with
    | 1 =>
    apply PrimeFactorization.mk (SortedList.mk [] True.intro)
    decide
    decide
  | isTrue h =>
  have is_prime := nat.first_factor.is_prime n h
  have is_factor := nat.first_factor.is_factor n h
  have := nat.dvd.def is_factor
  rw [this]
  apply PrimeFactorization.mul
  apply PrimeFactorization.new
  {
    apply nat.div.gt_zero
    apply lt_trans
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

def product.eq_zero : product list = 0 -> 0 ∈ list := by
  induction list with
  | nil => intro; contradiction
  | cons x xs ih =>
    unfold product
    intro eq_zero
    cases nat.mul.eq_zero eq_zero with
    | inl h => rw [h]; apply List.Mem.head
    | inr h =>
      apply List.Mem.tail
      apply ih h

def product.eq_one : product list = 1 -> ∀x, x ∈ list -> x = 1 := by
  intro eq_one y elem
  induction elem with
  | head _ =>
    have ⟨ _, _ ⟩ := nat.mul.eq_one eq_one
    assumption
  | tail _ _ ih =>
    apply ih
    have ⟨ _, _ ⟩ := nat.mul.eq_one eq_one
    assumption

def PrimeFactorization.never_zero : PrimeFactorization 0 -> False := by
  intro factorization
  have := product.eq_zero factorization.product_eq
  have := (factorization.all_primes.contains) 0 this
  contradiction

def PrimeFactorization.is_factor (n p: nat) (f: PrimeFactorization n) : p ∈ f.factors.items -> p ∣ n := by
  cases f with
  | mk factors is_prime product_eq =>
  cases factors with
  | mk factors sorted =>
  intro elem
  simp only at elem
  induction elem generalizing n with
  | head factors => exists product factors
  | tail head _elem ih =>
    rename_i factors
    have ⟨ x, xprf ⟩ := ih (n / head) sorted.pop is_prime.right (by
      simp only
      rw [←product_eq]
      simp only
      rw [product.cons]
      rw [nat.mul_div]
      have := is_prime.left.left
      apply lt_trans
      apply nat.lt_succ_self
      assumption)
    exists x * head
    rw [←nat.mul.assoc, xprf, ←nat.dvd.def]
    exists product factors

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
    cases nat.dvd.eq_one_of_by_one p p_dvd_n
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
          cases nat.prime.dvd_or_coprime p f prime_p with
          | inl p_dvd_f =>
            cases is_prime.left.right p p_dvd_f with
            | inl h => cases h <;> contradiction
            | inr h => contradiction
          | inr p_coprime_f => assumption
        }
        assumption
        apply lt_trans
        apply nat.lt_succ_self
        exact is_prime.left.left
      }
      exact is_prime.right
      rw [←product_eq, product.cons, nat.mul_div]
      apply lt_trans
      apply nat.lt_succ_self
      exact is_prime.left.left

def PrimeFactorization.unique (a b: PrimeFactorization n) : a = b := by
  have a_is_factor := a.is_factor
  have b_is_factor := b.is_factor

  have a_is_complete := a.is_complete
  have b_is_complete := b.is_complete

  cases a with
  | mk a_factors a_is_prime a_product_eq =>
  cases a_factors with
  | mk a_factors a_sorted =>

  cases b with
  | mk b_factors b_is_prime b_product_eq =>
  cases b_factors with
  | mk b_factors b_sorted =>

  congr

  induction a_factors generalizing n b_factors with
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
    have n_gt_1 : 1 < n := by
      cases (inferInstance: Decidable (1 < n)) with
      | isTrue => assumption
      | isFalse =>
        match n with
        | 0 =>
          have := product.eq_zero a_product_eq
          have := (a_is_prime.contains) 0 this
          contradiction
        | 1 =>
          cases product.eq_one a_product_eq a (.head _)
          have := (a_is_prime.contains) 1 (.head _)
          contradiction
        | nat.succ (nat.succ 0) + n =>
          rename_i h
          rw [nat.succ_add, nat.succ_add] at h
          have h := le_of_not_lt h
          have := nat.le_of_succ_le_succ h
          have := nat.le_zero this
          contradiction

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
      have first_factor_in_a := a_is_complete first_factor (nat.first_factor.is_prime n n_gt_1) (by
        apply nat.first_factor.is_factor
        assumption
      )
      have first_factor_in_b := b_is_complete first_factor (nat.first_factor.is_prime n n_gt_1) (by
        apply nat.first_factor.is_factor
        assumption
      )
      simp only at first_factor_in_a first_factor_in_b
      have ff_eq_a := (a_sorted.pick_first) first_factor_in_a (by
        intro y y_in_factors
        have prime_y := (a_is_prime.contains) _ y_in_factors
        have y_dvd_n := a_is_factor _ y_in_factors
        exact nat.first_factor.is_smallest_factor n n_gt_1 y prime_y.left y_dvd_n)
      have ff_eq_b := (b_sorted.pick_first) first_factor_in_b (by
        intro y y_in_factors
        have prime_y := (b_is_prime.contains) _ y_in_factors
        have y_dvd_n := b_is_factor _ y_in_factors
        exact nat.first_factor.is_smallest_factor n n_gt_1 y prime_y.left y_dvd_n)
      rw [←ff_eq_b, ←ff_eq_a]
      congr

      let nfa: PrimeFactorization (n / first_factor) := PrimeFactorization.mk (SortedList.mk a_factors a_sorted.pop) a_is_prime.right (by
        simp only at a_product_eq
        simp only at *
        rw [←a_product_eq, product.cons, ff_eq_a, nat.mul_div]
        apply lt_trans
        apply nat.lt_succ_self
        exact a_is_prime.left.left)

      let nfb: PrimeFactorization (n / first_factor) := PrimeFactorization.mk (SortedList.mk b_factors b_sorted.pop) b_is_prime.right (by
        simp only at b_product_eq
        simp only at *
        rw [←b_product_eq, product.cons, ff_eq_b, nat.mul_div]
        apply lt_trans
        apply nat.lt_succ_self
        exact b_is_prime.left.left)

      apply @ih (n / first_factor)
      any_goals (simp only at *)
      any_goals (clear ih)
      exact nfa.is_factor
      exact nfa.is_complete
      exact nfb.is_factor
      exact nfb.is_complete
      exact nfa.factors.is_sorted
      exact nfa.all_primes
      exact nfa.product_eq
      exact nfb.factors.is_sorted
      exact nfb.all_primes
      exact nfb.product_eq

instance PrimeFactorization.instSubSingleton : Subsingleton (PrimeFactorization n) := ⟨ PrimeFactorization.unique ⟩

instance PrimeFactorization.instInhabitted (n_nz: 0 < n) : Inhabited (PrimeFactorization n) := ⟨ PrimeFactorization.new n n_nz ⟩
