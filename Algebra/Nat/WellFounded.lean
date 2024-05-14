import Algebra.Nat.Cmp

def nat.lt : nat -> nat -> Prop := TotalOrder.instLT.lt

instance nat.wf : WellFounded nat.lt := WellFounded.intro (by
  intro a
  induction a with
  | zero => 
    apply Acc.intro
    intro y y_lt_a
    have := nat.not_lt_zero y_lt_a
    contradiction
  | succ a ih =>  
    apply Acc.intro
    intro y y_lt_a
    cases nat.lt_or_eq_of_le <| nat.le_of_lt_succ y_lt_a with
    | inl y_lt_a => exact Acc.inv ih y_lt_a
    | inr y_eq_a =>
      rw [y_eq_a]
      assumption
  )

#print axioms nat.wf

instance nat.wf_rel : WellFoundedRelation nat where
  rel := nat.lt
  wf := nat.wf

#print axioms nat.wf_rel

