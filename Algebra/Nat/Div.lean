import Algebra.Nat.Mul
import Algebra.Nat.Sub
import Algebra.Nat.WellFounded

def nat.div_mod_induction
  ( motive: nat -> nat -> Sort α )
  ( is_lt: ∀(a b: nat), a < b -> motive a b )
  ( is_ge: ∀(a b: nat), a ≥ b -> motive (a - b) b -> motive a b ):
  ∀a b, 0 < b -> motive a b := fun a b b_nz =>
    match lt_or_ge_dec a b with
    | .Lt a_lt_b => is_lt a b a_lt_b
    | .Ge a_ge_b => is_ge a b a_ge_b (nat.div_mod_induction motive is_lt is_ge (a - b) b b_nz)
termination_by a => a
decreasing_by
  apply sub_nz_lt <;> assumption

#print axioms nat.div_mod_induction

def nat.div : ∀(_ b: nat), 0 < b -> nat := by
  apply nat.div_mod_induction
    (fun _ _ => nat)
    (fun _ _ _ => nat.zero)
    (fun _ _ _ prev => prev.succ)

#print axioms nat.div

def nat.mod : ∀(_ b: nat), 0 < b -> nat := by
  apply nat.div_mod_induction
    (fun _ _ => nat)
    (fun a _ _ => a)
    (fun _ _ _ prev => prev)

#print axioms nat.mod

