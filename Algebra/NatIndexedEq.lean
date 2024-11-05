import Algebra.Nat.Basic

universe u
variable { α: nat -> Type u }

inductive NatEq: ∀{ n m: nat }, α n -> α m -> Prop where
  | refl : ∀{n} (a: α n), NatEq a a

infix:50 " =v " => NatEq

@[refl]
def NatEq.rfl : vs =v vs := refl _

def NatEq.length_eq { vs: α n } { ws: α m } :
  vs =v ws -> n = m := by
  intro vs_eq_ws
  cases vs_eq_ws
  rfl

def NatEq.symm :
  vs =v ws -> ws =v vs := by
  intro vs_eq_ws
  cases vs_eq_ws
  rfl

def NatEq.trans :
  vs =v ws -> ws =v xs -> vs =v xs := by
  intro vs_eq_ws ws_eq_xs
  cases vs_eq_ws
  cases ws_eq_xs
  rfl

def NatEq.subst {p : ∀{n}, α n → Prop}
  { as: α n } { bs: α m }
  (h₁ : as =v bs) (h₂ : p as) : p bs :=
  match h₁ with
  | .refl _ => h₂

set_option linter.unusedVariables false
def NatEq.of_eq : as = bs -> as =v bs
| .refl _ => NatEq.refl _
set_option linter.unusedVariables true

instance NatEq.EquivalenceInst : Equivalence (@NatEq α n n) where
  refl := refl
  symm := symm
  trans := trans
