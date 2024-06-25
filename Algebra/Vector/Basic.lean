import Algebra.Nat.Mul

inductive Vector.{u} (α: Type u) : nat -> Type u where
  | nil : Vector α 0
  | cons : α -> Vector α n -> Vector α n.succ

inductive Vector.Mem : α -> Vector α n -> Prop where
  | head : ∀head tail, Mem head (cons head tail)
  | tail : ∀head tail elem, Mem elem tail -> Mem elem (cons head tail)

instance Vector.MemInst : Membership α (Vector α n) := ⟨ Vector.Mem ⟩

inductive Vec.Eq.{u} { α: Type u } :
  ∀{ n m: nat }, Vector α n -> Vector α m -> Prop where
  | refl : ∀a, Eq a a

infix:50 " =v " => Vec.Eq

@[refl]
def Vec.Eq.rfl : vs =v vs := refl _

def Vec.Eq.length_eq { vs: Vector α n } { ws: Vector α m } :
  vs =v ws -> n = m := by
  intro vs_eq_ws
  cases vs_eq_ws
  rfl

#print axioms Vec.Eq.length_eq

def Vec.Eq.symm :
  vs =v ws -> ws =v vs := by
  intro vs_eq_ws
  cases vs_eq_ws
  rfl

#print axioms Vec.Eq.symm

def Vec.Eq.trans :
  vs =v ws -> ws =v xs -> vs =v xs := by
  intro vs_eq_ws ws_eq_xs
  cases vs_eq_ws
  cases ws_eq_xs
  rfl

#print axioms Vec.Eq.trans

instance Vec.Eq.EquivalenceInst : Equivalence (@Vec.Eq α n n) where
  refl := refl
  symm := symm
  trans := trans

def Vec.cons.injEq : (.cons v vs) =v (.cons w ws) -> v = w ∧ vs =v ws := by
  intro h
  cases h
  apply And.intro <;> rfl


#print axioms Vec.cons.injEq
