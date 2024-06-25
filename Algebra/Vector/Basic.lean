import Algebra.Nat.Mul

inductive Vector.{u} (α: Type u) : nat -> Type u where
  | nil : Vector α 0
  | cons : α -> Vector α n -> Vector α n.succ

inductive Vector.Mem.{u} {α: Type u} : α -> Vector α n -> Prop where
  | head : ∀{n} (head: α) (tail: Vector α n), Mem head (cons head tail)
  | tail : ∀{n} (head: α) (tail: Vector α n) (elem: α), Mem elem tail -> Mem elem (cons head tail)

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

def Vec.Eq.subst { α: Type u } {p : ∀{n}, Vector α n → Prop}
  { as: Vector α n } { bs: Vector α m }
  (h₁ : as =v bs) (h₂ : p as) : p bs :=
  match h₁ with
  | .refl _ => h₂

#print axioms Vec.Eq.subst

set_option linter.unusedVariables false
def Vec.Eq.of_eq : as = bs -> as =v bs
| .refl _ => Vec.Eq.refl _
set_option linter.unusedVariables true

#print axioms Vec.Eq.subst

instance Vec.Eq.EquivalenceInst : Equivalence (@Vec.Eq α n n) where
  refl := refl
  symm := symm
  trans := trans

def Vec.cons.injEq : (.cons v vs) =v (.cons w ws) -> v = w ∧ vs =v ws := by
  intro h
  cases h
  apply And.intro <;> rfl

#print axioms Vec.cons.injEq

def Vec.cons.congrEq : v = w ∧ vs =v ws -> (.cons v vs) =v (.cons w ws) := by
  intro h
  have ⟨ h, g ⟩ := h
  subst w
  cases g
  rfl

#print axioms Vec.cons.congrEq

def Vector.mem_cons { elem v: α } { vs: Vector α n }:
  elem ∈ cons v vs -> elem = v ∨ elem ∈ vs := by
  intro h
  cases h
  apply Or.inl rfl
  apply Or.inr
  assumption

def Vector.eq_nil_of_zero_len (vs: Vector α n) :
  n = 0 -> vs =v .nil := by
  intro
  subst n
  cases vs
  rfl

#print axioms Vector.eq_nil_of_zero_len
