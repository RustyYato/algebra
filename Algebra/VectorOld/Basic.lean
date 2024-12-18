import Algebra.Nat.Mul
import Algebra.NatIndexedEq

inductive Vector.{u} (α: Type u) : nat -> Type u where
  | nil : Vector α 0
  | cons : α -> Vector α n -> Vector α n.succ

inductive Vector.Mem.{u} {α: Type u} : α -> Vector α n -> Prop where
  | head : ∀{n} (head: α) (tail: Vector α n), Mem head (cons head tail)
  | tail : ∀{n} (head: α) (tail: Vector α n) (elem: α), Mem elem tail -> Mem elem (cons head tail)

instance Vector.MemInst : Membership α (Vector α n) := ⟨ Vector.Mem ⟩

def Vector.cons.injVEq : (Vector.cons v vs) =v (Vector.cons w ws) -> v = w ∧ vs =v ws := by
  intro h
  cases h
  apply And.intro <;> rfl

def Vector.cons.congrEq : v = w ∧ vs =v ws -> (Vector.cons v vs) =v (Vector.cons w ws) := by
  intro h
  have ⟨ h, g ⟩ := h
  subst w
  cases g
  rfl

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
