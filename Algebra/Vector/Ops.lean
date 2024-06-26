import Algebra.Vector.Basic
import Algebra.Fin.Basic
import Algebra.Range.Basic

def Vector.append (vs: Vector α n) (ws: Vector α m) :
  Vector α (n + m) :=
  match vs with
  | .nil => ws
  | .cons v vs => .cons v (append vs ws)

#print axioms Vector.append

instance Vector.appendInst : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) := ⟨ append ⟩

def Vector.flatten (vs: Vector (Vector α m) n) : Vector α (n * m) :=
  match vs with
  | .nil => .nil
  | .cons v vs => v ++ vs.flatten

#print axioms Vector.flatten

def Vector.from_list (list: List α) : Vector α (nat.ofNat list.length) :=
  match list with
  | .nil => .nil
  | .cons v vs => .cons v (Vector.from_list vs)

#print axioms Vector.flatten

def Vector.to_list (vs: Vector α n) : List α :=
  match vs with
  | .nil => .nil
  | .cons v vs => .cons v vs.to_list

#print axioms Vector.flatten

def Vector.get (vs: Vector α n) (idx: fin n) : α :=
  match idx with
  | .zero => match vs with
    | .cons v _ => v
  | .succ idx => match vs with
    | .cons _ vs => vs.get idx

def Vector.set (vs: Vector α n) (idx: fin n) (value: α) : Vector α n :=
  match idx with
  | .zero => match vs with
    | .cons _ vs => .cons value vs
  | .succ idx => match vs with
    | .cons v vs => .cons v (vs.set idx value)

def Vector.swap (vs: Vector α n) (a b: fin n) : Vector α n := by
  exact (vs.set b (vs.get a)).set a (vs.get b)
