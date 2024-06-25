import Algebra.Vector.Basic

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
