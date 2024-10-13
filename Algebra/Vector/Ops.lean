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

def Vector.remove (vs: Vector α n.succ) (idx: fin n.succ) : Vector α n :=
  match idx with
  | .zero => match vs with
    | .cons _ vs => vs
  | .succ idx => match vs with
    | .cons v vs =>
    match n with
    | .succ _ => .cons v (vs.remove idx)

@[simp]
def Vector.insert_at (vs: Vector α n) (idx: fin n.succ) (value: α) : Vector α n.succ :=
  match idx with
  | .zero => .cons value vs
  | .succ idx => match vs with
    | .cons v vs => .cons v (vs.insert_at idx value)

def Vector.insert_at_get (vs: Vector α n) (idx: fin n.succ) (value: α):
  (vs.insert_at idx value).get idx = value := by
  cases idx with
  | zero =>
    unfold insert_at get
    rfl
  | succ idx =>
    cases n with
    | zero => contradiction
    | succ n =>
    cases vs with
    | cons v vs =>
    unfold insert_at get
    dsimp
    apply Vector.insert_at_get

#print axioms Vector.insert_at_get

def Vector.insert_at_get_ge (vs: Vector α n) (b: fin n) (a: fin n.succ) (value: α):
  a.val ≤ b.val ->
  (vs.insert_at a value).get b.succ = vs.get b := by
  intro a_lt_b
  cases a with
  | zero =>
    conv => {
      lhs
      unfold insert_at get
    }
  | succ a =>
    match n with
    | .succ n =>
    cases vs with
    | cons v vs =>
    conv => {
      unfold insert_at
    }
    match b with
    | .succ b =>
    unfold get
    dsimp
    apply Vector.insert_at_get_ge
    exact a_lt_b

#print axioms Vector.insert_at_get_ge

def Vector.insert_at_get_lt (vs: Vector α n) (b: fin n) (a: fin n.succ) (value: α):
  a.val > b.val ->
  (vs.insert_at a value).get (fin.mk b.val
    (by apply lt_trans b.valLt; apply nat.lt_succ_self)) = vs.get b := by
  intro a_gt_b
  induction b with
  | zero =>
    cases a
    contradiction
    cases vs
    rfl
  | succ b ih =>
    conv in (fin.mk b.succ.val _) => {
        unfold fin.val fin.mk
        dsimp
    }
    rename_i n
    match n with
    | .succ n =>
    cases vs with
    | cons v vs =>
    match a with
    | .succ a =>
    unfold insert_at
    dsimp
    unfold get
    dsimp
    apply ih
    assumption

#print axioms Vector.insert_at_get_lt

def Vector.remove_get_lt { n: nat } (vs: Vector α n.succ) (a: fin n.succ) (b: fin n) :
  b.val < a.val ->
  (vs.remove a).get b = vs.get (fin.mk b.val (lt_trans b.valLt (nat.lt_succ_self _))) := by
  intro b_lt_a
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases vs with
    | cons v vs =>
    cases a with
    | zero =>
      cases b <;> contradiction
    | succ a =>
    unfold Vector.remove
    dsimp
    cases b with
    | zero => rfl
    | succ b =>
      unfold fin.val fin.mk Vector.get
      dsimp
      apply ih
      exact b_lt_a

#print axioms Vector.remove_get_lt

def Vector.remove_get_ge { n: nat } (vs: Vector α n.succ) (a: fin n.succ) (b: fin n) :
  b.val ≥ a.val ->
  (vs.remove a).get b = vs.get b.succ := by
  intro b_gt_a
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases vs with
    | cons v vs =>
    cases b with
    | zero =>
      have := nat.le_zero b_gt_a
      cases a with
      | succ a => contradiction
      | zero => rfl
    | succ b =>
    cases a with
    | zero => rfl
    | succ a =>
      unfold Vector.remove
      dsimp
      unfold Vector.get
      dsimp
      rw [ih]
      dsimp
      exact b_gt_a

#print axioms Vector.remove_get_ge

def Vector.swap (vs: Vector α n) (a b: fin n) : Vector α n := by
  exact (vs.set b (vs.get a)).set a (vs.get b)

def Vector.cast (vs: Vector α n) (h: n = m) : Vector α m := h ▸ vs

def Vector.cast_eqv (vs: Vector α n) (h: n = m) : vs.cast h =v vs
 := by
 subst m
 rfl

def Vector.reverseAux (vs: Vector α n) (out: Vector α m) :
  Vector α (m + n) :=
  match vs with
  | .nil => Vector.cast out (nat.add_zero m).symm
  | .cons v vs => Vector.cast (vs.reverseAux <| .cons v out) (by
    rw [nat.add_succ, ←nat.succ_add])

#print axioms Vector.reverseAux

def Vector.reverse (vs: Vector α n) : Vector α n := Vector.reverseAux vs .nil

#print axioms Vector.reverse
