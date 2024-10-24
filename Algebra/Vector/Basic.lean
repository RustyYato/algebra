import Algebra.List.Basic
import Algebra.Fin.Basic

structure Vector (α) (n: nat) where
  data: list α
  data_length: data.length = n

def Vector.nil : Vector α 0 where
  data := .nil
  data_length := rfl
def Vector.cons (x: α) (xs: Vector α n) : Vector α n.succ where
  data := .cons x xs.data
  data_length := by rw [list.length, xs.data_length]

def Vector.get (as: Vector α n) (x: fin n) : α :=
  as.data[x.val]'(by rw [as.data_length]; exact x.isLt)

def Vector.insert_at (as: Vector α n) (idx: fin n.succ) (x: α) : Vector α n.succ where
  data := as.data.insert_at idx.val x
  data_length := by
    rw [list.length_insert_at, as.data_length]

def Vector.insert_at_get_lt (as: Vector α n) (pos: fin n) (idx: fin n.succ) (x: α) :
  pos.val < idx.val ->
  (as.insert_at idx x).get (fin.mk pos.val (lt_trans pos.isLt (nat.lt_succ_self _))) = as.get pos := by
  intro h
  unfold insert_at get
  dsimp
  rw [list.insert_at_getElem_lt]
  congr 1
  rw [fin.mk_val]
  rw [fin.mk_val]
  assumption
  apply nat.le_of_lt_succ
  rw [as.data_length]
  exact idx.isLt

def Vector.insert_at_get_ge (as: Vector α n) (pos: fin n) (idx: fin n.succ) (x: α) :
  pos.val ≥ idx.val ->
  (as.insert_at idx x).get pos.succ = as.get pos := by
  intro h
  unfold insert_at get
  dsimp
  rw [list.insert_at_getElem_gt]
  congr 1
  apply lt_of_le_of_lt h
  apply nat.lt_succ_self
  apply nat.le_of_lt_succ
  rw [as.data_length]
  exact idx.isLt
  apply nat.le_of_lt_succ
  rw [as.data_length]
  exact pos.isLt

def Vector.append (as: Vector α n) (bs: Vector α m) : Vector α (n + m) where
  data := as.data ++ bs.data
  data_length := by rw [list.length_append, as.data_length, bs.data_length]

instance : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) := ⟨Vector.append⟩
def Vector.append.def (as: Vector α n) (bs: Vector α m) : as ++ bs = as.append bs := rfl

def Vector.recursion
  { motive: ∀{n}, Vector α n -> Sort _ }
  (nil: motive .nil)
  (cons: ∀{n} x (xs: Vector α n), motive xs -> motive (Vector.cons x xs))
  : ∀{n} (v: Vector α n), motive v
| .zero, ⟨.nil,.refl _⟩ => nil
| .succ _, ⟨.cons _ xs,h⟩  => cons _ _ (Vector.recursion nil cons ⟨xs,nat.succ.inj h⟩)

def Vector.ind
  { motive: ∀{n}, Vector α n -> Prop }
  (nil: motive .nil)
  (cons: ∀{n} x (xs: Vector α n), motive xs -> motive (Vector.cons x xs))
  : ∀{n} (v: Vector α n), motive v := recursion nil cons

def Vector.recursion_nil { motive: ∀{n}, Vector α n -> Sort _ }
  (nil: motive .nil)
  (cons: ∀{n} x (xs: Vector α n), motive xs -> motive (Vector.cons x xs)):
  Vector.recursion nil cons .nil = nil := rfl

def Vector.recursion_cons { motive: ∀{n}, Vector α n -> Sort _ }
  (nil: motive .nil)
  (cons: ∀{n} x (xs: Vector α n), motive xs -> motive (Vector.cons x xs)):
  Vector.recursion nil cons (.cons x xs) = cons x xs (Vector.recursion nil cons xs) := rfl

def Vector.remove {n: nat} (as: Vector α n.succ) (idx: fin n.succ) : Vector α n where
  data := as.data.remove idx.val <| by
    rw [as.data_length]
    exact idx.isLt
  data_length := by
    rw [list.length_remove, as.data_length]
    rfl

def Vector.remove_get_lt {n: nat} (as: Vector α n.succ) (pos idx: fin n.succ) :
  (h: pos.val < idx.val) ->
  (as.remove idx).get (fin.mk pos.val (by
    apply lt_of_lt_of_le h
    apply nat.le_of_lt_succ
    exact idx.isLt)) = as.get pos := by
    intro h
    unfold remove get
    dsimp
    rw [list.remove_getElem_lt]
    congr 1
    rw [fin.mk_val]
    rw [fin.mk_val]
    assumption

def Vector.remove_get_ge {n: nat} (as: Vector α n.succ) (pos: fin n) (idx: fin n.succ) :
  (h: pos.val ≥ idx.val) ->
  (as.remove idx).get pos = as.get pos.succ := by
  intro h
  unfold remove get
  dsimp
  rw [list.remove_getElem_ge]
  congr 1
  assumption
  rw [as.data_length]
  exact pos.isLt
