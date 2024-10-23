import Algebra.Nat.Cmp

inductive fin : nat -> Type where
  | zero : fin (nat.succ n)
  | succ : fin n -> fin n.succ

def fin.val (x: fin n) : nat :=
  match x with
  | .zero => .zero
  | .succ x => .succ x.val

def fin.val.congr (x y: fin n) : x.val = y.val -> x = y := by
  intro x_eq_y
  induction x with
  | zero =>
    match y with
    | .zero =>  rfl
  | succ x ih =>
    match y with
    | .succ _ =>
      congr
      apply ih
      unfold fin.val at x_eq_y
      exact nat.succ.inj x_eq_y

#print axioms fin.val.congr

def fin.valLt (x: fin n) : x.val < n := by
  induction x with
  | zero => trivial
  | succ _ ih => exact ih

def fin.mk (x: nat) : x < n -> fin n := fun lt =>
  match x with
  | .zero =>
    match n with
    | .succ _ => .zero
  | .succ x =>
    match n with
    | .succ _ =>
    .succ <| fin.mk x lt

def fin.mk_val (x: nat) (h: x < n) : (fin.mk x h).val = x := by
  induction x generalizing n with
  | zero =>
    match n with | .succ n => rfl
  | succ x ih =>
    match n with
    | .succ n =>
      unfold mk val
      rw [ih]

#print axioms fin.mk_val

def fin.val_mk (x: fin n) : fin.mk x.val x.valLt = x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    unfold val mk
    dsimp
    rw [ih]

#print axioms fin.val_mk

def fin.n_gt_zero (x: fin n) : 0 < n := by
  cases x <;> trivial

#print axioms fin.n_gt_zero

def fin.to_Fin (x: fin n) : Fin n.toNat := by
  apply Fin.mk x.val.toNat
  apply nat.toNat_lt
  apply fin.valLt

def fin.of_Fin (x: Fin n) : fin (nat.ofNat n) := by
  apply fin.mk (nat.ofNat x.val)
  apply nat.ofNat_lt
  exact x.isLt

instance Fin.Ord : Ord (fin n) where
  compare a b := compare a.val b.val

#print axioms Fin.Ord

instance Fin.TotalOrdInst : TotalOrder (fin n) where
  compare_antisymm := by
    intros
    unfold compare
    apply compare_antisymm
  compare_transitive := by
    intros
    unfold compare
    apply compare_transitive <;> assumption
  eq_of_compare_eq := by
    unfold compare
    intros
    apply fin.val.congr
    apply eq_of_compare_eq <;> assumption
  compare_eq_refl := by
    unfold compare
    intros
    unfold Ord
    dsimp
    apply compare_eq_refl <;> assumption

#print axioms Fin.TotalOrdInst
