import Algebra.Nat.Cmp

inductive fin : nat -> Type where
  | zero : fin (nat.succ n)
  | succ : fin n -> fin n.succ

def fin.val (x: fin n) : nat :=
  match x with
  | .zero => .zero
  | .succ x => .succ x.val

def fin.val.inj (x y: fin n) : x.val = y.val -> x = y := by
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

def fin.isLt (x: fin n) : x.val < n := by
  induction x with
  | zero => apply nat.zero_lt_succ
  | succ _ ih => exact ih.succ

def fin.nonzero (x: fin n) : 0 < n := lt_of_le_of_lt (nat.zero_le _) x.isLt

def fin.mk (x: nat) : x < n -> fin n := fun lt =>
  match x with
  | .zero =>
    match n with
    | .succ _ => .zero
  | .succ x =>
    match n with
    | .succ _ =>
    .succ <| fin.mk x <| nat.lt_of_succ_lt_succ lt

def fin.mk_val (x: nat) (h: x < n) : (fin.mk x h).val = x := by
  induction x generalizing n with
  | zero =>
    match n with | .succ n => rfl
  | succ x ih =>
    match n with
    | .succ n =>
      unfold mk val
      rw [ih]

def fin.val_mk (x: fin n) : fin.mk x.val x.isLt = x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    unfold val mk
    dsimp
    rw [ih]

def fin.mk.inj (x y: nat) (xLt: x < n) (yLt: y < n) : fin.mk x xLt = fin.mk y yLt -> x = y := by
  intro h
  rw [←mk_val x xLt, ←mk_val y yLt, h]

def fin.n_gt_zero (x: fin n) : 0 < n := by
  cases x <;> apply nat.zero_lt_succ

def fin.to_Fin (x: fin n) : Fin n.toNat := by
  apply Fin.mk x.val.toNat
  apply nat.toNat_lt
  apply fin.isLt

def fin.of_Fin (x: Fin n) : fin (nat.ofNat n) := by
  apply fin.mk (nat.ofNat x.val)
  apply nat.ofNat_lt
  exact x.isLt

instance : LT (fin n) where
  lt a b := a.val < b.val

instance : LE (fin n) where
  le a b := a.val ≤ b.val

instance (a b: fin n) : Decidable (a ≤ b) := decidable_of_iff (a.val ≤ b.val) (Iff.refl _)

instance : Min (fin n) := minOfLe
instance : Max (fin n) := maxOfLe

instance : IsLinearOrder (fin n) :=
  IsLinearOrder.transfer nat (fin n) fin.val (fin.val.inj _ _) (Iff.refl _) (Iff.refl _) (by
    intro x y
    unfold min instMinFin instMinNat_1 minOfLe
    dsimp
    split
    rw [if_pos]
    assumption
    rw [if_neg]
    assumption) (by
    intro x y
    unfold max instMaxFin instMaxNat maxOfLe
    dsimp
    split
    rw [if_pos]
    assumption
    rw [if_neg]
    assumption)
