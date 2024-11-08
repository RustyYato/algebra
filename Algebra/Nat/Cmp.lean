import Algebra.Nat.Basic
import Algebra.Order.Defs

inductive nat.LE : nat -> nat -> Prop where
| zero x : LE 0 x
| succ x y : LE x y ->  LE x.succ y.succ

inductive nat.LT : nat -> nat -> Prop where
| zero (x: nat) : LT 0 x.succ
| succ x y : LT x y -> LT x.succ y.succ

instance : LE nat := ⟨nat.LE⟩
instance : LT nat := ⟨nat.LT⟩

instance nat.decLe : ∀(a b: nat), Decidable (a ≤ b)
| .succ _, .zero => .isFalse (nomatch ·)
| .zero, _ => .isTrue (.zero _)
| .succ a, .succ b =>
  match decLe a b with
  | .isTrue h => .isTrue h.succ
  | .isFalse h => .isFalse fun g => match g with | .succ _ _ g => h g

instance : Min nat := minOfLe
instance : Max nat := maxOfLe

instance : IsLinearOrder' nat where
  lt_iff_le_and_not_le := by
    intro a b
    induction b generalizing a with
    | zero =>
      apply Iff.intro (nomatch ·)
      intro ⟨h,h₀⟩
      cases a <;> contradiction
    | succ b ih =>
      cases a with
      | zero =>
        apply Iff.intro
        intro _
        apply And.intro
        apply nat.LE.zero
        intro; contradiction
        intro ⟨_,_⟩
        apply nat.LT.zero
      | succ a =>
        apply Iff.intro
        intro h
        cases h <;> rename_i h
        have ⟨h₀,h₁⟩  := ih.mp h
        apply And.intro
        exact h₀.succ
        intro g
        cases g; contradiction
        intro ⟨h₀,h₁⟩
        apply nat.LT.succ
        apply ih.mpr
        apply And.intro
        cases h₀; assumption
        intro h
        apply h₁
        apply nat.LE.succ
        assumption
  le_antisymm := by
    intro a b a_le_b b_le_a
    induction a_le_b with
    | zero x =>
      cases b_le_a
      rfl
    | succ a b _ ih =>
      cases b_le_a
      congr
      apply ih
      assumption
  le_total := by
    intro a b
    induction a generalizing b with
    | zero => exact .inl (.zero _)
    | succ a ih =>
      cases b with
      | zero => exact .inr (.zero _)
      | succ b =>
        cases ih b
        apply Or.inl; apply nat.LE.succ; assumption
        apply Or.inr; apply nat.LE.succ; assumption
  le_complete := by
    intro a b
    induction a generalizing b with
    | zero => exact .inl (.zero _)
    | succ a ih =>
      cases b with
      | zero => exact .inr (nomatch ·)
      | succ b =>
        cases ih b
        apply Or.inl; apply nat.LE.succ; assumption
        apply Or.inr;
        intro h
        cases h
        contradiction
  le_trans := by
    intro a b c
    intro ab bc
    induction ab generalizing c with
    | zero => exact .zero _
    | succ a _ _ ih =>
      cases bc
      apply nat.LE.succ
      apply ih
      assumption
instance : IsLinearOrder nat where

def nat.lt_succ_self {a: nat} : a < a.succ := by
  induction a with
  | zero => exact .zero _
  | succ _ ih => exact ih.succ

def nat.zero_lt_succ {a: nat} : 0 < a.succ :=  .zero _

def nat.pos_of_lt  : ∀{a b: nat}, b < a -> 0 < a
| .succ _, _, _ => .zero _

def nat.zero_le (a: nat) : 0 ≤ a := .zero _
def nat.le_zero: ∀{a: nat}, a ≤ 0 -> a = 0
| .zero, _ => rfl

def nat.not_lt_zero {a: nat}: ¬(a < 0) := (nomatch ·)

def nat.succ_lt_succ {a b:nat}: a < b -> a.succ < b.succ := .succ _ _
def nat.lt_of_succ_lt_succ {a b:nat}: a.succ < b.succ -> a < b
| .succ _ _ h => h

def nat.succ_le_succ {a b:nat}: a ≤ b -> a.succ ≤ b.succ := .succ _ _
def nat.le_of_succ_le_succ {a b:nat}: a.succ ≤ b.succ -> a ≤ b
| .succ _ _ h => h

def nat.succ_le_of_lt {a b: nat} : a < b -> a.succ ≤ b
| .zero _ => (LE.zero _).succ
| .succ _ _ lt => (succ_le_of_lt lt).succ

def nat.le_of_lt_succ {a b: nat} : a < b.succ -> a ≤ b
| .zero a => .zero _
| .succ _ b h => succ_le_of_lt h

def nat.lt_succ_of_le {a b: nat} : a ≤ b -> a < b.succ
| .zero a => .zero _
| .succ _ _ h => (lt_succ_of_le h).succ

def nat.lt_of_succ_le {a b: nat} : a.succ ≤ b -> a < b
| .succ _ _ le => nat.lt_succ_of_le le

def nat.toNat_lt { a b: nat } : a < b -> a.toNat < b.toNat := by
  intro a_lt_b
  induction a generalizing b with
  | zero =>
    match b with
    | .succ _ => apply Nat.zero_lt_succ
  | succ a ih =>
    match b with
    | .succ b =>
    unfold toNat
    apply Nat.succ_lt_succ
    apply ih
    apply lt_of_succ_lt_succ
    assumption

def nat.toNat_le { a b: nat } : a ≤ b -> a.toNat ≤ b.toNat := by
  intro a_lt_b
  induction a generalizing b with
  | zero =>
    apply Nat.zero_le
  | succ a ih =>
    match b with
    | .succ b =>
    unfold toNat
    apply Nat.succ_le_succ
    apply ih
    apply le_of_succ_le_succ
    assumption

def nat.ofNat_lt { a b: Nat } : a < b -> nat.ofNat a < nat.ofNat b := by
  intro a_lt_b
  induction a generalizing b with
  | zero =>
    match b with
    | .succ _ => apply zero_lt_succ
  | succ a ih =>
    match b with
    | .succ b =>
    apply nat.succ_lt_succ
    apply ih
    apply Nat.lt_of_succ_lt_succ
    exact a_lt_b

def nat.ofNat_le { a b: Nat } : a ≤ b -> nat.ofNat a ≤ nat.ofNat b := by
  intro a_le_b
  induction a generalizing b with
  | zero => apply zero_le
  | succ a ih =>
    match b with
    | .succ b =>
    apply nat.succ_le_succ
    apply ih
    apply Nat.le_of_succ_le_succ
    exact a_le_b

instance : IsDecidableLinearOrder nat where
