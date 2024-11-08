import Algebra.Order.Defs
import Algebra.Int.Basic
import Algebra.Nat.Cmp

inductive int.LT : int -> int -> Prop where
| neg_pos: int.LT (.neg_succ _) (.pos_succ _)
| zero_pos: int.LT .zero (.pos_succ _)
| neg_zero: int.LT (.neg_succ _) .zero
| neg : a < b -> int.LT (.neg_succ b) (.neg_succ a)
| pos : a < b -> int.LT (.pos_succ a) (.pos_succ b)

inductive int.LE : int -> int -> Prop where
| neg_pos: int.LE (.neg_succ _) (.pos_succ _)
| zero_pos: int.LE .zero (.pos_succ _)
| neg_zero: int.LE (.neg_succ _) .zero
| zero : int.LE .zero .zero
| neg : a ≤ b -> int.LE (.neg_succ b) (.neg_succ a)
| pos : a ≤ b -> int.LE (.pos_succ a) (.pos_succ b)

instance : LT int := ⟨int.LT⟩
instance : LE int := ⟨int.LE⟩

def int.neg_lt_zero : int.neg_succ n < 0 := .neg_zero
def int.pos_lt_zero : 0 < int.pos_succ n := .zero_pos
def int.neg_lt_pos : int.neg_succ n < int.pos_succ m := .neg_pos

def int.neg_le_zero : int.neg_succ n ≤ 0 := .neg_zero
def int.zero_le_pos : 0 ≤ int.pos_succ n := .zero_pos
def int.neg_le_pos : int.neg_succ n ≤ int.pos_succ m := .neg_pos

def int.lt.pos_nat (a: nat) : 0 < a -> 0 < int.of_nat a := by
  intro h
  cases h
  exact .zero_pos

def int.cast_lt : a < b -> int.LT a b := id
def int.cast_le : a ≤ b -> int.LE a b := id

instance int.decLE (a b: int) : Decidable (a ≤ b) := by
  cases a <;> cases b
  any_goals
    apply Decidable.isFalse
    intro h
    contradiction
  exact .isTrue .zero
  exact .isTrue .zero_pos
  rename_i a b
  if h:a ≤ b then
    exact .isTrue (.pos h)
  else
    apply Decidable.isFalse
    intro h
    cases h; contradiction
  exact .isTrue .neg_zero
  exact .isTrue .neg_pos
  rename_i a b
  if h:b ≤ a then
    exact .isTrue (.neg h)
  else
    apply Decidable.isFalse
    intro h
    cases h; contradiction
instance : Min int := minOfLe
instance : Max int := maxOfLe

def int.of_nat.le {a b: nat} : int.of_nat a ≤ int.of_nat b ↔ a ≤ b := by
  cases a <;> cases b
  exact ⟨fun _ => .zero _, fun _ => .zero⟩
  exact ⟨fun _ => .zero _, fun _ => .zero_pos⟩
  exact ⟨(nomatch ·), (nomatch ·)⟩
  exact ⟨fun (int.LE.pos h) => (nat.succ_le_succ h), int.LE.pos ∘ nat.le_of_succ_le_succ⟩

def int.of_nat.lt {a b: nat} : int.of_nat a < int.of_nat b ↔ a < b := by
  cases a <;> cases b
  exact ⟨(nomatch ·), (nomatch ·)⟩
  exact ⟨fun _ => .zero _, fun _ => .zero_pos⟩
  exact ⟨(nomatch ·), (nomatch ·)⟩
  exact ⟨fun (int.LT.pos h) => (nat.succ_lt_succ h), int.LT.pos ∘ nat.lt_of_succ_lt_succ⟩


instance : IsLinearOrder int where
  lt_iff_le_and_not_le := by
    intro a b
    cases a <;> cases b
    any_goals
      apply Iff.intro
      try
        intro
        contradiction
      try
        intro ⟨_,_⟩
        contradiction
    any_goals
      try intro ⟨h₀,h₁⟩
    any_goals
      intro h
      apply And.intro
    any_goals apply int.LE.zero_pos
    any_goals apply int.LE.neg_pos
    any_goals apply int.LE.neg_zero
    any_goals apply int.LT.zero_pos
    any_goals apply int.LT.neg_pos
    any_goals apply int.LT.neg_zero
    any_goals
      intro
      contradiction
    any_goals cases h
    any_goals cases h₀
    any_goals apply int.LE.pos
    any_goals apply int.LE.neg
    any_goals apply int.LT.pos
    any_goals apply int.LT.neg
    any_goals
      apply le_of_lt
      assumption
    intro h
    cases h
    apply not_lt_of_le (α:=nat) <;> assumption
    rename_i h
    cases lt_or_eq_of_le h <;> rename_i h
    assumption
    subst h
    exfalso
    apply h₁
    apply int.LE.pos
    rfl
    intro h
    cases h
    apply not_lt_of_le (α:=nat) <;> assumption
    rename_i h
    cases lt_or_eq_of_le h <;> rename_i h
    assumption
    subst h
    exfalso
    apply h₁
    apply int.LE.neg
    rfl
  le_antisymm := by
    intro a b ab ba
    induction ab
    any_goals contradiction
    rfl
    congr
    cases ba
    apply le_antisymm <;> assumption
    congr
    cases ba
    apply le_antisymm <;> assumption
  le_total := by
    intro a b
    cases a <;> cases b
    apply Or.inl; exact .zero
    apply Or.inl
    exact .zero_pos
    apply Or.inr
    exact .neg_zero
    apply Or.inr
    exact .zero_pos
    rename_i a b
    cases le_total a b
    apply Or.inl; exact .pos (by assumption)
    apply Or.inr; exact .pos (by assumption)
    apply Or.inr .neg_pos
    apply Or.inl .neg_zero
    apply Or.inl .neg_pos
    rename_i a b
    cases le_total a b
    apply Or.inr; exact .neg (by assumption)
    apply Or.inl; exact .neg (by assumption)
  le_complete := by
    intro a b
    cases a <;> cases b
    apply Or.inl; exact .zero
    apply Or.inl
    exact .zero_pos
    apply Or.inr; intro h; contradiction
    apply Or.inr; intro h; contradiction
    rename_i a b
    cases le_complete a b
    apply Or.inl; exact .pos (by assumption)
    apply Or.inr; intro h; cases h; contradiction
    apply Or.inr; intro h; contradiction
    apply Or.inl .neg_zero
    apply Or.inl .neg_pos
    rename_i a b
    cases le_complete b a
    apply Or.inl; exact .neg (by assumption)
    apply Or.inr; intro h; cases h; contradiction
  le_trans := by
    intro a b c ab bc
    induction ab
    cases bc
    exact .neg_pos
    cases bc
    exact .zero_pos
    cases bc
    exact .neg_pos
    exact .neg_zero
    assumption
    cases bc
    exact .neg_pos
    exact .neg_zero
    apply int.LE.neg
    apply le_trans <;> assumption
    cases bc
    apply int.LE.pos
    apply le_trans <;> assumption

instance : IsDecidableLinearOrder int where
