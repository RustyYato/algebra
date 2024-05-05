import Algebra.Nat.Add
import Algebra.MyOption

inductive OrderingLe (α: Sort _) [LE α] (x y: α) where
  | Lt : x ≤ y -> x ≠ y -> OrderingLe α x y
  | Eq : x = y -> OrderingLe α x y
  | Gt : x ≥ y -> x ≠ y -> OrderingLe α x y


class TrustedLE (α: Sort _) [LE α] where
  le_trans (a b c: α) : a ≤ b -> b ≤ c -> a ≤ c
  le_refl (a: α) : a ≤ a
  le_antisymm (a b: α) : a ≤ b -> b ≤ a -> a = b
  decide_ord (a b: α): OrderingLe α a b
  

def is_sorted [LE α] [TrustedLE α] (list: List α) : Prop := match list with
  | [] => True
  | x :: xs => match xs with
    | [] => True
    | y :: _ => x ≤ y ∧ is_sorted xs

structure SortedList (α: Sort _) [LE α] [TrustedLE α] where
  items: List α
  is_sorted : is_sorted items

structure SortedIndCtx (α: Sort _) [LE α] [TrustedLE α] where
  motive: List α -> List α -> Sort _
  left_empty: ∀list, motive [] list
  right_empty: ∀x xs, motive (x::xs) []
  if_lt: ∀x y xs ys, x ≤ y -> x ≠ y -> motive xs (y::ys) -> motive (x::xs) (y::ys)
  if_gt: ∀x y xs ys, x ≥ y -> x ≠ y -> motive (x::xs) ys -> motive (x::xs) (y::ys)
  if_eq: ∀x y xs ys, x = y -> motive xs ys -> motive (x::xs) (y::ys)

def List.len (list: List α) : nat := match list with
  | .nil => .zero
  | .cons _ xs => xs.len.succ

def sorted_induction.fueled
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α)
  : ∀(fuel: nat) xs ys, my_option (ctx.motive xs ys) := by
    intro fuel xs ys
    match fuel with
    | .zero => exact .none
    | .succ fuel =>
    match xs with
    | .nil =>
      exact .some <| ctx.left_empty _
    | .cons x xs =>
      match ys with
      | .nil => exact .some <| ctx.right_empty _ _
      | .cons y ys =>
        have ih := sorted_induction.fueled ctx fuel
        match tle.decide_ord x y with
        | .Lt x_le_y x_ne_y =>
          apply (ih xs (y::ys)).map
          intro ih
          apply ctx.if_lt
          repeat assumption
        | .Eq x_eq_y =>
          apply (ih xs ys).map
          intro ih
          apply ctx.if_eq
          repeat assumption
        | .Gt x_ge_y x_ne_y =>
          apply (ih (x::xs) ys).map
          intro ih
          apply ctx.if_gt
          repeat assumption

#print axioms sorted_induction.fueled

def enough_fuel_for_lt
  {x:α} {xs ys: List α} {fuel: nat}:
  (x::xs).len + ys.len < fuel.succ -> 
  xs.len + ys.len < fuel := by
  intro enough_fuel
  apply nat.lt_of_lt_and_le _ (nat.le_of_lt_succ enough_fuel)
  have : List.len (x::xs) = xs.len.succ := rfl
  rw [this]
  rw [nat.succ_add]
  apply nat.lt_succ_self

def enough_fuel_for_eq
  {x y:α} {xs ys: List α} {fuel: nat}:
  (x::xs).len + (y::ys).len < fuel.succ -> 
  xs.len + ys.len < fuel := by
  intro enough_fuel
  apply nat.lt_of_lt_and_le _ (nat.le_of_lt_succ enough_fuel)
  have : List.len (x::xs) = xs.len.succ := rfl
  rw [this]
  have : List.len (y::ys) = ys.len.succ := rfl
  rw [this]
  rw [nat.add_succ, nat.succ_add]
  apply nat.lt_trans
  repeat apply nat.lt_succ_self

def enough_fuel_for_gt
  {y:α} {xs ys: List α} {fuel: nat}:
  xs.len + (y::ys).len < fuel.succ -> 
  xs.len + ys.len < fuel := by
  intro enough_fuel
  apply nat.lt_of_lt_and_le _ (nat.le_of_lt_succ enough_fuel)
  have : List.len (y::ys) = ys.len.succ := rfl
  rw [this]
  rw [nat.add_succ]
  apply nat.lt_succ_self
    

def sorted_induction.fueled.termination
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀(fuel: nat) xs ys,  xs.len + ys.len < fuel ->
    (sorted_induction.fueled ctx fuel xs ys).is_some := by
    intro fuel xs ys enough_fuel
    induction fuel generalizing xs ys with
    | zero => 
      unfold fueled
      have := nat.not_lt_zero enough_fuel
      contradiction
    | succ fuel ih =>
      match xs, ys with
      | [], _ =>
        unfold fueled
        trivial
      | _::_, [] =>
        unfold fueled
        trivial
      | x::xs, y::ys =>
        unfold fueled
        match h:tle.decide_ord x y with
        | .Lt x_le_y x_ne_y =>
          simp only
          rw [h]
          simp only
          unfold my_option.map
          split
          rename_i heq
          have := ih xs (y::ys) (enough_fuel_for_lt enough_fuel)
          rw [heq] at this
          contradiction
          trivial
        | .Gt x_ge_y x_ne_y =>
          simp only
          rw [h]
          simp only
          unfold my_option.map
          split
          rename_i heq
          have := ih (x::xs) ys (enough_fuel_for_gt enough_fuel)
          rw [heq] at this
          contradiction
          trivial  
        | .Eq x_eq_y =>
          simp only
          rw [h]
          simp only
          unfold my_option.map
          split
          rename_i heq
          have := ih xs ys (enough_fuel_for_eq enough_fuel)
          rw [heq] at this
          contradiction
          trivial

#print axioms sorted_induction.fueled.termination

axiom Test { α } : α

def sorted_induction.fueled.fuel_irr
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀(fuel_a fuel_b: nat) (xs ys: List α),
  xs.len + ys.len < fuel_a ->
  xs.len + ys.len < fuel_b ->
  sorted_induction.fueled ctx fuel_a xs ys = sorted_induction.fueled ctx fuel_b xs ys := by
    intro fuel_a fuel_b xs ys enough_fuel_a enough_fuel_b
    induction fuel_a generalizing fuel_b xs ys with
    | zero => 
      unfold fueled
      have := nat.not_lt_zero enough_fuel_a
      contradiction
    | succ fuel_a ih =>
      cases fuel_b with
      | zero => 
        unfold fueled
        have := nat.not_lt_zero enough_fuel_b
        contradiction
      | succ fuel_b =>
      match xs, ys with
      | [], _ =>
        unfold fueled
        trivial
      | _::_, [] =>
        unfold fueled
        trivial
      | x::xs, y::ys =>
        unfold fueled
        simp only
        split
        {
          have := ih fuel_b xs (y::ys) enough_fuel_a enough_fuel_b
          rw [this]
        }
        {
          have := ih fuel_b xs ys (enough_fuel_for_eq enough_fuel_a) (enough_fuel_for_eq enough_fuel_b)
          rw [this]
        }
        {
          have := ih fuel_b (x::xs) ys (enough_fuel_for_gt enough_fuel_a) (enough_fuel_for_gt enough_fuel_b)
          rw [this]
        }

#print axioms sorted_induction.fueled.fuel_irr

def sorted_induction
  { α: Sort _ }
  [LE α] [TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀(xs ys: List α), ctx.motive xs ys :=
  fun xs ys =>
  match h:sorted_induction.fueled ctx (xs.len + ys.len).succ xs ys with
  | .some m => m
  | .none => by
    have := sorted_induction.fueled.termination ctx (xs.len + ys.len).succ xs ys (nat.lt_succ_self _)
    rw [h] at this
    contradiction

def sorted_induction.of_fueled
  { α: Sort _ }
  [LE α] [TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀xs ys: List α, ∀fuel,
  xs.len + ys.len < fuel ->
  sorted_induction.fueled ctx fuel xs ys = .some (sorted_induction ctx xs ys) := by
  intro xs ys fuel enough_fuel
  match fuel with
  | .zero =>
    have := nat.not_lt_zero enough_fuel
    contradiction
  | .succ fuel =>
    unfold sorted_induction
    split
    {
      rename_i h
      rw [←h]
      clear h
      apply sorted_induction.fueled.fuel_irr
      assumption
      apply nat.lt_succ_self
    }
    {
      have := sorted_induction.fueled.termination ctx fuel.succ xs ys  enough_fuel
      rename_i h
      rw [sorted_induction.fueled.fuel_irr] at this
      rw [h] at this
      contradiction
      assumption
      apply nat.lt_succ_self
    }

#print axioms sorted_induction.of_fueled

def sorted_induction.fueled.left_empty
  { α: Sort _ }
  [LE α] [TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀fuel (ys: List α), ys.len < fuel -> sorted_induction.fueled ctx fuel [] ys = .some (ctx.left_empty ys) := by
    intro fuel ys enough_fuel
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
    unfold fueled
    rfl

#print axioms sorted_induction.fueled.left_empty

def sorted_induction.fueled.right_empty
  { α: Sort _ }
  [LE α] [TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀fuel (x:α) (xs: List α), (x::xs).len < fuel -> sorted_induction.fueled ctx fuel (x::xs) [] = .some (ctx.right_empty x xs) := by
    intro fuel x xs enough_fuel
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
    unfold fueled
    rfl

#print axioms sorted_induction.fueled.right_empty

def Exists.fst_val (α: Prop) { z: α -> β -> Prop } (a: ∃(x: α) (y: β), z x y): α := match a with
  | .intro x _ => x
def Exists.snd_val (α: Prop) { z: β -> α -> Prop } (a: ∃(x: β) (y: α), z x y): α:= match a with
  | .intro _ (.intro y _) => y
def Exists.val (α: Prop) { z: α -> Prop } (a: ∃(x: α), z x): α := match a with
  | .intro x _ => x

def sorted_induction.fueled.if_lt
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀fuel (x y:α) (xs ys: List α),
    (x::xs).len + (y::ys).len < fuel ->
    (foo: ∃a b, tle.decide_ord x y = .Lt a b) ->
    ∃prev,
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_lt x y xs ys foo.fst_val foo.snd_val prev) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
    exists (sorted_induction ctx xs (y::ys))
    unfold fueled
    have ⟨ a, b, dec_ord ⟩ := dec_ord
    simp only
    conv => {
      lhs
      rw [dec_ord]
    }
    simp only
    unfold my_option.map
    rw [sorted_induction.of_fueled]
    exact enough_fuel_for_lt enough_fuel

#print axioms sorted_induction.fueled.if_lt

def sorted_induction.fueled.if_gt
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀fuel (x y:α) (xs ys: List α),
    (x::xs).len + (y::ys).len < fuel ->
    (foo: ∃a b, tle.decide_ord x y = .Gt a b) ->
    ∃prev,
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_gt x y xs ys foo.fst_val foo.snd_val prev) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
    exists (sorted_induction ctx (x::xs) ys)
    unfold fueled
    have ⟨ a, b, dec_ord ⟩ := dec_ord
    simp only
    conv => {
      lhs
      rw [dec_ord]
    }
    simp only
    unfold my_option.map
    rw [sorted_induction.of_fueled]
    exact enough_fuel_for_gt enough_fuel

#print axioms sorted_induction.fueled.if_gt

def sorted_induction.fueled.if_eq
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀fuel (x y:α) (xs ys: List α),
    (x::xs).len + (y::ys).len < fuel ->
    (foo: ∃a, tle.decide_ord x y = .Eq a) ->
    ∃prev,
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_eq x y xs ys foo.val prev) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
    exists (sorted_induction ctx xs ys)
    unfold fueled
    have ⟨ a, dec_ord ⟩ := dec_ord
    simp only
    conv => {
      lhs
      rw [dec_ord]
    }
    simp only
    unfold my_option.map
    rw [sorted_induction.of_fueled]
    exact enough_fuel_for_eq enough_fuel

#print axioms sorted_induction.fueled.if_eq

