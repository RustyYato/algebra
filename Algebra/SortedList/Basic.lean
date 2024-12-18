import Algebra.Nat.Add
import Algebra.MyOption
import Algebra.Order.Defs

variable [LE α] [LT α] [IsLinearOrder α] [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] [DecidableEq α]

def is_sorted (list: List α) : Prop := match list with
  | [] => True
  | x :: xs => match xs with
    | [] => True
    | y :: _ => x ≤ y ∧ is_sorted xs

def dec_and (_: Decidable P) (_: Decidable Q): Decidable (P ∧ Q) := inferInstance
def dec_or (_: Decidable P) (_: Decidable Q): Decidable (P ∨ Q) := inferInstance

def is_sorted.pop (x: α) (xs: List α) :
  is_sorted (x::xs) -> is_sorted xs := by
  intro is_sorted_xs
  match xs with
  | .nil => trivial
  | .cons x' xs => exact is_sorted_xs.right

def is_sorted.push (x: α) (xs: List α) :
  is_sorted xs -> (∀y, y ∈ xs -> x ≤ y) -> is_sorted (x::xs) := by
  intro is_sorted_xs x_lower_bound
  match xs with
  | .nil => trivial
  | .cons x' xs =>
    apply And.intro
    exact x_lower_bound x' (.head _)
    assumption

def is_sorted.first (x: α) (xs: List α) :
  is_sorted (x::xs) -> ∀y, y ∈ xs -> x ≤ y := by
  intro sorted_xs y y_in_xs
  match xs with
  | .cons x' xs' =>
    cases y_in_xs
    exact sorted_xs.left
    apply le_trans
    exact sorted_xs.left
    apply is_sorted.first
    exact sorted_xs.right
    assumption

def is_sorted.contains (z x: α) (xs: List α) :
  is_sorted (x::xs) ->
  z ∈ (x::xs) -> x ≤ z:= by
  intro sorted_xs z_in_xs
  cases z_in_xs with
  | head _ => apply le_refl
  | tail _ tail_mem => match xs with
    | .cons x' xs' =>
      apply le_trans
      exact sorted_xs.left
      apply is_sorted.contains
      exact sorted_xs.pop
      assumption

def is_sorted.pop_snd (x x': α) (xs: List α) :
  is_sorted (x :: x' :: xs) -> is_sorted (x :: xs) := by
  intro sorted_xs
  have lower_x' := (sorted_xs.pop).first
  apply is_sorted.push
  exact (sorted_xs.pop).pop
  intro y y_in_xs
  have x'_le_y := lower_x' y y_in_xs
  apply le_trans sorted_xs.left x'_le_y

def is_sorted.pick_first:
  ∀{a x: α} {xs: List α},
  is_sorted (x::xs) ->
  a ∈ (x::xs) ->
  (∀y, y ∈ (x::xs) -> a ≤ y) ->
  a = x := by
    intro a x xs sorted_xs elem all_less
    cases elem with
    | head _ => rfl
    | tail _ elem =>
      induction elem with
      | head _ =>
        apply le_antisymm
        exact all_less x (.head _)
        exact sorted_xs.left
      | tail head _ ih =>
        apply ih
        exact sorted_xs.pop_snd
        intro y elem
        apply all_less
        cases elem with
        | head => exact .head _
        | tail _ _ =>
          apply List.Mem.tail
          apply List.Mem.tail
          assumption

instance is_sorted.dec (xs: List α) : Decidable (is_sorted xs) :=
  match xs with
  | [] => Decidable.isTrue True.intro
  | x::xs => match xs with
    | [] => Decidable.isTrue True.intro
    | y::ys => by
      unfold is_sorted
      apply dec_and
      exact inferInstance
      apply is_sorted.dec

structure SortedList (α: Sort _) [LE α] where
  items: List α
  is_sorted : is_sorted items

structure SortedIndCtx (α: Sort _) [LT α] where
  motive: List α -> List α -> Sort _
  left_empty: ∀list, motive [] list
  right_empty: ∀x xs, motive (x::xs) []
  if_lt: ∀x y xs ys, x < y -> motive xs (y::ys) -> motive (x::xs) (y::ys)
  if_gt: ∀x y xs ys, x > y -> motive (x::xs) ys -> motive (x::xs) (y::ys)
  if_eq: ∀x y xs ys, x = y -> motive xs ys -> motive (x::xs) (y::ys)
variable (ctx: SortedIndCtx α)

def List.len (list: List α) : nat := match list with
  | .nil => .zero
  | .cons _ xs => xs.len.succ

def List.len_empty : ([]: List α).len = 0 := rfl

inductive Compare (x y: α) where
| Lt : x < y -> Compare x y
| Eq : x = y -> Compare x y
| Gt : x > y -> Compare x y

def compare (x y: α) : Compare x y :=
  if h₀:x ≤ y then
    if h₁:y ≤ x then
      .Eq (le_antisymm h₀ h₁)
    else
      .Lt (lt_of_not_le h₁)
  else
      .Gt (lt_of_not_le h₀)

def sorted_induction.fueled
  : ∀(_fuel: nat) xs ys, my_option (ctx.motive xs ys)
| .zero, _, _ => .none
| .succ fuel, xs, ys => by
  match xs with
  | .nil =>
    exact .some <| ctx.left_empty _
  | .cons x xs =>
    match ys with
    | .nil => exact .some <| ctx.right_empty _ _
    | .cons y ys =>
      have ih := sorted_induction.fueled fuel
      match compare x y with
      | .Lt x_lt_y =>
        apply (ih xs (y::ys)).map
        intro ih
        apply ctx.if_lt
        repeat assumption
      | .Eq x_eq_y =>
        apply (ih xs ys).map
        intro ih
        apply ctx.if_eq
        repeat assumption
      | .Gt x_gt_y =>
        apply (ih (x::xs) ys).map
        intro ih
        apply ctx.if_gt
        repeat assumption

def enough_fuel_for_lt
  {x:α} {xs ys: List α} {fuel: nat}:
  (x::xs).len + ys.len < fuel.succ ->
  xs.len + ys.len < fuel := by
  intro enough_fuel
  apply lt_of_lt_of_le _ (nat.le_of_lt_succ enough_fuel)
  have : List.len (x::xs) = xs.len.succ := rfl
  rw [this]
  rw [nat.succ_add]
  apply nat.lt_succ_self

def enough_fuel_for_eq
  {x y:α} {xs ys: List α} {fuel: nat}:
  (x::xs).len + (y::ys).len < fuel.succ ->
  xs.len + ys.len < fuel := by
  intro enough_fuel
  apply lt_of_lt_of_le _ (nat.le_of_lt_succ enough_fuel)
  have : List.len (x::xs) = xs.len.succ := rfl
  rw [this]
  have : List.len (y::ys) = ys.len.succ := rfl
  rw [this]
  rw [nat.add_succ, nat.succ_add]
  apply lt_trans
  repeat apply nat.lt_succ_self

def enough_fuel_for_gt
  {y:α} {xs ys: List α} {fuel: nat}:
  xs.len + (y::ys).len < fuel.succ ->
  xs.len + ys.len < fuel := by
  intro enough_fuel
  apply lt_of_lt_of_le _ (nat.le_of_lt_succ enough_fuel)
  have : List.len (y::ys) = ys.len.succ := rfl
  rw [this]
  rw [nat.add_succ]
  apply nat.lt_succ_self

def sorted_induction.fueled.termination:
  ∀(fuel: nat) xs ys,  xs.len + ys.len < fuel ->
    (sorted_induction.fueled ctx fuel xs ys) ≠ .none := by
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
        intro
        contradiction
      | _::_, [] =>
        unfold fueled
        intro
        contradiction
      | x::xs, y::ys =>
        unfold fueled
        match h:compare x y with
        | .Lt x_lt_y =>
          simp only
          rw [h]
          simp only
          unfold my_option.map
          split
          rename_i heq
          have := ih xs (y::ys) (enough_fuel_for_lt enough_fuel)
          rw [heq] at this
          contradiction
          intro
          trivial
        | .Gt x_gt_y =>
          simp only
          rw [h]
          simp only
          unfold my_option.map
          split
          rename_i heq
          have := ih (x::xs) ys (enough_fuel_for_gt enough_fuel)
          rw [heq] at this
          contradiction
          intro
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
          intro
          trivial

def sorted_induction.fueled.fuel_irr:
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
          have := ih fuel_b xs (y::ys) (nat.lt_of_succ_lt_succ enough_fuel_a) (nat.lt_of_succ_lt_succ enough_fuel_b)
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

def sorted_induction:
  ∀(xs ys: List α), ctx.motive xs ys :=
  fun xs ys =>
  match h:sorted_induction.fueled ctx (xs.len + ys.len).succ xs ys with
  | .some m => m
  | .none => by
    have := sorted_induction.fueled.termination ctx (xs.len + ys.len).succ xs ys nat.lt_succ_self
    rw [h] at this
    contradiction

def sorted_induction.of_fueled:
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

def sorted_induction.fueled.left_empty:
  ∀fuel (ys: List α), ys.len < fuel -> sorted_induction.fueled ctx fuel [] ys = .some (ctx.left_empty ys) := by
    intro fuel ys enough_fuel
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
    unfold fueled
    rfl

def sorted_induction.fueled.right_empty:
  ∀fuel (x:α) (xs: List α), (x::xs).len < fuel -> sorted_induction.fueled ctx fuel (x::xs) [] = .some (ctx.right_empty x xs) := by
    intro fuel x xs enough_fuel
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
    unfold fueled
    rfl

def Exists.val (α: Prop) { z: α -> Prop } (a: ∃(x: α), z x): α := match a with
  | .intro x _ => x

def sorted_induction.fueled.if_lt:
  ∀fuel (x y:α) (xs ys: List α),
    (x::xs).len + (y::ys).len < fuel ->
    (foo: ∃a, compare x y = .Lt a) ->
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_lt x y xs ys foo.val (sorted_induction ctx xs (y::ys))) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
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
    exact enough_fuel_for_lt enough_fuel

def sorted_induction.fueled.if_gt:
  ∀fuel (x y:α) (xs ys: List α),
    (x::xs).len + (y::ys).len < fuel ->
    (foo: ∃a, compare x y = .Gt a) ->
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_gt x y xs ys foo.val (sorted_induction ctx (x::xs) ys) ) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
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
    exact enough_fuel_for_gt enough_fuel

def sorted_induction.fueled.if_eq:
  ∀fuel (x y:α) (xs ys: List α),
    (x::xs).len + (y::ys).len < fuel ->
    (foo: ∃a, compare x y = .Eq a) ->
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_eq x y xs ys foo.val (sorted_induction ctx xs ys)) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
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

def sorted_induction.left_empty:
  ∀(ys: List α), sorted_induction ctx [] ys = ctx.left_empty ys := by
    intro ys
    unfold sorted_induction
    split
    rw [sorted_induction.fueled.left_empty] at *
    rename_i h
    exact my_option.some.inj h.symm
    apply nat.lt_succ_self
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ nat.lt_succ_self h

def sorted_induction.right_empty:
  ∀(x:α) (xs: List α), sorted_induction ctx (x::xs) [] = ctx.right_empty x xs := by
    intro x xs
    unfold sorted_induction
    split
    rw [sorted_induction.fueled.right_empty] at *
    rename_i h
    exact my_option.some.inj h.symm
    rw [List.len_empty, nat.add_zero]
    apply nat.lt_succ_self
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ nat.lt_succ_self h

def sorted_induction.if_lt:
  ∀(x y:α) (xs ys: List α),
  (x_lt_y: x < y) ->
  sorted_induction ctx (x::xs) (y::ys) = ctx.if_lt x y xs ys x_lt_y (sorted_induction ctx xs (y::ys)) := by
    intro x y xs ys x_lt_y
    conv => {
      lhs
      unfold sorted_induction
    }
    split
    rw [sorted_induction.fueled.if_lt] at *
    rename_i h
    exact my_option.some.inj h.symm
    apply nat.lt_succ_self
    {
      exists x_lt_y
      cases h:compare x y with
      | Lt _ => rfl
      | Gt x_gt_y =>
        have := lt_asymm x_lt_y x_gt_y
        contradiction
      | Eq x_eq_y =>
        rw [x_eq_y] at x_lt_y
        have := lt_irrefl x_lt_y
        contradiction
    }
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ nat.lt_succ_self h

def sorted_induction.if_gt:
  ∀(x y:α) (xs ys: List α),
    (x_gt_y: x > y) ->
    sorted_induction ctx (x::xs) (y::ys) = ctx.if_gt x y xs ys x_gt_y (sorted_induction ctx (x::xs) ys) := by
    intro x y xs ys x_gt_y
    conv => {
      lhs
      unfold sorted_induction
    }
    split
    rw [sorted_induction.fueled.if_gt] at *
    rename_i h
    exact my_option.some.inj h.symm
    apply nat.lt_succ_self
    {
      exists x_gt_y
      cases h:compare x y with
      | Lt x_lt_y =>
        have := lt_asymm x_lt_y x_gt_y
        contradiction
      | Gt x_gt_y => rfl
      | Eq x_eq_y =>
        rw [x_eq_y] at x_gt_y
        have := lt_irrefl x_gt_y
        contradiction
    }
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ nat.lt_succ_self h

def sorted_induction.if_eq:
  ∀(x y:α) (xs ys: List α),
    (x_eq_y: x = y) ->
    sorted_induction ctx (x::xs) (y::ys) = ctx.if_eq x y xs ys x_eq_y (sorted_induction ctx xs ys) := by
    intro x y xs ys x_eq_y
    conv => {
      lhs
      unfold sorted_induction
    }
    split
    rw [sorted_induction.fueled.if_eq] at *
    rename_i h
    exact my_option.some.inj h.symm
    apply nat.lt_succ_self
    {
      exists x_eq_y
      cases h:compare x y with
      | Lt x_lt_y =>
        rw [x_eq_y] at x_lt_y
        have := lt_irrefl x_lt_y
        contradiction
      | Gt x_gt_y =>
        rw [x_eq_y] at x_gt_y
        have := lt_irrefl x_gt_y
        contradiction
      | Eq _ => rfl
    }
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ nat.lt_succ_self h

def sorted_induction'
  (motive: List α -> List α -> Sort _)
  {left_empty: ∀ys, motive [] ys}
  {right_empty: ∀x xs, motive (x::xs) []}
  {if_lt: ∀x y xs ys, x < y -> motive xs (y::ys) -> motive (x::xs) (y::ys)}
  {if_gt: ∀x y xs ys, x > y -> motive (x::xs) ys -> motive (x::xs) (y::ys)}
  {if_eq: ∀x y xs ys, x = y -> motive xs ys -> motive (x::xs) (y::ys)}:
  ∀(xs ys: List α), motive xs ys :=
  fun xs ys =>sorted_induction (SortedIndCtx.mk motive left_empty right_empty if_lt if_gt if_eq) xs ys
