import Algebra.Nat.Add
import Algebra.MyOption

inductive OrderingLe (α: Sort _) [LE α] (x y: α) where
  | Lt : x ≤ y -> x ≠ y -> OrderingLe α x y
  | Eq : x = y -> OrderingLe α x y
  | Gt : x ≥ y -> x ≠ y -> OrderingLe α x y

class TrustedLE (α: Sort _) [LE α] where
  le_trans (a b c: α) : a ≤ b -> b ≤ c -> a ≤ c
  lt_trans (a b c: α) : a ≤ b ∧ a ≠ b -> b ≤ c ∧ b ≠ c -> a ≤ c ∧ a ≠ c
  lt_of_lt_and_le (a b c: α) : a ≤ b ∧ a ≠ b -> b ≤ c -> a ≤ c ∧ a ≠ c
  lt_of_le_and_lt (a b c: α) : a ≤ b -> b ≤ c ∧ b ≠ c -> a ≤ c ∧ a ≠ c
  le_refl (a: α) : a ≤ a
  le_antisymm (a b: α) : a ≤ b -> b ≤ a -> a = b
  decide_ord (a b: α): OrderingLe α a b

instance dec_eq_of_trusted_le [LE α] [tle: TrustedLE α] : DecidableEq α := by
  intro a b
  match tle.decide_ord a b with
  | .Lt _ _ | .Gt _ _ => apply Decidable.isFalse; assumption
  | .Eq _ =>  apply Decidable.isTrue; assumption

instance : TrustedLE nat where
  le_trans _ _ _ := nat.le_trans
  lt_trans a b c := by
    intro a_lt_b b_lt_c
    have a_lt_b : a < b := by
      cases nat.lt_or_eq_of_le a_lt_b.left
      assumption
      have := a_lt_b.right
      contradiction
    have b_lt_c : b < c := by
      cases nat.lt_or_eq_of_le b_lt_c.left
      assumption
      have := b_lt_c.right
      contradiction
    have a_lt_c := nat.lt_trans a_lt_b b_lt_c
    apply And.intro
    exact nat.le_of_lt a_lt_c
    intro a_eq_c
    rw [a_eq_c] at a_lt_c
    have := nat.lt_irrefl _ a_lt_c
    contradiction
  lt_of_le_and_lt a b c := by
    intro a_lt_b b_lt_c
    have b_lt_c : b < c := by
      cases nat.lt_or_eq_of_le b_lt_c.left
      assumption
      have := b_lt_c.right
      contradiction
    have a_lt_c := nat.lt_of_le_and_lt a_lt_b b_lt_c
    apply And.intro
    exact nat.le_of_lt a_lt_c
    intro a_eq_c
    rw [a_eq_c] at a_lt_c
    have := nat.lt_irrefl _ a_lt_c
    contradiction
  lt_of_lt_and_le a b c := by
    intro a_lt_b b_lt_c
    have a_lt_b : a < b := by
      cases nat.lt_or_eq_of_le a_lt_b.left
      assumption
      have := a_lt_b.right
      contradiction
    have a_lt_c := nat.lt_of_lt_and_le a_lt_b b_lt_c
    apply And.intro
    exact nat.le_of_lt a_lt_c
    intro a_eq_c
    rw [a_eq_c] at a_lt_c
    have := nat.lt_irrefl _ a_lt_c
    contradiction

  le_refl := nat.le_refl
  le_antisymm _ _ := nat.le_antisymm
  decide_ord a b := match h:a.cmp b with
    | .lt => by
      apply OrderingLe.Lt
      apply nat.le_of_lt
      assumption
      intro a_eq_b
      rw [a_eq_b] at h
      rw [nat.cmp_refl b] at h
      contradiction
    | .gt => by
      apply OrderingLe.Gt
      apply nat.ge_of_gt
      apply nat.gt_of_cmp
      assumption
      intro a_eq_b
      rw [a_eq_b] at h
      rw [nat.cmp_refl b] at h
      contradiction
    | .eq => by
      apply OrderingLe.Eq
      apply nat.eq_of_cmp
      assumption

def is_sorted [LE α] [TrustedLE α] (list: List α) : Prop := match list with
  | [] => True
  | x :: xs => match xs with
    | [] => True
    | y :: _ => x ≤ y ∧ is_sorted xs

def dec_and (_: Decidable P) (_: Decidable Q): Decidable (P ∧ Q) := inferInstance
def dec_or (_: Decidable P) (_: Decidable Q): Decidable (P ∨ Q) := inferInstance

def is_sorted.pop [LE α] [TrustedLE α] (x: α) (xs: List α) :
  is_sorted (x::xs) -> is_sorted xs := by
  intro is_sorted_xs
  match xs with
  | .nil => trivial
  | .cons x' xs => exact is_sorted_xs.right

def is_sorted.first [LE α] [tle: TrustedLE α] (x: α) (xs: List α) :
  is_sorted (x::xs) -> ∀y, y ∈ xs -> x ≤ y := by
  intro sorted_xs y y_in_xs
  match xs with
  | .cons x' xs' =>
    cases y_in_xs
    exact sorted_xs.left
    apply tle.le_trans
    exact sorted_xs.left
    apply is_sorted.first
    exact sorted_xs.right
    assumption

#print axioms is_sorted.first

instance TrustedLE.dec_le [LE α] [tle: TrustedLE α] (x y: α) : Decidable (x ≤ y) := 
  match tle.decide_ord x y with
  | .Lt x_le_y _ => Decidable.isTrue x_le_y
  | .Eq x_eq_y => Decidable.isTrue (by
    rw [x_eq_y]
    apply tle.le_refl)
  | .Gt x_ge_y x_ne_y => Decidable.isFalse (by
    intro x_le_y
    have := tle.le_antisymm _ _ x_le_y x_ge_y
    contradiction)

#print axioms TrustedLE.dec_le

instance is_sorted.dec [LE α] [TrustedLE α] (xs: List α) : Decidable (is_sorted xs) := 
  match xs with
  | [] => Decidable.isTrue True.intro
  | x::xs => match xs with
    | [] => Decidable.isTrue True.intro
    | y::ys => by
      unfold is_sorted
      apply dec_and
      exact inferInstance
        
      apply is_sorted.dec

#print axioms is_sorted.dec

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

def List.len_empty : ([]: List α).len = 0 := rfl

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
          intro
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

#print axioms sorted_induction.fueled.termination

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
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_lt x y xs ys foo.fst_val foo.snd_val (sorted_induction ctx xs (y::ys))) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
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
    sorted_induction.fueled ctx fuel (x::xs) (y::ys) = .some (ctx.if_gt x y xs ys foo.fst_val foo.snd_val (sorted_induction ctx (x::xs) ys) ) := by
    intro fuel x y xs ys enough_fuel dec_ord
    match fuel with
    | .zero =>
      have := nat.not_lt_zero enough_fuel
      contradiction
    | .succ fuel =>
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

#print axioms sorted_induction.fueled.if_eq

def sorted_induction.left_empty
  { α: Sort _ }
  [LE α] [TrustedLE α]
  (ctx: SortedIndCtx α):
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
    exact sorted_induction.fueled.termination ctx _ _ _ (nat.lt_succ_self _) h

#print axioms sorted_induction.left_empty

def sorted_induction.right_empty
  { α: Sort _ }
  [LE α] [TrustedLE α]
  (ctx: SortedIndCtx α):
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
    exact sorted_induction.fueled.termination ctx _ _ _ (nat.lt_succ_self _) h

#print axioms sorted_induction.right_empty

def sorted_induction.if_lt
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀(x y:α) (xs ys: List α),
  (x_le_y: x ≤ y) ->
  (x_ne_y: x ≠ y) ->
  sorted_induction ctx (x::xs) (y::ys) = ctx.if_lt x y xs ys x_le_y x_ne_y (sorted_induction ctx xs (y::ys)) := by
    intro x y xs ys x_le_y x_ne_y
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
      exists x_le_y
      exists x_ne_y
      cases h:tle.decide_ord x y with
      | Lt _ _ => rfl
      | Gt x_ge_y _ =>
        have := tle.le_antisymm _ _ x_le_y x_ge_y
        contradiction
      | Eq _ => 
        contradiction
    }
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ (nat.lt_succ_self _) h



#print axioms sorted_induction.if_lt

def sorted_induction.if_gt
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
  ∀(x y:α) (xs ys: List α),
    (x_ge_y: x ≥ y) ->
    (x_ne_y: x ≠ y) ->
    sorted_induction ctx (x::xs) (y::ys) = ctx.if_gt x y xs ys x_ge_y x_ne_y (sorted_induction ctx (x::xs) ys) := by
    intro x y xs ys x_ge_y x_ne_y
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
      exists x_ge_y
      exists x_ne_y
      cases h:tle.decide_ord x y with
      | Lt x_le_y _ => 
        have := tle.le_antisymm _ _ x_le_y x_ge_y
        contradiction
      | Gt _ _ =>
        rfl
      | Eq _ => 
        have := x_ne_y.symm
        contradiction
    }
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ (nat.lt_succ_self _) h

#print axioms sorted_induction.if_gt

def sorted_induction.if_eq
  { α: Sort _ }
  [LE α] [tle: TrustedLE α]
  (ctx: SortedIndCtx α):
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
      cases h:tle.decide_ord x y with
      | Lt _ _ => 
        contradiction
      | Gt x_le_y _ =>
        contradiction
      | Eq _ => 
        rfl
    }
    rename_i h
    apply False.elim
    exact sorted_induction.fueled.termination ctx _ _ _ (nat.lt_succ_self _) h

#print axioms sorted_induction.if_eq

def sorted_induction'
  { α: Sort _ }
  [LE α] [TrustedLE α]
  (motive: List α -> List α -> Sort _)
  {left_empty: ∀list, motive [] list}
  {right_empty: ∀x xs, motive (x::xs) []}
  {if_lt: ∀x y xs ys, x ≤ y -> x ≠ y -> motive xs (y::ys) -> motive (x::xs) (y::ys)}
  {if_gt: ∀x y xs ys, x ≥ y -> x ≠ y -> motive (x::xs) ys -> motive (x::xs) (y::ys)}
  {if_eq: ∀x y xs ys, x = y -> motive xs ys -> motive (x::xs) (y::ys)}
  :
  ∀(xs ys: List α), motive xs ys :=
  fun xs ys =>sorted_induction (SortedIndCtx.mk motive left_empty right_empty if_lt if_gt if_eq) xs ys
