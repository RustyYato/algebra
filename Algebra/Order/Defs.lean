-- inductive HasOrdering : α -> α -> Order -> Prop where
-- | intro

class Order (α: Type _) where
  cmp: α -> α -> Ordering -> Prop

def cmp [o: Order α] : α -> α -> Ordering -> Prop := o.cmp

def Order.lt [Order α] (a b: α) := cmp a b .lt

instance [Order α] : LT α where
  lt := Order.lt

def Order.le [Order α] (a b: α) := cmp a b .lt ∨ cmp a b .eq

instance [Order α] : LE α where
  le := Order.le

class IsLinearOrder (α: Type _) [Order α]: Prop where
  cmp_unique: ∀(a b: α) o₀ o₁, cmp a b o₀ -> cmp a b o₁ -> o₀ = o₁
  cmp_refl: ∀a: α, cmp a a Ordering.eq
  cmp_swap: ∀(a b: α) o, cmp a b o -> cmp b a o.swap
  cmp_trans: ∀(a b c: α) o, cmp a b o -> cmp b c o -> cmp a c o
  cmp_eq: ∀a b: α, cmp a b .eq -> a = b
  cmp_total: ∀a b: α, ∃o, cmp a b o

abbrev DecidableOrder α [Order α] := ∀(a b: α) o, Decidable (cmp (α := α) a b o)

instance (priority := 500) [Order α] [DecidableOrder α] (a b: α) : Decidable (a < b) :=
  if h:cmp a b .lt then
    .isTrue h
  else
    .isFalse <| fun h₀ => h h₀

instance (priority := 500) [Order α] [DecidableOrder α] (a b: α) : Decidable (a ≤ b) :=
  if h:cmp a b .lt then
    .isTrue (.inl h)
  else if g:cmp a b .eq then
    .isTrue (.inr g)
  else
    .isFalse <| fun
      | .inl h₀ => h h₀
      | .inr h₀ => g h₀

instance [Ord α] : Order α where
  cmp a b o := compare a b = o

instance [Ord α] (a b: α) (o: Ordering) : Decidable (cmp a b o) := by
  unfold cmp Order.cmp instOrderOfOrd
  dsimp
  exact inferInstance

instance {P: Ordering -> Prop} [DecidablePred P] : Decidable (∃o: Ordering, P o) :=
  match inferInstanceAs (Decidable (P .lt ∨ P .eq ∨ P .gt)) with
  | .isTrue h  => .isTrue <| match h with
    | .inl h => ⟨_,h⟩
    | .inr (.inl h) => ⟨_,h⟩
    | .inr (.inr h) => ⟨_,h⟩
  | .isFalse h => .isFalse <| fun
    | ⟨.lt, h₀⟩ => h (.inl h₀)
    | ⟨.eq, h₀⟩ => h (.inr (.inl h₀))
    | ⟨.gt, h₀⟩ => h (.inr (.inr h₀))

instance {P: Ordering -> Prop} [DecidablePred P] : Decidable (∀o: Ordering, P o) :=
  match inferInstanceAs (Decidable (P .lt ∧ P .eq ∧ P .gt)) with
  | .isTrue ⟨h₀,h₁,h₂⟩  => .isTrue <| fun
    | .lt => h₀
    | .eq => h₁
    | .gt => h₂
  | .isFalse h => .isFalse <| fun h₀ => h ⟨ h₀ _, h₀ _, h₀ _ ⟩

instance : IsLinearOrder Bool where
  cmp_unique := by decide
  cmp_refl := by decide
  cmp_swap := by decide
  cmp_trans := by decide
  cmp_eq := by decide
  cmp_total := by decide

variable [Order α] [IsLinearOrder α] {a b c k: α}

def cmp_unique: ∀{o₀ o₁}, cmp a b o₀ -> cmp a b o₁ -> o₀ = o₁ := IsLinearOrder.cmp_unique _ _ _ _
def cmp_refl: ∀a: α, cmp a a Ordering.eq := IsLinearOrder.cmp_refl
def cmp_swap: ∀o, cmp a b o -> cmp b a o.swap := IsLinearOrder.cmp_swap _ _
def cmp_trans: ∀o, cmp a b o -> cmp b c o -> cmp a c o := IsLinearOrder.cmp_trans _ _ _
def cmp_eq: cmp a b .eq -> a = b := IsLinearOrder.cmp_eq _ _
def cmp_total: ∀a b: α, ∃o, cmp a b o := IsLinearOrder.cmp_total

def lt_or_eq_of_le : a ≤ b -> a < b ∨ a = b := by
  intro le
  cases le <;> rename_i h
  exact .inl h
  apply Or.inr (cmp_eq h)

def cmp_or_eq_trans :
  cmp a b o ∨ cmp a b .eq ->
  cmp b c o ∨ cmp b c .eq ->
  cmp a c o ∨ cmp a c .eq := by
  intro ab bc
  cases ab <;> cases bc <;> rename_i ab bc
  apply Or.inl
  apply cmp_trans <;> assumption
  cases cmp_eq bc
  exact Or.inl ab
  cases cmp_eq ab
  exact Or.inl bc
  cases cmp_eq ab
  cases cmp_eq bc
  apply Or.inr
  apply cmp_refl

def cmp_of_cmp_of_cmp_or_eq :
  cmp a b o ->
  cmp b c o ∨ cmp b c .eq ->
  cmp a c o := by
  intro ab bc
  cases bc <;> rename_i bc
  apply cmp_trans <;> assumption
  cases cmp_eq bc
  assumption

def cmp_of_cmp_or_eq_of_cmp :
  cmp a b o ∨ cmp a b .eq ->
  cmp b c o ->
  cmp a c o := by
  intro ab bc
  cases ab <;> rename_i ab
  apply cmp_trans <;> assumption
  cases cmp_eq ab
  assumption

def lt_irrefl : ¬(a < a) := fun h => nomatch cmp_unique h (cmp_refl _)

@[refl]
def le_refl : a ≤ a := .inr (cmp_refl _)

def le_trans : a ≤ b -> b ≤ c -> a ≤ c := cmp_or_eq_trans
def ge_trans : c ≥ b -> b ≥ a -> c ≥ a := flip cmp_or_eq_trans

def lt_of_cmp : cmp a b .lt -> a < b := id
def eq_of_cmp : cmp a b .eq -> a = b := cmp_eq
def gt_of_cmp : cmp a b .gt -> a > b := cmp_swap _
def le_of_lt : a < b -> a ≤ b := .inl
def le_of_eq : a = b -> a ≤ b := fun h => h ▸ le_refl

def cmp_of_lt : a < b -> cmp a b .lt := id
def cmp_of_gt : a > b -> cmp a b .gt := cmp_swap _
def cmp_of_eq : a = b -> cmp a b .eq := fun h => h ▸ cmp_refl _

def lt_trans : a < b -> b < c -> a < c := cmp_trans _
def lt_of_lt_of_le : a < b -> b ≤ c -> a < c := cmp_of_cmp_of_cmp_or_eq
def lt_of_le_of_lt : a ≤ b -> b < c -> a < c := cmp_of_cmp_or_eq_of_cmp

def le_antisymm : a ≤ b -> b ≤ a -> a = b := by
  intro ab ba
  cases lt_or_eq_of_le ab <;> rename_i ab
  have := lt_irrefl (lt_of_lt_of_le ab ba)
  contradiction
  assumption

def ne_of_lt : a < b -> a ≠ b := by
  intro ab h
  subst h
  exact lt_irrefl ab

def not_lt_of_le : a ≤ b -> ¬b < a := (lt_irrefl <| lt_of_le_of_lt · ·)
def not_le_of_lt : a < b -> ¬b ≤ a := flip not_lt_of_le
def lt_of_not_le : ¬(a ≤ b) -> b < a := by
  intro h
  have ⟨o,prf⟩ := cmp_total a b
  cases o
  have := h (le_of_lt prf)
  contradiction
  have := h (le_of_eq (eq_of_cmp prf))
  contradiction
  apply gt_of_cmp
  assumption
def le_of_not_lt : ¬(a < b) -> b ≤ a := by
  intro h
  have ⟨o,prf⟩ := cmp_total a b
  cases o
  have := h prf
  contradiction
  apply le_of_eq
  symm
  apply eq_of_cmp
  assumption
  apply le_of_lt
  apply gt_of_cmp
  assumption

def lt_antisymm : a < b -> b < a -> False := (lt_irrefl <| lt_trans · ·)

attribute [irreducible] Order.lt Order.le

variable [DecidableOrder α]

instance : Max α where
  max a b := if a ≤ b then b else a
instance : Min α where
  min a b := if a ≤ b then a else b

def max.def (a b: α) : max a b = if a ≤ b then b else a := rfl
def min.def (a b: α) : min a b = if a ≤ b then a else b := rfl

def max.ge_left (a b: α) : a ≤ max a b := by
  rw [max.def]
  split
  assumption
  rfl

def max.ge_right (a b: α) : b ≤ max a b := by
  rw [max.def]
  split
  rfl
  apply le_of_lt
  apply lt_of_not_le
  assumption

def min.le_left (a b: α) : min a b ≤ a := by
  rw [min.def]
  split
  rfl
  apply le_of_lt
  apply lt_of_not_le
  assumption

def min.le_right (a b: α) : min a b ≤ b := by
  rw [min.def]
  split
  assumption
  rfl

def max.ge (a b k: α) : k ≤ a ∨ k ≤ b -> k ≤ max a b := by
  intro kab
  rw [max.def]
  split
  cases kab
  apply le_trans <;> assumption
  assumption
  cases kab
  assumption
  apply le_trans
  assumption
  apply le_of_lt
  apply lt_of_not_le
  assumption

def max.le (a b k: α) : a ≤ k -> b ≤ k -> max a b ≤ k := by
  intro ka kb
  rw [max.def]
  split <;> assumption

def max.gt (a b k: α) : k < a ∨ k < b -> k < max a b := by
  intro kab
  rw [max.def]
  split
  cases kab
  apply lt_of_lt_of_le <;> assumption
  assumption
  cases kab
  assumption
  apply lt_of_lt_of_le
  assumption
  apply le_of_lt
  apply lt_of_not_le
  assumption

def max.lt (a b k: α) : a < k -> b < k -> max a b < k := by
  intro ka kb
  rw [max.def]
  split <;> assumption

def min.ge (a b k: α) : k ≤ a -> k ≤ b -> k ≤ min a b := by
  intro ka kb
  rw [min.def]
  split <;> assumption

def min.le (a b k: α) : a ≤ k ∨ b ≤ k -> min a b ≤ k := by
  intro kab
  rw [min.def]
  split
  cases kab
  assumption
  apply le_trans <;> assumption
  cases kab
  apply le_trans
  apply le_of_lt
  apply lt_of_not_le
  repeat assumption

def min.gt (a b k: α) : k < a -> k < b -> k < min a b := by
  intro ka kb
  rw [min.def]
  split <;> assumption

def min.lt (a b k: α) : a < k ∨ b < k -> min a b < k := by
  intro kab
  rw [min.def]
  split
  cases kab
  assumption
  apply lt_of_le_of_lt <;> assumption
  cases kab
  apply lt_of_le_of_lt
  apply le_of_lt
  apply lt_of_not_le
  repeat assumption

def max.eq_left_or_right (a b: α) : max a b = a ∨ max a b = b := by
  rw [max.def]
  split
  exact Or.inr rfl
  exact Or.inl rfl

def min.eq_left_or_right (a b: α) : min a b = a ∨ min a b = b := by
  rw [min.def]
  split
  exact Or.inl rfl
  exact Or.inr rfl

def min.le_max (a b: α) : min a b ≤ max a b := by
  cases min.eq_left_or_right a b <;> (rename_i h; rw [h])
  apply max.ge_left
  apply max.ge_right

def max.comm (a b: α) : max a b = max b a := by
  apply le_antisymm
  apply max.le
  apply max.ge_right
  apply max.ge_left
  apply max.le
  apply max.ge_right
  apply max.ge_left

def min.comm (a b: α) : min a b = min b a := by
  apply le_antisymm
  apply min.ge
  apply min.le_right
  apply min.le_left
  apply min.ge
  apply min.le_right
  apply min.le_left

def max.assoc (a b c: α) : max (max a b) c = max a (max b c) := by
  apply le_antisymm
  apply max.le
  apply max.le
  apply max.ge_left
  apply max.ge
  apply Or.inr
  apply max.ge_left
  apply max.ge
  apply Or.inr
  apply max.ge_right
  apply max.le
  apply max.ge
  apply Or.inl
  apply max.ge_left
  apply max.le
  apply max.ge
  apply Or.inl
  apply max.ge_right
  apply max.ge_right

def max.of_ge_right (a b: α) : a ≤ b -> max a b = b := by
  intro h
  rw [max.def, if_pos h]

def max.of_ge_left (a b: α) : b ≤ a -> max a b = a := by
  intro h
  rw [max.comm]
  exact max.of_ge_right _ _ h

def min.of_le_left (a b: α) : a ≤ b -> min a b = a := by
  intro h
  rw [min.def, if_pos h]

def min.of_le_right (a b: α) : b ≤ a -> min a b = b := by
  intro h
  rw [min.comm]
  exact min.of_le_left _ _ h
