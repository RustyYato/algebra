class TotalOrder (α: Sort _) [Ord α] where
  compare_transitive:
    ∀{a b c: α} {o: Ordering}, compare a b = o -> compare b c = o -> compare a c = o
  eq_of_compare_eq:
    ∀{a b: α}, compare a b = Ordering.eq -> a = b
  compare_eq_refl:
    ∀(a: α), compare a a = Ordering.eq
  compare_antisymm:
    ∀{a b: α}, compare a b = (compare b a).swap

variable { α: Sort _ } [Ord α] [TotalOrder α]

def compare_transitive: ∀{a b c: α} {o: Ordering}, compare a b = o -> compare b c = o -> compare a c = o := TotalOrder.compare_transitive
def eq_of_compare_eq: ∀{a b: α}, compare a b = Ordering.eq -> a = b := TotalOrder.eq_of_compare_eq
def compare_eq_refl: ∀(a: α), compare a a = Ordering.eq := TotalOrder.compare_eq_refl
def compare_antisymm: ∀{a b: α}, compare a b = (compare b a).swap := TotalOrder.compare_antisymm

instance TotalOrder.instLT : LT α where
  lt a b := compare a b = Ordering.lt

instance TotalOrder.instLE : LE α where
  le a b := compare a b = Ordering.lt ∨ compare a b = Ordering.eq

instance TotalOrder.instBEq: BEq α where
  beq a b := compare a b = Ordering.eq

def TotalOrder.unfold_lt : ∀(a b: α), (a < b) = (compare a b = Ordering.lt) := fun _ _ => rfl
def TotalOrder.unfold_le : ∀(a b: α), (a ≤ b) = (compare a b = Ordering.lt ∨ compare a b = Ordering.eq) := fun _ _ => rfl
def TotalOrder.unfold_ge : ∀(a b: α), (a ≥ b) = (b ≤ a) := fun _ _ => rfl

inductive DecidableOrder (a b: α) where
  | Lt : a < b -> DecidableOrder a b
  | Eq : a = b -> DecidableOrder a b
  | Gt : a > b -> DecidableOrder a b

instance TotalOrder.instLTDec (a b: α) : Decidable (a < b) :=
  match h:compare a b with
  | .lt => Decidable.isTrue h
  | .eq | .gt => Decidable.isFalse (by
    intro a_lt_b
    rw [a_lt_b] at h
    contradiction)

instance TotalOrder.instLEDec (a b: α) : Decidable (a ≤ b) :=
  match h:compare a b with
  | .lt => Decidable.isTrue (Or.inl h)
  | .eq => Decidable.isTrue (Or.inr h)
  | .gt => Decidable.isFalse (by
    intro a_le_b
    cases a_le_b <;> (rename_i a_cmp_b; rw [a_cmp_b] at h; contradiction))

instance TotalOrder.instDecEq : DecidableEq α := fun a b =>
  match h:compare  a b with
  | .lt | .gt => Decidable.isFalse <| by
    intro a_eq_b
    rw [a_eq_b, compare_eq_refl] at h
    contradiction
  | .eq => Decidable.isTrue <| eq_of_compare_eq h

def compare_or_eq_transitive
 :
  ∀(a b c: α) (o: Ordering),
    (compare a b = o ∨ compare a b = Ordering.eq) ->
    (compare b c = o ∨ compare b c = Ordering.eq) ->
    (compare a c = o ∨ compare a c = Ordering.eq) := by
    intro a b c o
    intro a_cmp_b b_cmp_c
    cases a_cmp_b with
    | inr a_eq_b =>
      cases eq_of_compare_eq a_eq_b with
      | refl =>
      assumption
    | inl a_cmp_b =>
      cases b_cmp_c with
      | inr b_eq_c =>
        cases eq_of_compare_eq b_eq_c with
        | refl =>
        apply Or.inl
        assumption
      | inl b_cmp_c =>
        apply Or.inl
        apply compare_transitive <;> assumption

#print axioms compare_or_eq_transitive

def compare_of_cmp_or_eq_of_cmp
 :
  ∀(a b c: α) (o: Ordering),
    (compare a b = o ∨ compare a b = Ordering.eq) ->
    compare b c = o ->
    compare a c = o := by
    intro a b c o
    intro a_cmp_b b_cmp_c
    cases a_cmp_b
    apply compare_transitive <;> assumption
    rename_i h
    cases TotalOrder.eq_of_compare_eq h
    assumption

#print axioms compare_of_cmp_or_eq_of_cmp

def compare_of_cmp_of_cmp_or_eq
 :
  ∀(a b c: α) (o: Ordering),
    compare a b = o ->
    (compare b c = o ∨ compare b c = Ordering.eq) ->
    compare a c = o := by
    intro a b c o
    intro a_cmp_b b_cmp_c
    cases b_cmp_c
    apply compare_transitive <;> assumption
    rename_i h
    cases TotalOrder.eq_of_compare_eq h
    assumption

#print axioms compare_of_cmp_of_cmp_or_eq

def swap_compare
 :
  ∀{ a b: α } { o: Ordering }, compare a b = o -> compare b a = o.swap := by
  intro a b o a_cmp_b
  rw [←a_cmp_b]
  apply compare_antisymm

#print axioms swap_compare

def swap_compare'
 :
  ∀{ a b: α }, compare a b = (compare b a).swap := by
  intro a b
  rw [swap_compare rfl]

#print axioms swap_compare

def lt_irrefl
 :
  ∀{a: α}, ¬(a < a) := by
  intro a a_lt_a
  have := swap_compare a_lt_a
  rw [a_lt_a] at this
  contradiction

#print axioms lt_irrefl

@[refl]
def le_refl

  { a: α } : a ≤ a := Or.inr <| compare_eq_refl a

def lt_trans
 :
  ∀{a b c: α}, a < b -> b < c -> a < c := by
  intros; apply compare_transitive <;> assumption

#print axioms lt_trans

def le_trans
 :
  ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c := by
  intros; apply compare_or_eq_transitive <;> assumption

#print axioms le_trans

--- start conversions to/from compare ---

def gt_of_compare
 :
  ∀{a b: α}, compare a b = Ordering.gt -> a > b := swap_compare

#print axioms gt_of_compare

def compare_of_gt
 :
  ∀{a b: α}, a > b -> compare a b = Ordering.gt := swap_compare

#print axioms compare_of_gt

def lt_of_compare
 :
  ∀{a b: α}, compare a b = Ordering.lt -> a < b := id

#print axioms lt_of_compare

def compare_of_lt
 :
  ∀{a b: α}, a < b -> compare a b = Ordering.lt := id

#print axioms compare_of_lt

def eq_of_compare
 :
  ∀{a b: α}, compare a b = Ordering.eq -> a = b := eq_of_compare_eq

#print axioms eq_of_compare

def compare_of_eq
 :
  ∀{a b: α}, a = b -> compare a b = Ordering.eq := fun x => match x with | .refl _ => compare_eq_refl _

#print axioms compare_of_eq

def le_of_compare
 :
  ∀{a b: α}, compare a b = Ordering.lt ∨ compare a b = Ordering.eq -> a ≤ b := id

#print axioms le_of_compare

def compare_of_le
 :
  ∀{a b: α}, a ≤ b -> compare a b = Ordering.lt ∨ compare a b = Ordering.eq := id

#print axioms compare_of_le

def ge_of_compare
 :
  ∀{a b: α}, compare a b = Ordering.gt ∨ compare a b = Ordering.eq -> a ≥ b := by
    intro a b ge
    cases ge
    rename_i h
    apply Or.inl; apply swap_compare h
    rename_i h
    cases eq_of_compare_eq h; apply le_refl

#print axioms ge_of_compare

def compare_of_ge
 :
  ∀{a b: α}, a ≥ b -> compare a b = Ordering.gt ∨ compare a b = Ordering.eq := by
    intro a b a_ge_b
    cases a_ge_b
    apply Or.inl; rename_i h; apply swap_compare h
    apply Or.inr;  rename_i h; apply swap_compare h

#print axioms compare_of_ge

def ne_of_compare
 :
  ∀{a b: α}, compare a b = Ordering.gt ∨ compare a b = Ordering.lt -> a ≠ b := by
    intro a b ne
    intro a_eq_b
    cases a_eq_b
    cases ne <;> (rw [TotalOrder.compare_eq_refl] at *; contradiction)

#print axioms ne_of_compare

def compare_of_ne
 :
  ∀{a b: α}, a ≠ b -> compare a b = Ordering.gt ∨ compare a b = Ordering.lt := by
    intro a b a_ne_b
    cases h:compare a b
    any_goals (apply Or.inl; rfl)
    any_goals (apply Or.inr; rfl)
    have := eq_of_compare_eq h
    contradiction

#print axioms compare_of_ne

--- end conversions to/from compare ---

def not_lt_implies_ge
  :
  ∀{ a b: α }, ¬(a < b) -> a ≥ b := by
  intro a b not_a_lt_b
  match h:compare a b with
  | .lt => contradiction
  | .eq => exact Or.inr (swap_compare h)
  | .gt => exact Or.inl (swap_compare h)

#print axioms not_lt_implies_ge

def not_ge_implies_lt
  :
  ∀{ a b: α }, ¬(a ≥ b) -> a < b := by
  intro a b not_a_ge_b
  match h:compare a b with
  | .lt => exact h
  | .eq => exact False.elim <| not_a_ge_b <| Or.inr (swap_compare h)
  | .gt => exact False.elim <| not_a_ge_b <| Or.inl (swap_compare h)

#print axioms not_ge_implies_lt

def lt_or_ge
 :
  ∀(a b: α), a < b ∨ a ≥ b :=
  fun a b =>
  match h:compare a b with
  | .lt =>  Or.inl h
  | .eq =>  Or.inr <| Or.inr <| swap_compare h
  | .gt =>  Or.inr <| Or.inl <| swap_compare h

#print axioms lt_or_ge

def not_lt_and_ge
 :
  ∀{ a b: α }, a < b -> a ≥ b -> False := by
  intro a b a_lt_b a_ge_b
  rw [TotalOrder.unfold_ge, TotalOrder.unfold_le] at a_ge_b
  rw [swap_compare a_lt_b] at a_ge_b
  cases a_ge_b <;> contradiction

#print axioms not_lt_and_ge

def lt_of_lt_of_le
 :
  ∀{ a b c: α }, a < b -> b ≤ c -> a < c := by
  intro a b c a_lt_b b_le_c
  cases b_le_c with
  | inl h => apply lt_trans <;> assumption
  | inr h => rw [←eq_of_compare_eq h]; assumption

#print axioms lt_of_lt_of_le

def lt_of_le_of_lt:
  ∀{ a b c: α }, a ≤ b -> b < c -> a < c := by
  intro a b c a_le_b b_lt_c
  cases a_le_b with
  | inl h => apply lt_trans <;> assumption
  | inr h => rw [eq_of_compare_eq h]; assumption

#print axioms lt_of_lt_of_le

def le_antisymm:
  ∀{ a b: α }, a ≤ b -> b ≤ a -> a = b := by
  intro a b a_le_b b_le_a
  cases a_le_b with
  | inr a_eq_b => exact eq_of_compare_eq a_eq_b
  | inl a_lt_b => cases b_le_a with
    | inr b_eq_a => exact (eq_of_compare_eq b_eq_a).symm
    | inl b_lt_a =>
      have := lt_irrefl <| compare_transitive a_lt_b b_lt_a
      contradiction

#print axioms le_antisymm

def lt_antisymm:
  ∀{ a b: α }, a < b -> b < a -> False := by
  intro a b a_lt_b b_lt_a
  exact lt_irrefl <| lt_trans a_lt_b b_lt_a

#print axioms lt_antisymm

instance TotalOrder.instLawfulBEq: LawfulBEq α where
  eq_of_beq := by
    intro a b a_beq_b
    apply eq_of_compare_eq
    exact of_decide_eq_true a_beq_b
  rfl := by
    intro a
    unfold BEq.beq instBEq
    simp only
    rw [compare_eq_refl]
    rfl

#print axioms instLawfulBEq

def beq_symm
 :
  ∀{ a b: α }, a == b -> b == a := by
    intro a b a_eq_b
    have := eq_of_beq a_eq_b
    rw [this]
    exact TotalOrder.instLawfulBEq.rfl

#print axioms beq_symm

def le_of_beq { a b: α } : a == b -> a ≤ b :=
  fun a_eq_b => Or.inr <| of_decide_eq_true a_eq_b

#print axioms le_of_beq

def le_of_eq { a b: α } : a = b -> a ≤ b := by
  intro h
  subst h
  apply le_refl

#print axioms le_of_eq

def le_of_lt { a b: α } : a < b -> a ≤ b := Or.inl

#print axioms le_of_lt

def ge_of_eq { a b: α } : a = b -> a ≥ b := le_of_eq ∘ Eq.symm

#print axioms ge_of_eq

def ge_of_gt { a b: α } : a > b -> a ≥ b := Or.inl

#print axioms ge_of_gt

def le_of_not_gt { a b: α } : ¬a > b -> a ≤ b := by
  intro not_a_gt_b
  cases h:compare a b
  exact Or.inl h
  exact Or.inr h
  have := not_a_gt_b <| gt_of_compare h
  contradiction

#print axioms le_of_not_gt

def le_of_not_lt { a b: α } : ¬b < a -> a ≤ b := by
  intro not_a_gt_b
  cases h:compare a b
  exact Or.inl h
  exact Or.inr h
  have := not_a_gt_b <| gt_of_compare h
  contradiction

#print axioms le_of_not_gt

def lt_of_not_ge { a b: α } : ¬a ≥ b -> a < b := by
  intro not_a_ge_b
  cases h:compare a b
  exact h
  have := not_a_ge_b <| Or.inr <| swap_compare h
  contradiction
  have := not_a_ge_b <| Or.inl <| swap_compare h
  contradiction

#print axioms lt_of_not_ge

def ne_of_lt { a b: α } : a < b -> a ≠ b := by
  intro a_lt_b a_eq_b
  rw [a_eq_b] at a_lt_b
  exact lt_irrefl a_lt_b

def ne_of_gt { a b: α } : a > b -> a ≠ b := by
  intro a_gt_b a_eq_b
  rw [a_eq_b] at a_gt_b
  exact lt_irrefl a_gt_b

def lt_of_le_of_ne { a b: α } : a ≤ b -> a ≠ b -> a < b := by
  intro a_le_b a_ne_b
  cases a_le_b with
  | inl h => exact h
  | inr a_eq_b =>
    have := eq_of_compare_eq a_eq_b
    contradiction

def gt_of_ge_of_ne { a b: α } : a ≥ b -> a ≠ b -> a > b := by
  intro a_le_b a_ne_b
  cases a_le_b with
  | inl h => exact h
  | inr a_eq_b =>
    have := (eq_of_compare_eq a_eq_b).symm
    contradiction

def lt_or_eq_of_le { a b: α } : a ≤ b -> a < b ∨ a = b := by
  intro a_le_b
  cases a_le_b with
  | inl a_lt_b => exact Or.inl a_lt_b
  | inr a_eq_b => exact Or.inr <| eq_of_compare_eq a_eq_b

#print axioms lt_or_eq_of_le

def not_lt_of_le { a b: α } : a ≤ b -> ¬b < a := by
  intro h g
  have := lt_of_le_of_lt h g
  exact lt_irrefl this

#print axioms not_lt_of_le

def not_lt_of_ge { a b: α } : b ≥ a -> ¬b < a := not_lt_of_le

#print axioms not_lt_of_ge

def not_le_of_lt { a b: α } : a < b -> ¬b ≤ a := by
  intro g h
  have := lt_of_le_of_lt h g
  exact lt_irrefl this

#print axioms not_le_of_lt

def decide (a b: α) : DecidableOrder a b := match h:compare a b with
  | .lt => .Lt h
  | .eq => .Eq <| eq_of_compare_eq h
  | .gt => .Gt <| gt_of_compare h

def compare_or_eq_of_le
  (a b: α):
  a ≤ b ->
  compare a b = Ordering.lt ∨ a = b := by
  intro h
  cases lt_or_eq_of_le h
  apply Or.inl; assumption
  apply Or.inr
  assumption

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
  apply lt_of_not_ge
  assumption

def min.le_left (a b: α) : min a b ≤ a := by
  rw [min.def]
  split
  rfl
  apply le_of_lt
  apply lt_of_not_ge
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
  apply lt_of_not_ge
  assumption

def max.le (a b k: α) : a ≤ k -> b ≤ k -> max a b ≤ k := by
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
  apply lt_of_not_ge
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
