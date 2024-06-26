class TotalOrder (α: Sort _) [Ord α] where
  compare_transitive:
    ∀{a b c: α} {o: Ordering}, compare a b = o -> compare b c = o -> compare a c = o
  eq_of_compare_eq:
    ∀{a b: α}, compare a b = Ordering.eq -> a = b
  compare_eq_refl:
    ∀(a: α), compare a a = Ordering.eq
  compare_antisymm:
    ∀{a b: α}, compare a b = (compare b a).swap

instance TotalOrder.instLT [Ord α] [TotalOrder α] : LT α where
  lt a b := compare a b = Ordering.lt

instance TotalOrder.instLE [Ord α] [TotalOrder α] : LE α where
  le a b := compare a b = Ordering.lt ∨ compare a b = Ordering.eq

instance TotalOrder.instBEq [Ord α] [TotalOrder α]: BEq α where
  beq a b := compare a b = Ordering.eq

def TotalOrder.unfold_lt [Ord α] [TotalOrder α] : ∀(a b: α), (a < b) = (compare a b = Ordering.lt) := fun _ _ => rfl
def TotalOrder.unfold_le [Ord α] [TotalOrder α] : ∀(a b: α), (a ≤ b) = (compare a b = Ordering.lt ∨ compare a b = Ordering.eq) := fun _ _ => rfl
def TotalOrder.unfold_ge [Ord α] [TotalOrder α] : ∀(a b: α), (a ≥ b) = (b ≤ a) := fun _ _ => rfl

inductive DecidableOrder {α: Sort _} [Ord α] [TotalOrder α] (a b: α) where
  | Lt : a < b -> DecidableOrder a b
  | Eq : a = b -> DecidableOrder a b
  | Gt : a > b -> DecidableOrder a b

instance TotalOrder.instLTDec [Ord α] [TotalOrder α] (a b: α) : Decidable (a < b) :=
  match h:compare a b with
  | .lt => Decidable.isTrue h
  | .eq | .gt => Decidable.isFalse (by
    intro a_lt_b
    rw [a_lt_b] at h
    contradiction)

instance TotalOrder.instLEDec [Ord α] [TotalOrder α] (a b: α) : Decidable (a ≤ b) :=
  match h:compare a b with
  | .lt => Decidable.isTrue (Or.inl h)
  | .eq => Decidable.isTrue (Or.inr h)
  | .gt => Decidable.isFalse (by
    intro a_le_b
    cases a_le_b <;> (rename_i a_cmp_b; rw [a_cmp_b] at h; contradiction))

instance TotalOrder.instDecEq [Ord α] [TotalOrder α] : DecidableEq α := fun a b =>
  match h:compare  a b with
  | .lt | .gt => Decidable.isFalse <| by
    intro a_eq_b
    rw [a_eq_b, compare_eq_refl] at h
    contradiction
  | .eq => Decidable.isTrue <| eq_of_compare_eq h

def TotalOrder.compare_or_eq_transitive
  [Ord α] [TotalOrder α]:
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

#print axioms TotalOrder.compare_or_eq_transitive

def TotalOrder.swap_compare
  [Ord α] [TotalOrder α]:
  ∀{ a b: α } { o: Ordering }, compare a b = o -> compare b a = o.swap := by
  intro a b o a_cmp_b
  rw [←a_cmp_b]
  apply compare_antisymm

#print axioms TotalOrder.swap_compare

def TotalOrder.lt_irrefl
  [Ord α] [TotalOrder α]:
  ∀{a: α}, ¬(a < a) := by
  intro a a_lt_a
  have := swap_compare a_lt_a
  rw [a_lt_a] at this
  contradiction

#print axioms TotalOrder.lt_irrefl

def TotalOrder.le_refl
  [Ord α] [TotalOrder α]
  { a: α } : a ≤ a := Or.inr <| compare_eq_refl a

def TotalOrder.lt_trans
  [Ord α] [TotalOrder α]:
  ∀{a b c: α}, a < b -> b < c -> a < c := by
  intros; apply compare_transitive <;> assumption

#print axioms TotalOrder.lt_trans

def TotalOrder.le_trans
  [Ord α] [TotalOrder α]:
  ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c := by
  intros; apply compare_or_eq_transitive <;> assumption

#print axioms TotalOrder.le_trans

--- start conversions to/from compare ---

def TotalOrder.gt_of_compare
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, compare a b = Ordering.gt -> a > b := swap_compare

#print axioms TotalOrder.gt_of_compare

def TotalOrder.compare_of_gt
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, a > b -> compare a b = Ordering.gt := swap_compare

#print axioms TotalOrder.compare_of_gt

def TotalOrder.lt_of_compare
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, compare a b = Ordering.lt -> a < b := id

#print axioms TotalOrder.lt_of_compare

def TotalOrder.compare_of_lt
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, a < b -> compare a b = Ordering.lt := id

#print axioms TotalOrder.compare_of_lt

def TotalOrder.eq_of_compare
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, compare a b = Ordering.eq -> a = b := eq_of_compare_eq

#print axioms TotalOrder.eq_of_compare

def TotalOrder.compare_of_eq
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, a = b -> compare a b = Ordering.eq := fun x => match x with | .refl _ => compare_eq_refl _

#print axioms TotalOrder.compare_of_eq

def TotalOrder.le_of_compare
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, compare a b = Ordering.lt ∨ compare a b = Ordering.eq -> a ≤ b := id

#print axioms TotalOrder.le_of_compare

def TotalOrder.compare_of_le
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, a ≤ b -> compare a b = Ordering.lt ∨ compare a b = Ordering.eq := id

#print axioms TotalOrder.compare_of_le

def TotalOrder.ge_of_compare
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, compare a b = Ordering.gt ∨ compare a b = Ordering.eq -> a ≥ b := by
    intro a b ge
    cases ge
    rename_i h
    apply Or.inl; apply swap_compare h
    rename_i h
    cases eq_of_compare_eq h; apply le_refl

#print axioms TotalOrder.ge_of_compare

def TotalOrder.compare_of_ge
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, a ≥ b -> compare a b = Ordering.gt ∨ compare a b = Ordering.eq := by
    intro a b a_ge_b
    cases a_ge_b
    apply Or.inl; rename_i h; apply swap_compare h
    apply Or.inr;  rename_i h; apply swap_compare h

#print axioms TotalOrder.compare_of_ge

def TotalOrder.ne_of_compare
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, compare a b = Ordering.gt ∨ compare a b = Ordering.lt -> a ≠ b := by
    intro a b ne
    intro a_eq_b
    cases a_eq_b
    cases ne <;> (rw [TotalOrder.compare_eq_refl] at *; contradiction)

#print axioms TotalOrder.ne_of_compare

def TotalOrder.compare_of_ne
  [Ord α] [TotalOrder α]:
  ∀{a b: α}, a ≠ b -> compare a b = Ordering.gt ∨ compare a b = Ordering.lt := by
    intro a b a_ne_b
    cases h:compare a b
    any_goals (apply Or.inl; rfl)
    any_goals (apply Or.inr; rfl)
    have := eq_of_compare_eq h
    contradiction

#print axioms TotalOrder.compare_of_ne

--- end conversions to/from compare ---

def TotalOrder.not_lt_implies_ge
  [Ord α] [TotalOrder α] :
  ∀{ a b: α }, ¬(a < b) -> a ≥ b := by
  intro a b not_a_lt_b
  match h:compare a b with
  | .lt => contradiction
  | .eq => exact Or.inr (swap_compare h)
  | .gt => exact Or.inl (swap_compare h)

#print axioms TotalOrder.not_lt_implies_ge

def TotalOrder.not_ge_implies_lt
  [Ord α] [TotalOrder α] :
  ∀{ a b: α }, ¬(a ≥ b) -> a < b := by
  intro a b not_a_ge_b
  match h:compare a b with
  | .lt => exact h
  | .eq => exact False.elim <| not_a_ge_b <| Or.inr (swap_compare h)
  | .gt => exact False.elim <| not_a_ge_b <| Or.inl (swap_compare h)

#print axioms TotalOrder.not_ge_implies_lt

def TotalOrder.lt_or_ge
  [Ord α] [TotalOrder α]:
  ∀(a b: α), a < b ∨ a ≥ b :=
  fun a b =>
  match h:compare a b with
  | .lt =>  Or.inl h
  | .eq =>  Or.inr <| Or.inr <| swap_compare h
  | .gt =>  Or.inr <| Or.inl <| swap_compare h

#print axioms TotalOrder.lt_or_ge

def TotalOrder.not_lt_and_ge
  [Ord α] [TotalOrder α]:
  ∀{ a b: α }, a < b -> a ≥ b -> False := by
  intro a b a_lt_b a_ge_b
  rw [unfold_ge, unfold_le] at a_ge_b
  rw [swap_compare a_lt_b] at a_ge_b
  cases a_ge_b <;> contradiction

#print axioms TotalOrder.not_lt_and_ge

def TotalOrder.lt_of_lt_and_le
  [Ord α] [TotalOrder α]:
  ∀{ a b c: α }, a < b -> b ≤ c -> a < c := by
  intro a b c a_lt_b b_le_c
  cases b_le_c with
  | inl h => apply lt_trans <;> assumption
  | inr h => rw [←eq_of_compare_eq h]; assumption

#print axioms TotalOrder.lt_of_lt_and_le

def TotalOrder.lt_of_le_and_lt
  [Ord α] [TotalOrder α]:
  ∀{ a b c: α }, a ≤ b -> b < c -> a < c := by
  intro a b c a_le_b b_lt_c
  cases a_le_b with
  | inl h => apply lt_trans <;> assumption
  | inr h => rw [eq_of_compare_eq h]; assumption

#print axioms TotalOrder.lt_of_lt_and_le

def TotalOrder.le_antisymm
  [Ord α] [TotalOrder α]:
  ∀{ a b: α }, a ≤ b -> b ≤ a -> a = b := by
  intro a b a_le_b b_le_a
  cases a_le_b with
  | inr a_eq_b => exact eq_of_compare_eq a_eq_b
  | inl a_lt_b => cases b_le_a with
    | inr b_eq_a => exact (eq_of_compare_eq b_eq_a).symm
    | inl b_lt_a =>
      have := lt_irrefl <| compare_transitive a_lt_b b_lt_a
      contradiction

#print axioms TotalOrder.le_antisymm

def TotalOrder.lt_antisymm
  [Ord α] [TotalOrder α]:
  ∀{ a b: α }, a < b -> b < a -> False := by
  intro a b a_lt_b b_lt_a
  exact lt_irrefl <| lt_trans a_lt_b b_lt_a

#print axioms TotalOrder.lt_antisymm

instance TotalOrder.instLawfulBEq [Ord α] [TotalOrder α]: LawfulBEq α where
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

#print axioms TotalOrder.instLawfulBEq

def TotalOrder.beq_symm
  [Ord α] [TotalOrder α]:
  ∀{ a b: α }, a == b -> b == a := by
    intro a b a_eq_b
    have := eq_of_beq a_eq_b
    rw [this]
    exact instLawfulBEq.rfl

#print axioms TotalOrder.beq_symm

def TotalOrder.le_of_beq [Ord α] [TotalOrder α] { a b: α } : a == b -> a ≤ b :=
  fun a_eq_b => Or.inr <| of_decide_eq_true a_eq_b

#print axioms TotalOrder.le_of_beq

def TotalOrder.le_of_lt [Ord α] [TotalOrder α] { a b: α } : a < b -> a ≤ b := Or.inl

#print axioms TotalOrder.le_of_lt

def TotalOrder.le_of_not_gt [Ord α] [TotalOrder α] { a b: α } : ¬a > b -> a ≤ b := by
  intro not_a_gt_b
  cases h:compare a b
  exact Or.inl h
  exact Or.inr h
  have := not_a_gt_b <| TotalOrder.gt_of_compare h
  contradiction

#print axioms TotalOrder.le_of_not_gt

def TotalOrder.lt_of_not_ge [Ord α] [TotalOrder α] { a b: α } : ¬a ≥ b -> a < b := by
  intro not_a_ge_b
  cases h:compare a b
  exact h
  have := not_a_ge_b <| Or.inr <| TotalOrder.swap_compare h
  contradiction
  have := not_a_ge_b <| Or.inl <| TotalOrder.swap_compare h
  contradiction

#print axioms TotalOrder.lt_of_not_ge

def TotalOrder.le_of_eq [Ord α] [TotalOrder α] { a b: α } : a = b -> a ≤ b := by
  intro a_eq_b
  apply Or.inr
  rw [a_eq_b]
  apply compare_eq_refl

#print axioms TotalOrder.le_of_eq

def TotalOrder.ne_of_lt [Ord α] [TotalOrder α] { a b: α } : a < b -> a ≠ b := by
  intro a_lt_b a_eq_b
  rw [a_eq_b] at a_lt_b
  exact lt_irrefl a_lt_b

def TotalOrder.ne_of_gt [Ord α] [TotalOrder α] { a b: α } : a > b -> a ≠ b := by
  intro a_gt_b a_eq_b
  rw [a_eq_b] at a_gt_b
  exact lt_irrefl a_gt_b

def TotalOrder.lt_of_le_and_ne [Ord α] [TotalOrder α] { a b: α } : a ≤ b -> a ≠ b -> a < b := by
  intro a_le_b a_ne_b
  cases a_le_b with
  | inl h => exact h
  | inr a_eq_b =>
    have := eq_of_compare_eq a_eq_b
    contradiction

def TotalOrder.gt_of_ge_and_ne [Ord α] [TotalOrder α] { a b: α } : a ≥ b -> a ≠ b -> a > b := by
  intro a_le_b a_ne_b
  cases a_le_b with
  | inl h => exact h
  | inr a_eq_b =>
    have := (eq_of_compare_eq a_eq_b).symm
    contradiction

def TotalOrder.lt_or_eq_of_le [Ord α] [TotalOrder α] { a b: α } : a ≤ b -> a < b ∨ a = b := by
  intro a_le_b
  cases a_le_b with
  | inl a_lt_b => exact Or.inl a_lt_b
  | inr a_eq_b => exact Or.inr <| eq_of_compare_eq a_eq_b

#print axioms TotalOrder.lt_or_eq_of_le

def TotalOrder.decide [Ord α] [TotalOrder α] (a b: α) : DecidableOrder a b := match h:compare a b with
  | .lt => .Lt h
  | .eq => .Eq <| eq_of_compare_eq h
  | .gt => .Gt <| gt_of_compare h
