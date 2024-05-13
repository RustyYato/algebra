import Algebra.SortedList.Basic

-- if as is a subset of bs
def List.sorted_subset (as bs: List α) : Prop := match as with
  | [] => True
  | a::as => match bs with
     | [] => False
     | b::bs => a = b ∧ as.sorted_subset bs ∨ a ≠ b ∧ (a::as).sorted_subset bs

#print axioms List.sorted_subset

instance List.sorted_subset.dec [DecidableEq α] (as bs: List α) : Decidable (as.sorted_subset bs) := 
  match as with
  | [] => by
    apply Decidable.isTrue
    unfold List.sorted_subset
    trivial
  | a::as => match bs with
    | [] => Decidable.isFalse False.elim
    | b::bs => by
      unfold sorted_subset
      simp only
      have dec_and : ∀{P Q: Prop}, (Decidable P) -> (Decidable Q) -> Decidable (P ∧ Q) := fun _ _ => inferInstance
      have dec_or : ∀{P Q: Prop}, (Decidable P) -> (Decidable Q) -> Decidable (P ∨ Q) := fun _ _ => inferInstance
      apply dec_or
      apply dec_and
      exact inferInstance
      exact List.sorted_subset.dec as bs 
      apply dec_and
      exact inferInstance
      exact List.sorted_subset.dec (a::as) bs 

#print axioms List.sorted_subset.dec

def List.sorted_subset.len_check :
  ∀(as bs: List α),
  as.sorted_subset bs -> as.len ≤ bs.len := by
  intro as bs as_sub_bs
  induction bs generalizing as with
  | nil => cases as with
    | nil =>
      apply nat.le_refl
    | cons a as  => contradiction
  | cons b bs ih =>
    cases as with
    | nil =>
      apply nat.zero_le
    | cons a as =>
      cases as_sub_bs with
      | inl h =>
        have ⟨ _, h ⟩ := h
        have := ih as h
        unfold len
        apply nat.succ_le_succ
        assumption
      | inr h =>
        have := ih (a::as) h.right
        apply nat.le_trans this
        apply nat.le_of_lt
        apply nat.lt_succ_self

#print axioms List.sorted_subset.len_check

def List.sorted_subset.push_pop
  [DecidableEq α]:
  ∀(as bs: List α),
    (∀b, as.sorted_subset bs -> as.sorted_subset (b::bs))
  ∧ (∀a, (a::as).sorted_subset bs -> as.sorted_subset bs) := by
  intro as bs
  induction bs generalizing as with
  | nil =>
    apply And.intro
    {
      intro b as_sub_bs
      cases as with
      | nil => trivial
      | cons a as => contradiction
    }
    {
      intro a aas_sub_bs
      contradiction
    }
  | cons b' bs ih =>
    match as with
    | nil =>
      apply And.intro
      {
        intros
        trivial
      }
      {
        intros
        trivial
      }
    | cons a' as =>
      apply And.intro
      {
        intro b as_sub_bs
        cases as_sub_bs with
        | inl h =>
          have ⟨ _, as_sub_bs ⟩ := h 
          match decEq a' b with
          | .isTrue h => 
            rw [h]
            apply Or.inl
            apply And.intro
            rfl
            exact (ih as).left b' as_sub_bs
          | .isFalse h =>
            apply Or.inr
            apply And.intro
            assumption
            apply Or.inl
            assumption
        | inr h =>
          have ⟨ _, aas_sub_bs ⟩ := h
          match decEq a' b with
          | .isTrue h =>
            rw [h]
            apply Or.inl
            apply And.intro
            rfl
            have as_sub_bs := (ih as).right a' aas_sub_bs
            exact (ih as).left b' as_sub_bs
          | .isFalse h =>
            apply Or.inr
            apply And.intro
            assumption
            exact (ih (a'::as)).left b' aas_sub_bs
      }
      {
        intro a as_sub_bs
        cases as_sub_bs with
        | inl h =>
          exact (ih (a'::as)).left b' h.right
        | inr h =>
          have := (ih (a'::as)).right a h.right
          exact (ih (a'::as)).left b' this
      }

#print axioms List.sorted_subset.push_pop

def List.sorted_subset.push_right
  [DecidableEq α]:
  ∀(b: α) (as bs: List α),
  as.sorted_subset bs ->
  as.sorted_subset (b::bs) := by
  intro b as bs as_sub_bs
  exact (push_pop as bs).left b as_sub_bs

#print axioms List.sorted_subset.push_right

def List.sorted_subset.pop_left
  [DecidableEq α]:
  ∀(a: α) (as bs: List α),
  (a::as).sorted_subset bs ->
  as.sorted_subset bs := by
  intro a as bs as_sub_bs
  exact (push_pop as bs).right a as_sub_bs

#print axioms List.sorted_subset.pop_left

def List.sorted_subset.proof
  [Ord α] [TotalOrder α]:
  ∀(as bs: List α),
  is_sorted bs ->
  as.sorted_subset bs ->
  ∀x, x ∈ as -> x ∈ bs := by
  intro as bs sorted_bs as_sub_bs x x_in_as
  induction bs generalizing as with
  | nil =>
    match as with
    | .nil => trivial
    | .cons _ _ => contradiction
  | cons b bs ih =>
  match as with
  | .nil => trivial
  | .cons a as  =>
  match x_in_as with
  | .head _ =>
    match as_sub_bs with
    | .inl h =>
      have ⟨ a_eq_b, _ ⟩ := h
      rw [←a_eq_b]
      exact List.Mem.head _
    | .inr h =>
      have ⟨ _, xas_sub_bs ⟩ := h
      apply List.Mem.tail
      apply ih (x::as) sorted_bs.pop
      exact xas_sub_bs
      apply List.Mem.head _
  | .tail _ x_in_as =>
    match as_sub_bs with
    | .inl h => 
      have ⟨ _, as_sub_bs ⟩ := h
      apply List.Mem.tail
      exact ih _ sorted_bs.pop as_sub_bs x_in_as
    | .inr h =>
      have ⟨ _, aas_in_bs ⟩ := h
      apply List.Mem.tail
      apply ih
      exact sorted_bs.pop
      exact aas_in_bs.pop_left
      assumption

#print axioms List.sorted_subset.proof

def List.sorted_subset.first_not_picked
  [Ord α] [tle: TotalOrder α]
  : ∀(a b: α) (as bs: List α),
     a ≠ b
  -> (a::as).sorted_subset (b::bs)
  -> is_sorted (b::bs)
  -> b ≤ a := by
    intro a b as bs a_ne_b as_sub_bs sorted_bs
    match tle.decide a b with
    | .Gt a_ge_b =>
      apply tle.le_of_lt
      assumption
    | .Eq a_eq_b => contradiction
    | .Lt a_le_b =>
      apply False.elim
      unfold sorted_subset at as_sub_bs
      cases as_sub_bs with
      | inl h => 
        have ⟨ _, _ ⟩ := h
        contradiction
      | inr h =>
        have ⟨ _, aas_sub_bs ⟩ := h
        have : ∀y, y ∈ bs -> a ≠ y := by
          intro y y_in_bs
          have := sorted_bs.first
          have := this y y_in_bs
          apply tle.ne_of_lt
          apply tle.lt_of_lt_and_le <;> assumption
        have a_in_bs := List.sorted_subset.proof (a::as) bs sorted_bs.pop aas_sub_bs a (.head _)
        have := this a a_in_bs
        contradiction

#print axioms List.sorted_subset.first_not_picked

def List.sorted_subset.trans 
  [Ord α] [tle: TotalOrder α]
  (as bs cs: List α) :
  is_sorted as ->
  is_sorted bs ->
  is_sorted cs ->
  as.sorted_subset bs -> bs.sorted_subset cs -> as.sorted_subset cs := by
  intro sorted_as sorted_bs sorted_cs as_sub_bs bs_sub_cs
  induction cs generalizing as bs with
  | nil =>
    cases bs with
    | nil => assumption
    | cons b bs =>
      unfold sorted_subset at bs_sub_cs
      contradiction
  | cons c cs ih =>
    cases as with
    | nil => trivial
    | cons a as =>
      unfold sorted_subset
      simp only
      cases bs with
      | nil =>
        unfold sorted_subset at as_sub_bs
        contradiction
      | cons b bs =>
      unfold sorted_subset at bs_sub_cs
      cases bs_sub_cs with
      | inl h =>
        have ⟨ b_eq_c, bs_sub_cs ⟩ := h
        unfold sorted_subset at as_sub_bs
        cases as_sub_bs with 
        | inl h =>
          have ⟨ a_eq_b, as_sub_bs ⟩ := h
          apply Or.inl
          apply And.intro
          exact a_eq_b.trans b_eq_c
          apply ih
          exact sorted_as.pop
          exact sorted_bs.pop
          exact sorted_cs.pop
          assumption
          assumption
        | inr h =>
          have ⟨ a_ne_b, aas_sub_bs ⟩ := h
          apply Or.inr
          apply And.intro
          rw [←b_eq_c]
          assumption
          apply ih (a::as) bs
          any_goals assumption
          exact sorted_bs.pop
          exact sorted_cs.pop
      | inr h =>
        apply Or.inr
        have ⟨ b_ne_c, bbs_sub_cs ⟩ := h
        cases as_sub_bs with
        | inl h =>
          have ⟨ a_eq_b, _ ⟩ := h
          apply And.intro
          rw [a_eq_b]
          assumption
          apply ih _ (b::bs)
          assumption
          assumption
          exact sorted_cs.pop
          exact .inl h
          assumption
        | inr h =>
          have ⟨ a_ne_b, as_sub_bs ⟩ := h
          have b_le_a := List.sorted_subset.first_not_picked a b as bs a_ne_b (by apply as_sub_bs.push_right) sorted_bs
          have c_le_b := List.sorted_subset.first_not_picked b c bs cs b_ne_c (by apply bbs_sub_cs.push_right) sorted_cs
          have c_lt_b := tle.lt_of_le_and_ne c_le_b b_ne_c.symm
          have b_lt_a := tle.lt_of_le_and_ne b_le_a a_ne_b.symm
          apply And.intro
          apply tle.ne_of_gt
          apply tle.lt_trans <;> assumption
          exact ih (a::as) bs sorted_as sorted_bs.pop sorted_cs.pop as_sub_bs bbs_sub_cs.pop_left

#print axioms List.sorted_subset.trans

def List.sorted_subset.antisymm
  [Ord α] [TotalOrder α]
  (as bs: List α) :
  is_sorted as ->
  is_sorted bs ->
  as.sorted_subset bs -> bs.sorted_subset as -> as = bs := by
  intro sorted_as sorted_bs as_sub_bs bs_sub_as
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs => contradiction
  | cons a as ih =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      cases as_sub_bs with
      | inl h =>
        have ⟨ a_eq_b, as_sub_bs ⟩ := h
        cases bs_sub_as with
        | inl h =>
          have ⟨ _, bs_sub_as ⟩ := h
          congr
          apply ih
          exact sorted_as.pop
          exact sorted_bs.pop
          assumption
          assumption
        | inr bbs_as =>
          have := bbs_as.right.trans bs
          have := this sorted_bs sorted_as.pop sorted_bs.pop as_sub_bs
          have ge := List.sorted_subset.len_check (b::bs) bs this
          have lt : bs.len < (b::bs).len := by apply nat.lt_succ_self
          have := nat.not_lt_and_ge lt ge
          contradiction
      | inr h =>
          have := bs_sub_as.trans bs
          have := this sorted_bs sorted_as sorted_bs.pop h.right
          have ge := List.sorted_subset.len_check (b::bs) bs this
          have lt : bs.len < (b::bs).len := by apply nat.lt_succ_self
          have := nat.not_lt_and_ge lt ge
          contradiction

#print axioms List.sorted_subset.antisymm

