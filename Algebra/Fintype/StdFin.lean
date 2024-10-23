import Algebra.Fintype.Basic

section Fin.Fintype

def all_fins_lt (n: Nat) : Nat -> list (Fin n)
| 0 => .[]
| m + 1 =>
  have := all_fins_lt n  m
  if h:m < n then .cons ⟨m,h⟩ this else this

def mem_all_fins_lt (n m: Nat) : ∀x, x ∈ all_fins_lt n m ↔ x.val < m := by
  intro x
  induction m with
  | zero =>
    apply Iff.intro
    intro h
    contradiction
    intro h
    contradiction
  | succ m ih =>
    unfold all_fins_lt
    dsimp
    split <;> (apply Iff.intro) <;> (rename_i h; intro g)
    cases g
    apply Nat.lt_succ_self
    apply Nat.lt_trans
    apply ih.mp
    assumption
    apply Nat.lt_succ_self
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ g)
    apply list.mem.tail
    apply ih.mpr
    assumption
    subst m
    apply list.mem.head
    apply Nat.lt_trans
    apply ih.mp
    assumption
    apply Nat.lt_succ_self
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ g)
    apply ih.mpr
    assumption
    subst m
    have := h x.isLt
    contradiction

def nodup_all_fins_lt (n m: Nat) : (all_fins_lt n m).nodup := by
  induction m with
  | zero => exact list.pairwise.nil
  | succ m ih =>
    unfold all_fins_lt
    dsimp
    split
    apply list.pairwise.cons
    · intro x mem
      have := (mem_all_fins_lt n m x).mp mem
      intro h
      subst x
      have := Nat.lt_irrefl _ this
      contradiction
    repeat exact ih

def all_fins_lt_length (n m: Nat) : (all_fins_lt n m).length = .ofNat (min n m) := by
  induction m with
  | zero =>
    rw [Nat.min_zero]
    rfl
  | succ m ih =>
    unfold all_fins_lt
    dsimp
    split
    rw [list.cons_length, ih, Nat.min_eq_right, Nat.min_eq_right]
    rfl
    apply Nat.succ_le_of_lt
    assumption
    apply Nat.le_of_lt
    assumption
    rw [ih]
    have := Nat.le_of_not_lt (by assumption)
    rw [Nat.min_eq_left, Nat.min_eq_left]
    apply Nat.le_trans this
    apply Nat.le_succ
    assumption

end Fin.Fintype

instance Fin.FintypeInst : Fintype (Fin n) where
  all := .ofList (all_fins_lt n n) (nodup_all_fins_lt n n)
  all_spec := by
    intro x
    apply (Finset.ofList_mem _ _ _).mpr
    apply (mem_all_fins_lt _ _ _).mpr
    exact x.isLt

def Fin.card (f: Fintype (Fin n)) : f.card = .ofNat n := by
  rw [Subsingleton.allEq f FintypeInst]
  unfold FintypeInst Fintype.card Fintype.all
  dsimp
  rw [Finset.ofList_card, all_fins_lt_length, Nat.min_self n]
