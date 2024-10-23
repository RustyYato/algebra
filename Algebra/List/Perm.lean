import Algebra.List.Basic

inductive list.perm : list α -> list α -> Prop where
| trans : perm as bs -> perm bs cs -> perm as cs
| nil : perm nil nil
| cons : perm as bs -> perm (cons x as) (cons x bs)
| swap : perm (cons a (cons b cs)) (cons b (cons a cs))

inductive list.min_count : α -> list α -> nat -> Prop where
| nil : min_count x nil 0
| cons : min_count x as n -> min_count x (cons a as) n
| head : min_count a as n -> min_count a (cons a as) n.succ

def list.min_count.zero : list.min_count x as 0 := by
  induction as with
  | nil => exact .nil
  | cons a as ih => exact ih.cons

def list.min_count.le (n m: nat) :
  m ≤ n ->
  list.min_count x as n ->
  list.min_count x as m := by
  intro m_le_n mc
  induction mc generalizing m with
  | nil =>
    cases nat.le_zero m_le_n
    exact nil
  | cons _ ih =>
    apply cons
    apply ih
    assumption
  | head _ ih =>
    cases lt_or_eq_of_le m_le_n <;> rename_i h
    have := nat.le_of_lt_succ h
    apply cons
    apply ih
    assumption
    subst m
    apply head
    apply ih
    rfl

@[refl]
def list.perm.refl (as: list α) : list.perm as as := by
  induction as with
  | nil => exact .nil
  | cons _ _ ih => exact ih.cons

@[symm]
def list.perm.symm : list.perm as bs -> list.perm bs as := by
  intro perm
  induction perm with
  | nil => exact nil
  | cons _ ih => exact ih.cons
  | trans _ _ aih bih => exact bih.trans aih
  | swap => exact swap

def list.perm.eqv : @Equivalence (list α) list.perm where
  refl := refl
  symm := symm
  trans := trans

def list.perm.setoid α : Setoid (list α) where
  r := list.perm
  iseqv := list.perm.eqv

def list.perm.min_count {as bs: list α} :
  as.perm bs -> ∀x n, as.min_count x n -> bs.min_count x n := by
  intro perm x n h
  induction perm generalizing n with
  | trans _ _ aih bih =>
    apply bih
    apply aih
    exact h
  | nil =>
    cases h
    exact .nil
  | cons _ ih =>
    cases h
    apply min_count.cons
    apply ih
    assumption
    apply min_count.head
    apply ih
    assumption
  | swap =>
    cases h <;> rename_i h
    <;> (cases h <;> rename_i h)
    apply min_count.cons
    apply min_count.cons
    assumption
    apply min_count.head
    apply min_count.cons
    assumption
    apply min_count.cons
    apply min_count.head
    assumption
    apply min_count.head
    apply min_count.head
    assumption

def list.cons_perm_of_mem (as: list α) (x: α) :
  x ∈ as -> ∃as', as.perm (cons x as') := by
  intro h
  induction h with
  | head as => exists as
  | tail a as _ ih =>
    have ⟨as',perm⟩ := ih
    exists (cons a as')
    apply list.perm.trans perm.cons
    apply list.perm.swap

def list.find_cons_perm_of_mem [DecidableEq α] (as: list α) (x: α) :
  x ∈ as -> (as': list α) ×' as.perm (cons x as') := by
  intro h
  match as with
  | .cons a as =>
  if g:x = a then
    exists as
    rw [g]
  else
    have ⟨as',perm⟩ := find_cons_perm_of_mem as x (by
      cases h
      contradiction
      assumption)
    exists (cons a as')
    apply list.perm.trans perm.cons
    apply list.perm.swap

def list.mem_iff_min_count {as: list α} {x: α} : x ∈ as ↔ as.min_count x 1 := by
  induction as with
  | nil =>
    apply Iff.intro <;> (intro; contradiction)
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases h
    apply min_count.head
    apply min_count.zero
    apply min_count.cons
    apply ih.mp
    assumption
    intro h
    cases h
    apply list.mem.tail
    apply ih.mpr
    assumption
    apply list.mem.head

def list.perm_iff_forall_min_count {as bs: list α} :
  as.perm bs ↔ ∀x n, as.min_count x n ↔ bs.min_count x n := by
  apply Iff.intro
  · intro perm x n
    apply Iff.intro
    apply list.perm.min_count
    assumption
    apply list.perm.min_count
    symm; assumption
  · intro h
    induction as generalizing bs with
    | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => nomatch (h b 1).mpr (.head .zero)
    | cons a as ih =>
      have := mem_iff_min_count.mpr ((h a 1).mp (.head .zero))
      have ⟨bs',bs_perm_bs'⟩ := cons_perm_of_mem _ _ this
      apply perm.trans _ bs_perm_bs'.symm
      apply perm.cons
      apply ih
      intro x n
      apply Iff.intro
      intro g
      have := bs_perm_bs'.min_count x n ((h _ _).mp g.cons)
      cases this
      assumption
      rename_i n _
      have := bs_perm_bs'.min_count a _ ((h _ _).mp g.head)
      cases this
      rename_i g'
      apply g'.le
      apply le_of_lt
      apply nat.lt_succ_self
      assumption
      intro g
      cases (h _ _).mpr (bs_perm_bs'.symm.min_count x n g.cons) <;> rename_i g'
      assumption
      cases (h _ _).mpr (bs_perm_bs'.symm.min_count _ _ g.head) <;> rename_i g'
      apply g'.le
      apply le_of_lt
      apply nat.lt_succ_self
      assumption

def list.perm.length {as bs: list α} :
  as.perm bs -> as.length = bs.length := by
  intro h
  induction h with
  | nil => rfl
  | cons _ ih => rw [cons_length, cons_length, ih]
  | trans _ _ aih bih => rw [aih, bih]
  | swap => rfl

def list.perm.mem {as bs: list α} :
  as.perm bs -> ∀x, x ∈ as ↔ x ∈ bs := by
  intro h x
  apply Iff.trans
  apply mem_iff_min_count
  apply flip Iff.trans
  symm
  apply mem_iff_min_count
  apply perm_iff_forall_min_count.mp
  assumption

def list.min_count.pop_head : list.min_count x (.cons x as) (n.succ) -> list.min_count x as n := by
  intro h
  cases h
  apply le _ _ _
  assumption
  apply le_of_lt
  apply nat.lt_succ_self
  assumption

def list.perm.pop_head : list.perm (.cons x as) (.cons x bs) -> list.perm as bs := by
  intro h
  have := perm_iff_forall_min_count.mp h
  apply perm_iff_forall_min_count.mpr
  intro y n
  apply Iff.intro
  intro g
  cases (this y n).mp g.cons
  assumption
  rename_i n _
  cases (this x n.succ.succ).mp g.head <;> rename_i g'
  apply g'.le
  apply le_of_lt
  apply nat.lt_succ_self
  assumption

  intro g
  cases (this y n).mpr g.cons
  assumption
  rename_i n _
  cases (this x n.succ.succ).mpr g.head <;> rename_i g'
  apply g'.le
  apply le_of_lt
  apply nat.lt_succ_self
  assumption

instance list.dec_min_count [DecidableEq α] (as: list α) (x) (n) : Decidable (as.min_count x n) :=
    match n with
    | .zero => Decidable.isTrue .zero
    | .succ n =>
    match as with
    | .nil => Decidable.isFalse (nomatch ·)
    | .cons a as =>
      match decEq x a with
      | .isTrue h =>
        match as.dec_min_count x n with
        | .isTrue g => Decidable.isTrue (h ▸ g.head)
        | .isFalse g => Decidable.isFalse (by
          subst h
          intro h₀
          exact g h₀.pop_head)
      | .isFalse h =>
        match as.dec_min_count x n.succ with
        | .isTrue g => Decidable.isTrue g.cons
        | .isFalse g => Decidable.isFalse (by
          intro h₀
          cases h₀ <;> rename_i h₀
          exact g h₀
          contradiction)

instance list.dec_perm [DecidableEq α] (as bs: list α) : Decidable (as.perm bs) :=
    match as, bs with
    | .nil, .nil => Decidable.isTrue .nil
    | .nil, .cons b _ => Decidable.isFalse fun h => nomatch (h.mem b).mpr (.head _)
    | .cons a as, bs =>
      if h:a ∈ bs then
        have ⟨bs',perm⟩  := list.find_cons_perm_of_mem _ _ h
        match dec_perm as bs' with
        | .isTrue g => .isTrue (g.cons.trans perm.symm)
        | .isFalse g => .isFalse (fun g' => g (g'.trans perm).pop_head)
      else
        .isFalse fun g => h ((g.mem a).mp (.head _))
