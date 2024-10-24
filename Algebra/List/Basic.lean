import Algebra.List.Notation
import Algebra.Nat.Div
import Algebra.AxiomBlame
import Algebra.Function.Basic

def list.length : list α -> nat
| .nil => .zero
| .cons _ as => as.length.succ

def list.nil_length : (nil: list α).length = 0 := rfl

def list.cons_length (a: α) (as: list α) : (cons a as).length = as.length.succ := rfl

def list.get? (as: list α) (x: nat) : Option α :=
  match as with
  | .nil => .none
  | .cons a as =>
  match x with
  | .zero => .some a
  | .succ x => as.get? x

def list.get?_is_some_iff {as: list α} {x: nat} :
  (as.get? x).isSome ↔ x < as.length := by
  induction as generalizing x with
  | nil =>
    apply Iff.intro
    intro h
    contradiction
    intro h
    have := nat.not_lt_zero h
    contradiction
  | cons a as ih =>
    apply Iff.intro
    · intro h
      unfold get? at h
      split at h
      apply nat.zero_lt_succ
      apply nat.succ_lt_succ
      apply ih.mp
      assumption
    · intro h
      unfold get?
      split
      rfl
      apply ih.mpr
      apply nat.lt_of_succ_lt_succ
      assumption

instance : GetElem? (list α) nat α (fun l n => n < l.length) where
  getElem? as n := as.get? n
  getElem! as n := (as.get? n).getD default
  getElem as n h := (as.get? n).get (list.get?_is_some_iff.mpr h)

def list.getElem?_eq_get? (as: list α) (n: nat) : as[n]? = as.get? n := rfl
def list.getElem_eq_get? (as: list α) (n: nat) (h: n < as.length) : as[n] = (as.get? n).get (list.get?_is_some_iff.mpr h) := rfl
def list.getElem!_eq_get? [Inhabited α] (as: list α) (n: nat) : as[n]! = (as.get? n).getD default := rfl

instance list.LawfulGetElemInst : LawfulGetElem (list α) nat α (fun l n => n < l.length) where
  getElem?_def := by
    intro as n h
    rw [list.getElem?_eq_get?]
    split <;> rename_i h
    rw [list.getElem_eq_get?, Option.some_get]
    cases g:as.get? n
    rfl
    rename_i a'
    have : (as.get? n).isSome := by
      rw [g]
      rfl
    have :=list.get?_is_some_iff.mp this
    contradiction
  getElem!_def := by
    intro _ as n
    rw [list.getElem?_eq_get?, list.getElem!_eq_get?]
    cases as.get? n
    rfl
    rfl

def list.getElem?_eq_getElem (as: list α) (n: nat) (h: n < as.length) :
  as[n]? = .some as[n] := by
  exact getElem?_pos as n h

def list.getElem!_eq_getElem? [Inhabited α] (as: list α) (n: nat) :
  as[n]! = as[n]?.getD default := rfl

def list.getElem!_eq_getElem [Inhabited α] (as: list α) (n: nat) (h: n < as.length) :
  as[n]! = as[n] := by
  rw [getElem_eq_get?, getElem!_eq_get?]
  unfold Option.get
  split
  rename_i h _
  rw [h]
  rfl

def list.cons_getElem? (a: α) (as: list α) (n: nat) : (list.cons a as)[n.succ]? = as[n]? := rfl

def list.cons_getElem (a: α) (as: list α) (n: nat) (h: n < as.length) : (list.cons a as)[n.succ] = as[n] := rfl

inductive list.mem : α -> list α -> Prop where
| head (as: list α) : mem a (.cons a as)
| tail (a: α) (as: list α) : mem x as -> mem x (.cons a as)

instance : Membership α (list α) := ⟨list.mem⟩

def list.mem_iff_getElem (as: list α) (x: α) : x ∈ as ↔ ∃n, ∃h: n < as.length, x = as[n] := by
  induction as with
  | nil =>
    apply Iff.intro
    intro h; contradiction
    intro ⟨n,_,_⟩; cases n <;> contradiction
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases h
    exists 0
    exists nat.zero_lt_succ
    have ⟨n,h,prf⟩ := ih.mp (by assumption)
    exists n.succ
    exists h
    intro ⟨n,h,prf⟩
    subst x
    cases n
    apply list.mem.head
    apply list.mem.tail
    apply ih.mpr
    rename_i n
    exists n
    exists h

def list.mem_getElem (as: list α) (n: nat) (h: n < as.length) :
  as[n] ∈ as := by
  apply (mem_iff_getElem _ _).mpr
  exists n
  exists h

def list.attach_with (P: α -> Prop) (as: list α) (h: ∀x ∈ as, P x) : list { x // P x } :=
  match as with
  | .nil => .nil
  | .cons a as => .cons ⟨a, h _ (.head _) ⟩ <| as.attach_with P (fun x mem => h x (.tail _ _ mem))

def list.attach (as: list α) : list { x // x ∈ as } := as.attach_with (· ∈ as) (fun _ => id)

def list.mem_attach_with {as: list α} { P } { h } : ∀{x}, x ∈ as.attach_with P h ↔ x.val ∈ as := by
  intro ⟨x,h⟩
  induction as with
  | nil =>
    apply Iff.intro
    intro g
    contradiction
    intro g
    contradiction
  | cons a as ih =>
    apply Iff.intro
    intro g
    cases g
    apply list.mem.head
    apply list.mem.tail
    apply ih.mp
    assumption
    intro g
    cases g
    apply list.mem.head
    apply list.mem.tail
    apply ih.mpr
    assumption

def list.mem_attach {as: list α} : ∀{x}, x ∈ as.attach := by
  intro ⟨x,h⟩
  apply mem_attach_with.mpr
  assumption

def list.foldl (f: α -> β -> β) (acc: β) : list α -> β
| .nil => acc
| .cons a as => as.foldl f (f a acc)

def list.sum : list nat -> nat := list.foldl (· + ·) 0

def list.map (f: α -> β) : list α -> list β
| .nil => .nil
| .cons a as => .cons (f a) (as.map f)

def list.mem_map {f: α -> β} {as: list α} : ∀{x}, x ∈ (as.map f) ↔ ∃a, a ∈ as ∧ f a = x := by
  intro x
  induction as with
  | nil =>
    unfold map
    apply Iff.intro; intro; contradiction
    intro ⟨h,_,_⟩
    contradiction
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases h
    exists a
    apply And.intro
    apply list.mem.head
    rfl
    have ⟨a',mem,prf⟩  := ih.mp (by assumption)
    exists a'
    apply And.intro
    apply list.mem.tail
    assumption
    assumption
    intro ⟨a',mem,eq⟩
    subst x
    cases mem
    apply list.mem.head
    apply list.mem.tail
    apply ih.mpr
    exists a'

def list.length_map {f: α -> β} {as: list α} : (as.map f).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    unfold map length
    rw [ih]

def list.getElem?_map (f: α -> β) (as: list α) (n: nat) :
  (as.map f)[n]? = as[n]?.map f
  := by
  rw [getElem?_eq_get?, getElem?_eq_get?]
  induction as generalizing n with
  | nil => rfl
  | cons a as ih =>
  cases n with
  | zero => rfl
  | succ n =>
    rw [map, get?]
    dsimp
    rw [ih]
    rfl

def list.getElem_map (f: α -> β) (as: list α) (n: nat) (h: n < as.length) :
  (as.map f)[n]'(list.length_map.symm ▸ h) = f as[n]
  := by
  apply Option.some.inj
  rw [←Option.map_some', ←getElem?_eq_getElem, ←getElem?_eq_getElem]
  apply getElem?_map

def list.append (as bs: list α) : list α :=
  match as with
  | .nil =>  bs
  | .cons a as => .cons a (as.append bs)

instance : Append (list α) := ⟨list.append⟩

def list.mem_append {as bs: list α} : ∀{x}, x ∈ as ++ bs ↔ x ∈ as ∨ x ∈ bs := by
  intro x
  induction as with
  | nil =>
    apply Iff.intro
    exact Or.inr
    intro h
    cases h
    contradiction
    assumption
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases h
    apply Or.inl
    apply list.mem.head
    cases ih.mp (by assumption)
    apply Or.inl; apply list.mem.tail; assumption
    apply Or.inr; assumption
    intro h
    cases h <;> rename_i h
    cases h
    apply list.mem.head
    apply list.mem.tail
    apply ih.mpr
    apply Or.inl
    assumption
    apply list.mem.tail
    apply ih.mpr
    apply Or.inr
    assumption

def list.nil_append (bs: list α) : .[] ++ bs = bs := rfl

def list.cons_append (a: α) (as bs: list α) : (.cons a as) ++ bs = .cons a (as ++ bs) := rfl

def list.append_nil (as: list α) : as ++ .[] = as := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [cons_append, ih]

def list.append_cons (b: α) (as bs: list α) : as ++ (.cons b bs) = as ++ .[b] ++ bs := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [cons_append, ih]; rfl

def list.append_assoc (as bs cs: list α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [cons_append, cons_append, ih, cons_append]

def list.length_append (as bs: list α) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [cons_append, length, ih]
    rfl

def list.getElem?_append (as bs: list α) (n: nat) :
  (as ++ bs)[n]? = if h:n < as.length then .some as[n] else bs[n - as.length]?
  := by
  induction as generalizing n with
  | nil =>
    rw [dif_neg]
    rfl
    exact nat.not_lt_zero
  | cons a as ih =>
    cases n with
    | zero =>
      rw [dif_pos]
      rfl
      apply nat.zero_lt_succ
    | succ n =>
      have := ih n
      rw [cons_append, cons_getElem?]
      split
      rw [dif_pos] at this
      rw [cons_getElem, this]
      rfl
      assumption
      rw [dif_neg] at this
      rw [this]
      rfl
      assumption

def list.getElem_append (as bs: list α) (n: nat) (h: n < as.length + bs.length) :
  (as ++ bs)[n]'(length_append as bs ▸ h) = if h:n < as.length then as[n] else bs[n - as.length]'(by
    have h := le_of_not_lt h
    apply nat.add.lt_cancel_right
    rw [nat.sub_add_inv, nat.add.comm]
    assumption
    assumption)
  := by
  dsimp
  have := list.getElem?_append as bs n
  apply Option.some.inj
  rw [←getElem?_eq_getElem]
  split
  rw [dif_pos] at this
  rw [this]
  rfl
  assumption
  rw [dif_neg] at this
  rw [this]
  rw [getElem?_eq_getElem]
  assumption

def list.snoc (as: list α) (x: α) : list α := as ++ .[x]

def list.mem_snoc {as: list α} {a': α} : ∀{x}, x ∈ as.snoc a' ↔ x ∈ as ∨ x = a' := by
  intro x
  apply Iff.trans
  apply list.mem_append
  apply Iff.intro
  · intro  h
    cases h
    apply Or.inl; assumption
    apply Or.inr
    rename_i h
    cases h
    rfl
    contradiction
  · intro h
    cases h
    apply Or.inl; assumption
    apply Or.inr; subst x; apply list.mem.head

def list.flat_map (f: α -> list β) : list α -> list β
| .nil => .nil
| .cons a as => (f a) ++ (as.flat_map f)

def list.mem_flat_map {f: α -> list β} {as: list α} :
  ∀{x}, x ∈ as.flat_map f ↔ ∃a', a' ∈ as ∧ x ∈ f a' := by
  intro x
  induction as with
  | nil =>
    apply Iff.intro; intro h; contradiction
    intro ⟨h,_,_⟩; contradiction
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases mem_append.mp h
    exists a
    apply And.intro
    apply list.mem.head
    assumption
    have ⟨a',_,_⟩ := ih.mp (by assumption)
    exists a'
    apply And.intro
    apply list.mem.tail
    assumption
    assumption
    intro ⟨a',mem,eq⟩
    apply mem_append.mpr
    cases mem
    apply Or.inl
    assumption
    apply Or.inr
    apply ih.mpr
    exists a'

def list.flatten : list (list α) -> list α := list.flat_map id

def list.mem_flatten {as: list (list α)} : ∀{x}, x ∈ as.flatten ↔ ∃as' ∈ as, x ∈ as' := by
  intro x
  apply Iff.trans
  apply mem_flat_map
  apply Iff.intro
  intro ⟨as',h,eq⟩
  exists as'
  intro ⟨as',h,eq⟩
  exists as'

def list.repeat (a: α) : nat -> list α
| .zero => .[]
| .succ n => .cons a (list.repeat a n)

def list.mem_repeat {a: α} {n: nat} : ∀{x}, x ∈ list.repeat a n ↔ x = a ∧ 0 < n := by
  intro x
  induction n with
  | zero =>
    apply Iff.intro
    intro h
    contradiction
    intro ⟨_,_⟩
    contradiction
  | succ n ih =>
    apply Iff.intro
    intro h
    cases h
    apply And.intro
    rfl
    exact nat.zero_lt_succ
    have := ih.mp (by assumption)
    exact ⟨this.left,nat.zero_lt_succ⟩
    intro ⟨h,_⟩
    subst x
    apply list.mem.head

def list.length_repeat (a: α) (n: nat) : (list.repeat a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [list.repeat, length, ih]

def list.getElem_repeat (a: α) (n m: nat) :
  (h: m < n) -> (list.repeat a n)[m]'(by rw [list.length_repeat]; exact h) = a := by
  intro h
  induction n generalizing m with
  | zero => cases m <;> contradiction
  | succ n ih =>
    cases m
    rfl
    erw [cons_getElem, ih]
    assumption

def list.range : nat -> list nat
| .zero => .[]
| .succ n => .cons n (list.range n)

def list.mem_range (n: nat) : ∀{m}, m ∈ list.range n ↔ m < n := by
  intro m
  induction n with
  | zero =>
    apply Iff.intro
    intro h; contradiction
    intro h; cases m <;> contradiction
  | succ n ih =>
    apply Iff.intro
    intro h
    cases h
    apply nat.lt_succ_self
    apply lt_trans
    apply ih.mp
    assumption
    apply nat.lt_succ_self
    intro h
    cases lt_or_eq_of_le (nat.le_of_lt_succ h)
    apply list.mem.tail
    apply ih.mpr
    assumption
    subst m
    apply list.mem.head

def list.zip (as: list α) (bs: list β) : list (α × β) :=
  match as with
  | .[] => .[]
  | .cons a as =>
  match bs with
  | .[] => .[]
  | .cons b bs =>
    .cons ⟨a,b⟩ (as.zip bs)

def list.mem_zip {as: list α} {bs: list β} :
  ∀{x}, x ∈ as.zip bs ↔ ∃n, ∃h₀: n < as.length, ∃h₁: n < bs.length, x = ⟨as[n],bs[n]⟩ := by
  intro x
  induction as generalizing bs with
  | nil =>
    apply Iff.intro
    intro h
    contradiction
    intro ⟨n,h₀,_⟩
    have := nat.not_lt_zero <| h₀
    contradiction
  | cons a as ih =>
    cases bs with
    | nil =>
      apply Iff.intro
      intro h
      contradiction
      intro ⟨n,_,h₁,_⟩
      have := nat.not_lt_zero <| h₁
      contradiction
    | cons b bs =>
      apply Iff.intro
      intro h
      cases h
      exists 0
      exists nat.zero_lt_succ
      exists nat.zero_lt_succ
      rename_i mem
      have ⟨n,h₀,h₁,prf⟩ := ih.mp mem
      exists n.succ
      exists h₀
      exists h₁
      intro ⟨n,h₀,h₁,prf⟩
      cases n with
      | zero => subst x; apply list.mem.head
      | succ n =>
        apply list.mem.tail
        apply ih.mpr
        exists n
        exists h₀
        exists h₁

def list.product (as: list α) (bs: list β) : list (α × β) :=
  as.flat_map (fun a => list.zip (list.repeat a bs.length) bs)

def list.mem_product {as: list α} {bs: list β} : ∀{x}, x ∈ as.product bs ↔ x.1 ∈ as ∧ x.2 ∈ bs := by
  intro x
  apply Iff.trans
  apply list.mem_flat_map
  apply Iff.intro
  intro ⟨a,a_in_as,x_in_zip⟩
  have ⟨n,h₀,h₁,prf⟩ := list.mem_zip.mp x_in_zip
  · cases x with | mk x₀ x₁ =>
    have ⟨x₀_def,x₁_def⟩  := Prod.mk.inj prf
    dsimp
    subst x₀
    subst x₁
    apply And.intro
    rw [getElem_repeat]
    assumption
    assumption
    apply mem_getElem
  · intro ⟨l,r⟩
    exists x.fst
    apply And.intro
    assumption
    apply mem_zip.mpr
    have ⟨n₁,hn₁,prf₁⟩ := (mem_iff_getElem _ _).mp r
    exists n₁
    exists (by
      rw [length_repeat]
      assumption)
    exists (by assumption)
    cases x
    congr
    dsimp
    rw [getElem_repeat]
    assumption

instance list.dec_mem [DecidableEq α] (as: list α) (x: α) : Decidable (x ∈ as) :=
    match as with
    | .nil => Decidable.isFalse (nomatch ·)
    | .cons a as =>
      match decEq x a with
      | .isTrue h => .isTrue (h ▸ .head _)
      | .isFalse h =>
      match dec_mem as x with
      | .isTrue g => .isTrue (.tail _ _ g)
      | .isFalse g => .isFalse (fun h => by cases h <;> contradiction)

instance list.dec_forall_mem (P: α -> Prop) [DecidablePred P] (as: list α) : Decidable (∀x ∈ as, P x) :=
    match as with
    | .nil => Decidable.isTrue (fun _ h => nomatch h)
    | .cons a as =>
      if p:P a then
        match dec_forall_mem P as with
        | .isTrue h =>
          .isTrue fun _ mem =>
            match mem with
            | .head _ => p
            | .tail _ _ mem => h _ mem
        | .isFalse h => .isFalse (fun g => h (fun x h => g x (list.mem.tail _ _ h)))
      else
        .isFalse (fun g => p (g _ (.head _)))

inductive list.pairwise (P: α -> α -> Prop) : list α -> Prop where
| nil : pairwise P nil
| cons : (∀x ∈ as, P a x) -> pairwise P as -> pairwise P (cons a as)

def list.pairwise.head : pairwise P (.cons a as) -> (∀x ∈ as, P a x)
| .cons h _ => h

def list.pairwise.tail : pairwise P (.cons a as) -> pairwise P as
| .cons _ t => t

abbrev list.nodup : list α -> Prop := list.pairwise (· ≠ ·)

instance list.dec_pairwise {P: α -> α -> Prop} [DecidableRel P] : Decidable (list.pairwise P as) :=
  match as with
  | .[] => .isTrue .nil
  | .cons a as =>
    have : Decidable (list.pairwise P as) := list.dec_pairwise
    match inferInstanceAs (Decidable ((∀x ∈ as, P a x) ∧ list.pairwise P as)) with
    | .isTrue h => .isTrue (.cons h.left h.right)
    | .isFalse h => .isFalse (fun g => h ⟨g.head, g.tail⟩)

def list.nodup_map (f: α -> β) (as: list α) : as.nodup -> Function.Injective f -> (as.map f).nodup := by
  intro asnodup injf
  induction asnodup with
  | nil => exact list.pairwise.nil
  | cons a_not_mem _ ih =>
    rename_i as a _
    apply list.pairwise.cons
    intro b b_in_map fa_ne_b
    have ⟨a',a'_in_as,fa'_eq_b⟩ := mem_map.mp b_in_map
    subst b
    cases injf fa'_eq_b
    have := a_not_mem a a'_in_as
    contradiction
    assumption

def list.drop (n: nat) (as: list α) : list α :=
  match n with
  | .zero => as
  | .succ n =>
    match as with
    | .[] => .nil
    | .cons _ as => as.drop n

def list.drop_zero (as: list α) : as.drop 0 = as := rfl

-- keep idx in from so it is chosen as the termination variable
-- instead of as. this leads to a definitionaly equality with .cons
def list.insert_at (idx: nat) (x: α)  (as: list α) : list α :=
  match idx with
  | .zero => .cons x as
  | .succ idx =>
    match as with
    | .[] => .cons x .nil
    | .cons a as => .cons a (as.insert_at idx x)

def list.insert_at_zero (as: list α) (x: α) : as.insert_at 0 x = .cons x as := rfl

def list.length_insert_at (as: list α) (idx: nat) (x: α) :
  (as.insert_at idx x).length = as.length.succ := by
  induction idx generalizing as with
  | zero =>
    unfold insert_at
    rfl
  | succ idx ih =>
    cases as with
    | nil => rfl
    | cons a as =>
      unfold insert_at
      dsimp
      rw [cons_length, ih]
      rfl

def list.insert_at_get?_lt (as: list α) (n idx: nat) (x: α) :
  n < idx ->
  idx ≤ as.length ->
  (as.insert_at idx x).get? n = as.get? n := by
  intro h g
  induction idx generalizing as n with
  | zero =>
    cases n <;> contradiction
  | succ idx ih =>
    cases as with
    | nil =>
      unfold insert_at
      have := nat.le_zero g
      contradiction
    | cons a as =>
      unfold insert_at
      dsimp
      cases n
      rfl
      unfold get?
      dsimp
      apply ih
      assumption
      assumption

def list.insert_at_get?_gt (as: list α) (n idx: nat) (x: α) :
  n > idx ->
  idx ≤ as.length ->
  (as.insert_at idx x).get? n = as.get? n.pred := by
  intro h g
  induction idx generalizing as n with
  | zero =>
    cases n; contradiction
    unfold insert_at
    rfl
  | succ idx ih =>
    cases as with
    | nil =>
      have := nat.le_zero g
      contradiction
    | cons a as =>
      unfold insert_at
      dsimp
      cases n
      rfl
      rename_i n
      rw [get?]
      dsimp
      cases idx
      cases n; contradiction
      rfl
      rename_i idx
      cases n; contradiction
      rename_i n
      rw [ih]
      rfl
      assumption
      assumption

def list.insert_at_get?_eq (as: list α) (idx: nat) (x: α) :
  idx ≤ as.length ->
  (as.insert_at idx x).get? idx = x := by
  intro h
  induction idx generalizing as with
  | zero =>
    cases as <;> rfl
  | succ idx ih =>
    cases as
    cases h <;> contradiction
    unfold insert_at
    dsimp
    apply ih
    assumption

def list.insert_at_getElem_lt (as: list α) (n idx: nat) (x: α) :
  (h: n < idx) ->
  (g: idx ≤ as.length) ->
  (as.insert_at idx x)[n]'(by
    rw [length_insert_at]
    exact lt_trans h (nat.lt_succ_of_le g)
  ) = as[n]'(lt_of_lt_of_le h g) := by
  intro h g
  apply Option.some.inj
  rw [getElem_eq_get?, getElem_eq_get?, Option.some_get, Option.some_get]
  apply list.insert_at_get?_lt <;> assumption

def list.insert_at_getElem_gt (as: list α) (n idx: nat) (x: α) :
  (h: n > idx) ->
  idx ≤ as.length ->
  (g: n ≤ as.length) ->
  (as.insert_at idx x)[n]'(by
    rw [as.length_insert_at]
    apply nat.lt_succ_of_le
    assumption) = as[n.pred]'(by
    cases n
    have := nat.not_lt_zero h
    contradiction
    apply nat.lt_of_succ_le
    assumption) := by
  intro h g _
  apply Option.some.inj
  rw [getElem_eq_get?, getElem_eq_get?, Option.some_get, Option.some_get]
  apply list.insert_at_get?_gt <;> assumption

def list.insert_at_getElem_eq (as: list α) (idx: nat) (x: α) :
  (h: idx ≤ as.length) ->
  (as.insert_at idx x)[idx]'(by
    rw [length_insert_at]
    apply nat.lt_succ_of_le
    assumption) = x := by
  intro h
  apply Option.some.inj
  rw [getElem_eq_get?, Option.some_get]
  apply list.insert_at_get?_eq <;> assumption

-- keep idx in from so it is chosen as the termination variable
-- instead of as. this leads to a definitionaly equality with .cons
def list.remove (idx: nat) (as: list α) (h: idx < as.length) : list α :=
  match idx with
  | .zero => match as with
    | .cons _ as => as
  | .succ idx =>
    match as with
    | .cons a as => .cons a (as.remove idx h)

def list.cons_remove_zero (a: α) (as: list α) : (list.cons a as).remove 0 rfl = as := rfl
def list.cons_remove_succ (idx: nat) (a: α) (as: list α) (h: idx < as.length) : (list.cons a as).remove idx.succ h = .cons a (as.remove idx h) := rfl

def list.length_remove (as: list α) (idx: nat) (h: idx < as.length) :
  (as.remove idx h).length = as.length.pred := by
  induction idx generalizing as with
  | zero =>
    match as with
    | .cons a as => rfl
  | succ idx ih =>
    match as with
    | .cons a as =>
    unfold remove
    dsimp
    rw [cons_length, cons_length, ih]
    match as with
    | .nil => cases idx <;> contradiction
    | .cons _ _ => rfl

def list.remove_get?_lt (as: list α) (pos idx: nat) (idxLt: idx < as.length) :
  (h: pos < idx) ->
  (as.remove idx idxLt).get? pos = as.get? pos := by
    intro h
    induction idx generalizing pos as with
    | zero => cases pos <;> contradiction
    | succ idx ih =>
      cases as
      contradiction
      unfold list.remove
      dsimp
      cases pos
      rfl
      unfold get?; dsimp
      rw [ih _ _ _ h]

def list.remove_get?_ge (as: list α) (pos idx: nat) (idxLt: idx < as.length) :
  (h: pos ≥ idx) ->
  (as.remove idx idxLt).get? pos = as.get? pos.succ := by
  intro h
  induction idx generalizing pos as with
  | zero =>
    cases as
    contradiction
    rfl
  | succ idx ih =>
    cases as
    contradiction
    rw [list.remove]
    dsimp
    cases pos
    have := nat.le_zero h
    contradiction
    rw [get?]
    dsimp
    rw [ih]
    rfl
    assumption

def list.remove_getElem_lt (as: list α) (pos idx: nat) (idxLt: idx < as.length) :
  (h: pos < idx) ->
  (as.remove idx idxLt)[pos]'(by
      cases as
      cases idx <;> contradiction
      rw [length_remove]
      apply lt_of_lt_of_le h
      apply nat.le_of_lt_succ
      assumption) = as[pos]'(lt_trans h idxLt) := by
    intro h
    apply Option.some.inj
    rw [getElem_eq_get?, getElem_eq_get?, Option.some_get, Option.some_get]
    apply remove_get?_lt
    assumption

def list.remove_getElem_ge (as: list α) (pos idx: nat) (idxLt: idx < as.length) :
  (h: pos ≥ idx) ->
  (g: pos.succ < as.length) ->
  (as.remove idx idxLt)[pos]'(by
    cases as
    contradiction
    rw [length_remove]
    exact g) = as[pos.succ] := by
  intro h g
  apply Option.some.inj
  rw [getElem_eq_get?, getElem_eq_get?, Option.some_get, Option.some_get]
  apply remove_get?_ge
  assumption
