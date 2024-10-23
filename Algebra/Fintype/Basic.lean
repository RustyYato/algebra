import Algebra.Fintype.Finset

class Fintype (α: Type _) where
  all: Finset α
  all_spec: ∀x, x ∈ all

instance : Fintype Bool where
  all := .ofList .[true, false] (by decide)
  all_spec := by decide

instance : Subsingleton (Fintype α) where
  allEq := by
    intro a b
    cases a with | mk all_a all_a_spec =>
    cases b with | mk all_b all_b_spec =>
    congr
    ext a
    apply Iff.intro <;> intro
    apply all_b_spec
    apply all_a_spec

def Fintype.card (f: Fintype α) := f.all.card

def Fintype.card_eq (f g: Fintype α) :
  f.card = g.card := by
  cases f with | mk f fspec =>
  cases g with | mk g gspec =>
  cases f with | mk f fnodup =>
  cases g with | mk g gnodup =>
  unfold card Finset.card
  dsimp
  induction f using Multiset.ind with | mk f =>
  induction g using Multiset.ind with | mk g =>
  rw [Multiset.mk_length, Multiset.mk_length]
  dsimp at *
  replace fspec : ∀x, x ∈ f := by
    intro x
    apply (Multiset.mk_mem _ _).mp
    apply fspec
  replace gspec : ∀x, x ∈ g := by
    intro x
    apply (Multiset.mk_mem _ _).mp
    apply gspec
  replace fnodup := (Multiset.mk_nodup _).mp fnodup
  replace gnodup := (Multiset.mk_nodup _).mp gnodup
  have mem_iff : ∀{x}, x ∈ f ↔ x ∈ g := by
    intro x
    apply Iff.intro
    intro; apply gspec
    intro; apply fspec
  clear gspec fspec
  rw [list.perm.length]
  apply list.perm_iff_forall_min_count.mpr
  intro x n
  cases n
  apply Iff.intro
  intro; apply list.min_count.zero
  intro; apply list.min_count.zero
  rename_i n
  cases n
  apply Iff.intro
  intro m
  apply list.mem_iff_min_count.mp
  apply mem_iff.mp
  apply list.mem_iff_min_count.mpr
  assumption
  intro m
  apply list.mem_iff_min_count.mp
  apply mem_iff.mpr
  apply list.mem_iff_min_count.mpr
  assumption
  rename_i n
  apply Iff.intro
  intro h
  have := list.not_min_count_and_nodup _ h
  contradiction
  intro h
  have := list.not_min_count_and_nodup _ h
  contradiction
