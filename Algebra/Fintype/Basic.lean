import Algebra.List.Perm
import Algebra.Ty.Basic

class Fintype (α: Type _) where
  all: list α
  all_nodups: all.nodup
  all_spec: ∀x, x ∈ all

instance : Fintype Bool where
  all := .[true, false]
  all_nodups := by decide
  all_spec := by decide

def Fintype.perm (a b: Fintype α) : a.all.perm b.all := by
  cases a with | mk as as_nodup as_spec =>
  cases b with | mk bs bs_nodup bs_spec =>
  dsimp
  apply list.perm_iff_forall_min_count.mpr
  intro x n
  cases n
  apply Iff.intro
  intro; apply list.min_count.zero
  intro; apply list.min_count.zero
  rename_i n
  cases n
  apply Iff.intro
  intro
  apply list.mem_iff_min_count.mp
  apply bs_spec
  intro
  apply list.mem_iff_min_count.mp
  apply as_spec
  rename_i n
  apply Iff.intro
  intro h
  have := list.not_min_count_and_nodup _ h
  contradiction
  intro h
  have := list.not_min_count_and_nodup _ h
  contradiction

def Fintype.card (f: Fintype α) := f.all.length

def Fintype.card_eq (f g: Fintype α) :
  f.card = g.card := by
  unfold card
  rw [list.perm.length]
  apply perm

def Fintype.of_equiv [f: Fintype α] (eq: Ty.EmbedIso α β) : Fintype β where
  all := f.all.map eq.fwd
  all_nodups := by
    apply list.nodup_map
    exact f.all_nodups
    exact eq.fwd_inj
  all_spec := by
    intro x
    apply list.mem_map.mpr
    exists eq.rev x
    apply And.intro
    apply f.all_spec
    rw [eq.rev_fwd]

def Fintype.card_of_equiv (f: Fintype α) (g: Fintype β) (eq: Ty.EmbedIso α β) : f.card = g.card := by
  rw [card_eq _ (@of_equiv α β f eq)]
  unfold of_equiv card
  erw [list.length_map]
