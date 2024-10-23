import Algebra.Fintype.Basic
import Algebra.Fin.Basic

def all_fins : (n: nat) -> list (fin n)
| .zero => .[]
| .succ n => .cons fin.zero ((all_fins n).map fin.succ)

def all_fins_mem : ∀x, x ∈ all_fins n := by
  intro x
  induction n with
  | zero => contradiction
  | succ n ih =>
    unfold all_fins
    cases x
    apply list.mem.head
    apply list.mem.tail
    apply list.mem_map.mpr
    rename_i x
    exists x
    apply And.intro
    apply ih
    rfl

def all_fins_nodup : (all_fins n).nodup := by
  induction n with
  | zero => exact list.pairwise.nil
  | succ n ih =>
    apply list.pairwise.cons
    intro x h g
    subst x
    have ⟨_,_,_⟩ := list.mem_map.mp h
    contradiction
    apply list.nodup_map
    assumption
    apply fin.succ.inj

instance : Fintype (fin n) where
  all := .ofList (all_fins n) all_fins_nodup
  all_spec a := by
    apply (Finset.ofList_mem _ _ _).mpr
    apply all_fins_mem
