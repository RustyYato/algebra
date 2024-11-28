import Algebra.Fintype.Basic
import Algebra.Fin.Basic

namespace fin.fintype

def all_fins : (n: nat) -> List (fin n)
| .zero => []
| .succ n => .cons fin.zero ((all_fins n).map fin.succ)

def all_fins_mem : ∀x, x ∈ all_fins n := by
  intro x
  induction n with
  | zero => contradiction
  | succ n ih =>
    unfold all_fins
    cases x
    apply List.Mem.head
    apply List.Mem.tail
    apply List.mem_map.mpr
    rename_i x
    exists x
    apply And.intro
    apply ih
    rfl

def all_fins_nodup : (all_fins n).Nodup := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    apply List.Pairwise.cons
    intro x h g
    subst x
    have ⟨_,_,_⟩ := List.mem_map.mp h
    contradiction
    apply List.nodup_map
    assumption
    apply fin.succ.inj

def all_fins_length : (all_fins n).length = n.toNat := by
  induction n with
  | zero => rfl
  | succ n ih => rw [all_fins, List.length_cons, List.length_map, ih]; rfl

end fin.fintype

instance fin.FintypeInst : Fintype (fin n) where
  all := fin.fintype.all_fins n
  all_nodups := fin.fintype.all_fins_nodup
  all_spec := fin.fintype.all_fins_mem

def fin.card (f: Fintype (fin n)) : f.card = n.toNat := by
  rw [Fintype.card_eq _ fin.FintypeInst]
  unfold FintypeInst Fintype.card Fintype.all
  dsimp
  rw [fin.fintype.all_fins_length]
